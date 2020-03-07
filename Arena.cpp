#include <iostream>
#include <iomanip>
#include <vector>
#include <array>
#include <list>
#include <cmath>
#include <fstream>
#include <random>
#include <chrono>
#include <sstream>
#include <unistd.h>
#include <sys/wait.h>
#include <ext/stdio_filebuf.h>
#include <sys/ioctl.h>
#include <poll.h>
#include <omp.h>
#include <algorithm>
using namespace std;
using namespace std::chrono;

constexpr bool tests{true};
constexpr bool Debug_AI{false},Timeout{false};
constexpr double FirstTurnTime{1*(Timeout?1:10)},TimeLimit{0.050*(Timeout?1:10)};
constexpr int PIPE_READ{0},PIPE_WRITE{1};
constexpr int N{2};
constexpr int Houses_Per_Player{6};
constexpr int Turn_Limit{200},Seed_Win_Threshold{25};

bool stop{false};//Global flag to stop all arena threads when SIGTERM is received
default_random_engine generator(system_clock::now().time_since_epoch().count());

inline bool Capture_Seed_Count(const int seed_count){
    return seed_count==2 || seed_count==3;
}

struct state{
    array<int,2*Houses_Per_Player> seeds;//[0,5] are current player seeds, [6,11] are enemy player seeds
    array<int,2> score{0,0};//current player's score then enemy player's score
    bool white{true};
    int turn{0};
    vector<int> valid_moves;
    void recompute_valid_moves(){//Valid moves for the current player
        valid_moves.clear();
        const bool enemy_has_seeds{any_of(next(seeds.begin(),Houses_Per_Player),seeds.end(),[](const int seed_count){return seed_count>0;})};
        for(int mv{0};mv<Houses_Per_Player;++mv){
            if(seeds[mv]>0 && (enemy_has_seeds || mv+seeds[mv]>=Houses_Per_Player)){//mv+seeds[mv]>=Houses_Per_Player indicates sowing in the opponent's houses
                valid_moves.push_back(mv);
            }
        }
    }
    inline void reverse_state(){
        rotate(seeds.begin(),next(seeds.begin(),Houses_Per_Player),seeds.end());
        swap(score[0],score[1]);
        white=!white;
        recompute_valid_moves();
    }
    void simulate(const int mv){//Assumes validity of the move
        int current_idx{mv};
        while(seeds[mv]>0){
            current_idx=current_idx+1<seeds.size()?current_idx+1:0;//current_idx=(current_idx+1)%seeds.size()
            if(current_idx==mv){//Cannot sow into the house played from
                ++current_idx;//If we had the state from the point of view of the opponent we would have to check if current_idx equals seeds.size() (12)
            }
            ++seeds[current_idx];
            --seeds[mv];
        }
        array<int,6> Enemy_Seeds_Before_Capture;
        copy(next(seeds.begin(),Houses_Per_Player),seeds.end(),Enemy_Seeds_Before_Capture.begin());
        const int score_before_capture{score[0]};
        while(current_idx>=Houses_Per_Player && Capture_Seed_Count(seeds[current_idx])){//Capture mechanism
            score[0]+=seeds[current_idx];
            seeds[current_idx]=0;
            --current_idx;
        }
        if(none_of(next(seeds.begin(),Houses_Per_Player),seeds.end(),[](const int seed_count){return seed_count>0;})){//Enemy has no more seeds, captures must be forfeit
            copy(Enemy_Seeds_Before_Capture.begin(),Enemy_Seeds_Before_Capture.end(),next(seeds.begin(),Houses_Per_Player));//restore state after sowing but before capture
            score[0]=score_before_capture;
        }
        reverse_state();
        if(valid_moves.empty()){
            score[0]+=accumulate(seeds.begin(),next(seeds.begin(),Houses_Per_Player),0);
            fill(seeds.begin(),next(seeds.begin(),Houses_Per_Player),0);
        }
        ++turn;
    }
    inline bool game_over()const{
        return valid_moves.empty() || turn>Turn_Limit || any_of(score.begin(),score.end(),[](const int s){return s>=Seed_Win_Threshold;});
    }
    inline int winner()const{//1 win, -1 loss 0 draw
        return score[0]>score[1]?1:(score[1]>score[0]?-1:0);
    }
    inline int total_seeds()const{
        return accumulate(seeds.begin(),seeds.end(),0);
    }
};

struct AI{
    int id,pid,outPipe,errPipe,inPipe,turnOfDeath;
    string name;
    inline void stop(const int turn=-1){
        if(alive()){
            kill(pid,SIGTERM);
            int status;
            waitpid(pid,&status,0);//It is necessary to read the exit code for the process to stop
            if(!WIFEXITED(status)){//If not exited normally try to "kill -9" the process
                kill(pid,SIGKILL);
            }
            turnOfDeath=turn;
        }
    }
    inline bool alive()const{
        return kill(pid,0)!=-1;//Check if process is still running
    }
    inline void Feed_Inputs(const string &inputs){
        if(write(inPipe,&inputs[0],inputs.size())!=inputs.size()){
            throw(5);
        }
    }
    inline ~AI(){
        close(errPipe);
        close(outPipe);
        close(inPipe);
        stop();
    }
};

void StartProcess(AI &Bot){
    int StdinPipe[2];
    int StdoutPipe[2];
    int StderrPipe[2];
    if(pipe(StdinPipe)<0){
        perror("allocating pipe for child input redirect");
    }
    if(pipe(StdoutPipe)<0){
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        perror("allocating pipe for child output redirect");
    }
    if(pipe(StderrPipe)<0){
        close(StderrPipe[PIPE_READ]);
        close(StderrPipe[PIPE_WRITE]);
        perror("allocating pipe for child stderr redirect failed");
    }
    int nchild{fork()};
    if(nchild==0){//Child process
        if(dup2(StdinPipe[PIPE_READ],STDIN_FILENO)==-1){// redirect stdin
            perror("redirecting stdin");
            return;
        }
        if(dup2(StdoutPipe[PIPE_WRITE],STDOUT_FILENO)==-1){// redirect stdout
            perror("redirecting stdout");
            return;
        }
        if(dup2(StderrPipe[PIPE_WRITE],STDERR_FILENO)==-1){// redirect stderr
            perror("redirecting stderr");
            return;
        }
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        close(StdoutPipe[PIPE_READ]);
        close(StdoutPipe[PIPE_WRITE]);
        close(StderrPipe[PIPE_READ]);
        close(StderrPipe[PIPE_WRITE]);
        execl(Bot.name.c_str(),Bot.name.c_str(),(char*)NULL);//(char*)Null is really important
        //If you get past the previous line its an error
        perror("exec of the child process");
    }
    else if(nchild>0){//Parent process
        close(StdinPipe[PIPE_READ]);//Parent does not read from stdin of child
        close(StdoutPipe[PIPE_WRITE]);//Parent does not write to stdout of child
        close(StderrPipe[PIPE_WRITE]);//Parent does not write to stderr of child
        Bot.inPipe=StdinPipe[PIPE_WRITE];
        Bot.outPipe=StdoutPipe[PIPE_READ];
        Bot.errPipe=StderrPipe[PIPE_READ];
        Bot.pid=nchild;
    }
    else{//failed to create child
        close(StdinPipe[PIPE_READ]);
        close(StdinPipe[PIPE_WRITE]);
        close(StdoutPipe[PIPE_READ]);
        close(StdoutPipe[PIPE_WRITE]);
        perror("Failed to create child process");
    }
}

inline string EmptyPipe(const int fd){
    int nbytes;
    if(ioctl(fd,FIONREAD,&nbytes)<0){
        throw(4);
    }
    string out;
    out.resize(nbytes);
    if(read(fd,&out[0],nbytes)<0){
        throw(4);
    }
    return out;
}

bool IsValidMove(const state &S,const AI &Bot,const string &Move){
	stringstream ss(Move);
	int house_index;
	if(!(ss >> house_index)){
		return false;
	}
	return true;
}

string GetMove(const state &S,AI &Bot,const int turn){
    pollfd outpoll{Bot.outPipe,POLLIN};
    time_point<system_clock> Start_Time{system_clock::now()};
    string out;
    while(static_cast<duration<double>>(system_clock::now()-Start_Time).count()<(turn==1?FirstTurnTime:TimeLimit) && !IsValidMove(S,Bot,out)){
        double TimeLeft{(turn==1?FirstTurnTime:TimeLimit)-static_cast<duration<double>>(system_clock::now()-Start_Time).count()};
        if(poll(&outpoll,1,TimeLeft)){
            out+=EmptyPipe(Bot.outPipe);
        }
    }
    return out;
}

int StringToAction(const string &mv_str){
	stringstream ss(mv_str);
	int house_index;
	ss >> house_index;
	return house_index;
}

inline bool Has_Won(const array<AI,N> &Bot,const int idx)noexcept{
    if(!Bot[idx].alive()){
        return false;
    }
    for(int i=0;i<N;++i){
        if(i!=idx && Bot[i].alive()){
            return false;
        }
    }
    return true;
}

inline bool All_Dead(const array<AI,N> &Bot)noexcept{
    for(const AI &b:Bot){
        if(b.alive()){
            return false;
        }
    }
    return true;
}

int Play_Game(const array<string,N> &Bot_Names,state &S){
	array<AI,N> Bot;
	int turn{0},id{0};
	for(int i=0;i<N;++i){
		Bot[i].id=i;
		Bot[i].name=Bot_Names[i];
		StartProcess(Bot[i]);
	}
	while(++turn>0){
        //cerr << "Turn " << turn << endl;
		int house_played;
		if(Bot[id].alive()){
			//Feed turn inputs
			stringstream ss;
			for(const int seed_count:S.seeds){
				ss << seed_count << " ";
			}
			try{
				Bot[id].Feed_Inputs(ss.str().c_str());
				string out{GetMove(S,Bot[id],turn)};
				house_played=StringToAction(out);
				string err_str{EmptyPipe(Bot[id].errPipe)};
                if(Debug_AI){
                    ofstream err_out("log.txt",ios::app);
                    err_out << err_str << endl;
                }
            }
            catch(int ex){
            	if(ex==1){//Timeout
                    cerr << "Loss by Timeout of AI " << Bot[id].id << " name: " << Bot[id].name << endl;
                }
                else if(ex==3){
                    cerr << "Invalid move from AI " << Bot[id].id << " name: " << Bot[id].name << endl;
                }
                else if(ex==4){
                    cerr << "Error emptying pipe of AI " << Bot[id].name << endl;
                }
                else if(ex==5){
                    cerr << "AI " << Bot[id].name << " died before being able to give it inputs" << endl;
                }
                Bot[id].stop(turn);
            }
		}
		if(All_Dead(Bot)){
            return -1;//Draw
        }
        else{
        	for(int i=0;i<N;++i){
        		if(Has_Won(Bot,i)){
        			return i;
        		}
        	}
        }
		S.simulate(house_played);
        if(S.game_over()){
        	return S.winner()==1?(S.white?0:1):(S.winner()==-1?(S.white?1:0):(-1));
        }
        id=(id+1)%N;
	}
	throw(0);
}

state Random_Initial_State(){
	state S;
	fill(S.seeds.begin(),S.seeds.end(),4);
	fill(S.score.begin(),S.score.end(),0);
	S.turn=1;
	S.recompute_valid_moves();
	return S;
}

array<float,N> Play_Round(const array<string,N> &Bot_Names){
	array<float,N> Points;
	fill(Points.begin(),Points.end(),0);
	for(int i=0;i<N;++i){
		state S{Random_Initial_State()};
		array<string,N> Bot_Names2{Bot_Names};
		rotate(Bot_Names2.begin(),next(Bot_Names2.begin(),i),Bot_Names2.end());
		const int winner{Play_Game(Bot_Names2,S)};
		if(winner==-1){
			for(float &p:Points){
				p+=0.5;
			}
		}
		else{
			Points[(winner+i)%N]+=1;
            //Points[winner]+=1;
		}
	}
	return Points;
}

void StopArena(const int signum){
    stop=true;
}

int main(int argc,char **argv){
    if(argc<3){
        cerr << "Program takes 2 inputs, the names of the AIs fighting each other" << endl;
        return 0;
    }
    int N_Threads{1};
    if(argc>=4){//Optional N_Threads parameter
        N_Threads=min(2*omp_get_num_procs(),max(1,atoi(argv[3])));
        cerr << "Running " << N_Threads << " arena threads" << endl;
    }
    array<string,N> Bot_Names;
    for(int i=0;i<2;++i){
        Bot_Names[i]=argv[i+1];
    }
    cout << "Testing AI " << Bot_Names[0];
    for(int i=1;i<N;++i){
        cerr << " vs " << Bot_Names[i];
    }
    cerr << endl;
    for(int i=0;i<N;++i){//Check that AI binaries are present
        ifstream Test{Bot_Names[i].c_str()};
        if(!Test){
            cerr << Bot_Names[i] << " couldn't be found" << endl;
            return 0;
        }
        Test.close();
    }
    signal(SIGTERM,StopArena);//Register SIGTERM signal handler so the arena can cleanup when you kill it
    signal(SIGPIPE,SIG_IGN);//Ignore SIGPIPE to avoid the arena crashing when an AI crashes
    int games{0},draws{0};
    array<double,2> points{0,0};
    #pragma omp parallel num_threads(N_Threads) shared(games,points,Bot_Names)
    while(!stop){
        array<float,N> round_points{Play_Round(Bot_Names)};
        for(int i=0;i<N;++i){
        	#pragma omp atomic
        	points[i]+=round_points[i];
        }
        #pragma omp atomic
        games+=2;
        double p{static_cast<double>(points[0])/games};
        double sigma{sqrt(p*(1-p)/games)};
        double better{0.5+0.5*erf((p-0.5)/(sqrt(2)*sigma))};
        #pragma omp critical
        cout << "Wins:" << setprecision(4) << 100*p << "+-" << 100*sigma << "% Games:" << games << " Draws:" << draws << " " << better*100 << "% chance that " << Bot_Names[0] << " is better" << endl;
    }
}