#include <iostream>
#include <iomanip>
#include <sstream>
#include <cmath>
#include <ctime>
#include <algorithm>
#include <string>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <stack>
#include <set>
#include <fstream>
using namespace std;

#define maxn 30100
#define BETA 0.6
#define SP0 85
#define MaxIdleIters 1000
#define parent_num 20

struct solution_struct{
	vector<int> solution;
	int connectivity;
	int total_distance;
};

struct scomp{
	vector<int> list;
	int size, key_vertex;
};

int vertex_num, K, visited_vertex_num, run_times;
vector<int> adjlist[maxn];
int visited_vertex[maxn];
int weight[maxn], vertex_cpn_id[maxn];
int int_array[maxn];
bool deleted[maxn], visited[maxn];
scomp component[maxn];
solution_struct parent[parent_num + 10];
vector<int> solution_operating, S0, S_best, local_best_solution;
stack<int> unused_cpn_id;
set< pair<int, int> > used_cpn_id;
int f_best, f_avg, succ;
double t_avg, init_cost_time, func_time;
clock_t start_time;
long long iter;
double time_out;

int rank_cnty[parent_num + 10];
int rank_dis[parent_num + 10];
int indexs[parent_num + 10];
stack<int> to_visit;
ofstream out;
vector<int> min_cnty;
int dis;
int cnty_operating;
int diss[parent_num];
int local_best_cnty;
double cost_time;
bool in_parent[maxn];

inline double time_cost() {
	return (double)(clock() - start_time) / CLOCKS_PER_SEC;
}

inline bool timeout() {
	return time_cost() > time_out;
}

void read_graph(string file_name) {	
	ifstream in;
	in.open(file_name);
	string s;
	getline(in, s);
	istringstream iss(s);
	iss >> vertex_num;
	int num;
	char c;
	for (int i = 0; i<vertex_num; ++i) {
		adjlist[i].clear();
		getline(in, s);
		istringstream iss(s);
		iss >> num >> c;
		while (iss >> num) adjlist[i].push_back(num);
	}
}

void depth_first_search_split(int start, bool change_visited, bool add_weight) {
	visited_vertex_num = 0;
    while(!to_visit.empty()) to_visit.pop();
    to_visit.push(start);
    visited[start] = true;
    int v;
    while(!to_visit.empty()) {
        v = to_visit.top();
        to_visit.pop();
        visited_vertex[visited_vertex_num++] = v;
        for(auto &n : adjlist[v])
            if(!deleted[n] && !visited[n]) to_visit.push(n), visited[n] = true;
    }

	int cpn_id = unused_cpn_id.top();
	unused_cpn_id.pop();
	used_cpn_id.insert(make_pair(visited_vertex_num, cpn_id));
	scomp &cpn = component[cpn_id];
	cpn.list.resize(visited_vertex_num);
	cpn.key_vertex = visited_vertex[0];
	cpn.size = visited_vertex_num;
	for (int j = 0; j < visited_vertex_num; ++j) {//优化为不需要使用这个循环
		vertex_cpn_id[visited_vertex[j]] = cpn_id;
		cpn.list[j] = visited_vertex[j];
		if(add_weight) weight[visited_vertex[j]]++;
		if (weight[visited_vertex[j]] > weight[cpn.key_vertex] ||
		 (weight[visited_vertex[j]] == weight[cpn.key_vertex] && adjlist[visited_vertex[j]].size() > adjlist[cpn.key_vertex].size()))
			cpn.key_vertex = visited_vertex[j];
		visited[visited_vertex[j]] = change_visited;
	}
}

int seperate_graph() {
	while (!unused_cpn_id.empty()) unused_cpn_id.pop();
	for (int i = 0; i <= vertex_num; ++i) unused_cpn_id.push(i);  //add one more
	used_cpn_id.clear();
	fill(visited, visited + vertex_num, false);
	cnty_operating = 0;
	for (int i = 0; i < vertex_num; ++i)
		if (!deleted[i] && !visited[i]) {
			depth_first_search_split(i, true, false);
			//for (int j = 0; j < visited_vertex_num; ++j)
			//	visited[visited_vertex[j]] = true;//优化为不需要使用这个循环
			cnty_operating += (visited_vertex_num - 1) * visited_vertex_num / 2;
		}
	fill(visited, visited + vertex_num, false);
	return cnty_operating;
}

int select_large_component() {
	int L = used_cpn_id.begin() -> first, R = used_cpn_id.rbegin() -> first;//使用set<pair>记录使用过的id，避免两次遍历
	int bound = (L + R) >> 1;
	int cnt = 0;
	for (auto it = used_cpn_id.rbegin(); it != used_cpn_id.rend() && it -> first >= bound; ++it)//从后往前/从大到小遍历，遇到不够大的终止
		int_array[cnt++] = it -> second;
	return int_array[rand() % cnt];
}

void add_to_solution(int add_vertex) {
	int cpn_id = vertex_cpn_id[add_vertex];
	int cpn_size = component[cpn_id].size;
	deleted[add_vertex] = true;
	for (auto &n : adjlist[add_vertex])
		if (!deleted[n] && vertex_cpn_id[n] == cpn_id) {//第二个判断条件表示是否已经访问过
			depth_first_search_split(n, false, true);
			cnty_operating += (visited_vertex_num - 1) * visited_vertex_num / 2;
			//cpn_size += visited_vertex_num;
			//for (int i = 0; i < visited_vertex_num; ++i)
			//	weight[visited_vertex[i]]++;//可以放在深度遍历里面完成
		}
	cnty_operating -= cpn_size * (cpn_size - 1) / 2;
	unused_cpn_id.push(cpn_id);
	used_cpn_id.erase(make_pair(component[cpn_id].size, cpn_id));
}

void remove_from_solution() {
	int increase = maxn * maxn, back_vertex = -1;
	int idx = -1;
	for (auto &v : solution_operating) {//修改为传统迭代
		++idx;
		int delta = 0, cnt = 0, cpn_id;
		int sub_vertex_num = 0;
		for (auto &n : adjlist[v])
			if (!deleted[n])
				if (!visited[cpn_id = vertex_cpn_id[n]]) {//写在同一个if
					visited[cpn_id] = true;
					delta += sub_vertex_num * component[cpn_id].size;
					sub_vertex_num += component[cpn_id].size;
				}
		delta += sub_vertex_num;
		for (auto &n : adjlist[v])
			if (!deleted[n]) visited[vertex_cpn_id[n]] = false;
		if (delta <= increase) increase = delta, back_vertex = idx;
	}
	swap(solution_operating[back_vertex], solution_operating.back());//放到最后再删除，效率较高
	back_vertex = solution_operating.back();
	solution_operating.pop_back();
	deleted[back_vertex] = false;
	weight[back_vertex] = 0;
    cnty_operating += increase;
	int cpn_id;
	for (auto &adj : adjlist[back_vertex])
		if (!deleted[adj])
			if (!visited[cpn_id = vertex_cpn_id[adj]]) {
				visited[cpn_id] = true;
				unused_cpn_id.push(cpn_id);
				used_cpn_id.erase(make_pair(component[cpn_id].size, cpn_id));
			}
	for (auto &adj : adjlist[back_vertex])
		if (!deleted[adj]) visited[vertex_cpn_id[adj]] = false;
	depth_first_search_split(back_vertex, false, false);
}

void component_based_neiborhood_search() {
	clock_t func_start_time = clock();
	fill(weight, weight + vertex_num, 0);
	local_best_solution = solution_operating;
	int local_best_cnty = seperate_graph();//放在initialize和crossover
	int idle_iter = 0;
	while (idle_iter < MaxIdleIters) {
		int add_vertex = component[select_large_component()].key_vertex;
		solution_operating.push_back(add_vertex);
		add_to_solution(add_vertex);
        remove_from_solution();
        ++iter;
		if (cnty_operating < local_best_cnty) {
			local_best_solution = solution_operating;
			local_best_cnty = cnty_operating;
			idle_iter = 0;
		}
		else idle_iter++;
	}
	for (auto &v : solution_operating) deleted[v] = false;
	solution_operating = local_best_solution;
    cnty_operating = local_best_cnty;
	for (auto &v : solution_operating) deleted[v] = true;
	func_time += (double)(clock() - func_start_time) / CLOCKS_PER_SEC;
}

double get_distance(vector<int> &S1, vector<int> &S2) {
	int Sim = 0;
	for (auto &num : S1) visited[num] = true;
	for (auto &num : S2) Sim += visited[num];
	for (auto &num : S1) visited[num] = false;
	return K - Sim;
}

int deth_first_search(int start, vector<bool>& visited) {
	stack<int> s;
	s.push(start);
	visited[start] = true;
	int size = 0;
	while(!s.empty()) {
		int vertex = s.top();
		s.pop();
		size++;
		for(int i = 0; i < adjlist[vertex].size(); ++i) {
			int neibor = adjlist[vertex][i];
			if(!deleted[neibor] && !visited[neibor]) {
				s.push(neibor);
				visited[neibor] = true;
			}
		}
	}
	return size;
}

int get_connectivity() {//只需要得到连通度，不需要将原图分割、记录子图信息时，使用该函数
	int connectivity = 0;
	vector<bool> visited(vertex_num, false);
	for(int i = 0; i < vertex_num; ++i) {
		if(!deleted[i] && !visited[i]) {
			int size = deth_first_search(i, visited);
			connectivity += size * (size - 1) / 2;
		}
	}
	return connectivity;
}

void population_initialization() {
	fill(deleted, deleted + vertex_num, false);
	for (int i = 0; i < parent_num; ++i) {
		solution_operating.resize(K);
		for (int j = 0; j < K; ++j) {
			solution_operating[j] = rand() % vertex_num;
			while (deleted[solution_operating[j]]) solution_operating[j] = rand() % vertex_num;
			deleted[solution_operating[j]] = true;
		}
		component_based_neiborhood_search();
		while (true) {
			bool differ = true;
            for(int j = 0; j < i; ++j) {
                bool same = true;
                for(auto &v : parent[j].solution) 
                    if(!deleted[v]) {
                        same = false;
                        break;
                    }
                if(same) {
                    differ = false;
                    break;
                }
            }
			if (differ) break;
			int idx = rand() % K;
			deleted[solution_operating[idx]] = false;
			int v = rand() % vertex_num;
			while (deleted[idx]) v = rand() % vertex_num;
			deleted[v] = true;
            solution_operating[idx] = v;
		}
		parent[i].solution = solution_operating;
		int cnty;
		parent[i].connectivity = (cnty = get_connectivity());
		if(cnty < local_best_cnty) {
			local_best_cnty = cnty;
			S0 = solution_operating;
			cost_time=time_cost();
		}
		cout << i << " pool initialization cnty : " << cnty << endl;
        parent[i].total_distance = 0;
        for(int j = 0; j < i; ++j) {
            dis = 0;
            for(auto &v : parent[j].solution) dis += deleted[v];
            dis = K - dis;
            parent[i].total_distance += dis;
            parent[j].total_distance += dis;
        }
		fill(deleted, deleted + vertex_num, false);
	}
}

void double_backbone_based_crossover(vector<int> &S1, vector<int> &S2) {
	int cnt = 0;
	for (auto &v : solution_operating) deleted[v] = false;
	solution_operating.clear();
	for (auto &v : S1) in_parent[v] = true;
	for (auto &v : S2)
		if (in_parent[v]) {
			solution_operating.push_back(v);
            deleted[v] = true;
			in_parent[v] = false;
		}
		else int_array[cnt++] = v;
	for (auto &v : S1)
		if (in_parent[v]) int_array[cnt++] = v;//S1独有的点visited没有置为false
	for (int i = 0; i < cnt; ++i)
		if (rand() % 100 <= SP0) {
            solution_operating.push_back(int_array[i]);
            deleted[int_array[i]] = true;
        }
	if (solution_operating.size() != K) seperate_graph();
	if (solution_operating.size() < K) {
		for (auto &v : S1) in_parent[v] = true;
		for (auto &v : S2) in_parent[v] = true;//XB里面有些点并没有加入solution_operating，这时visited = true
		while (solution_operating.size() < K) {//后面add_to_solution会调用dfs_split，里面会使用visited数组，这会导致误以为这些点被删掉
			scomp &cur = component[select_large_component()];
			int idx = rand() % cur.size;
			if (!in_parent[cur.list[idx]]) {
				solution_operating.push_back(cur.list[idx]);
				add_to_solution(solution_operating.back());
			}
		}
        for (auto &v : S1) in_parent[v] = false;
        for (auto &v : S2) in_parent[v] = false;
	}
	while (solution_operating.size() > K) remove_from_solution();
}

bool cnty_compare(int i, int j) {return parent[i].connectivity < parent[j].connectivity;}
bool distance_compare(int i, int j) {return parent[i].total_distance > parent[j].total_distance;}

void rank_based_pool_updating() {
	parent[parent_num] = solution_struct{solution_operating, cnty_operating, 0};
	int avg = 0;
	for (int i = 0; i < parent_num; ++i) {
		dis = 0;
		for(auto &v : parent[i].solution) dis += deleted[v];
		dis = K - dis;
		diss[i] = dis;
		parent[parent_num].total_distance += dis;
		parent[i].total_distance += dis;
		cout << parent[i].total_distance << " ";
		avg += parent[i].total_distance;
	}
	cout << parent[parent_num].total_distance << " " << avg / (parent_num + 1) << endl;
    stable_sort(indexs, indexs + parent_num + 1, cnty_compare);
    for(int i = 0; i < parent_num + 1; ++i) rank_cnty[indexs[i]] = i;
    stable_sort(indexs, indexs + parent_num + 1, distance_compare);
    for(int i = 0; i < parent_num + 1; ++i) rank_dis[indexs[i]] = i;
    int idx = -1, max_score = -1, score;
    for(int i = 0; i < parent_num + 1; ++i) {
        score = BETA * rank_cnty[i] + (1 - BETA) * rank_dis[i];
        if(score > max_score) idx = i, max_score = score;
    }
	if (idx != parent_num) {
		swap(parent[idx], parent[parent_num]);
		for(auto &v : parent[parent_num].solution) visited[v] = true;
		for(int i = 0; i < parent_num; ++i) {
			dis = 0;
			for(auto &v : parent[i].solution) dis += visited[v];
			dis = K - dis;
			parent[i].total_distance -= dis;
		}
		for(auto &v : parent[parent_num].solution) visited[v] = false;
	}
	else for(int i = 0; i < parent_num; ++i) parent[i].total_distance -= diss[i];
}

void critical_node_problem() {
	srand(time(0));
	local_best_cnty = maxn * maxn;
	S0.clear();
	start_time = clock();
	population_initialization();
	init_cost_time += time_cost();
	cost_time = 0;
	fill(in_parent, in_parent + vertex_num, false);
	while (!timeout()) {
		int Si = rand() % parent_num, Sj = rand() % parent_num;
		while (Si == Sj) Si = rand() % parent_num, Sj = rand() % parent_num;//不用参数，直接用全局变量
		double_backbone_based_crossover(parent[Si].solution, parent[Sj].solution);
		component_based_neiborhood_search();
		cout << "best connectivity once : " << local_best_cnty << " / " << cnty_operating << endl;
		cout << "best ever : " << f_best << endl;
		if (cnty_operating < local_best_cnty) {
			S0 = solution_operating;
			local_best_cnty = cnty_operating;
			cost_time = time_cost();
		}
		rank_based_pool_updating();
	}
	if (local_best_cnty < f_best) {
        S_best = S0;
        f_best = local_best_cnty;
        t_avg = cost_time;
        succ = 1;
    }
    else if (local_best_cnty == f_best) t_avg += cost_time, succ++;
    min_cnty.push_back(local_best_cnty);
    f_avg += local_best_cnty;
    out << local_best_cnty << endl;
}

void print(vector<int> &solution_operating) {
	sort(solution_operating.begin(), solution_operating.end());
	for (auto &vertex : solution_operating) cout << vertex << " ";
	fill(deleted, deleted + vertex_num, false);
	for (auto &num : solution_operating) deleted[num] = true;
	cout << "\n" << seperate_graph() << endl;
}

void one_benchmark(string file_name, int k) {
    min_cnty.clear();
	read_graph(file_name);
	K = k;
    f_best=vertex_num*vertex_num, f_avg=0, succ=0;
    t_avg=0; init_cost_time=0; func_time=0; iter=0;
    for (int i=0; i<run_times; ++i) critical_node_problem();
    cout << fixed;
	for(auto &cnty : min_cnty) cout << cnty << " ";
	cout << endl;
    cout << "f_best " << f_best << "\n";
    cout << "f_avg " << setprecision(1) << double(f_avg)/run_times << "\n";
    cout << "succ " << succ << "\n"; 
    cout << "t_avg " << setprecision(1) << t_avg/succ << "\n";
    cout << "init_cost_time " << setprecision(1) << init_cost_time/run_times << "\n";
    cout << "func_time " << setprecision(1) << func_time/run_times << "\n";
    cout << "iter " << iter << "\n";

    out << fixed;
    for(auto &cnty : min_cnty) out << cnty << " ";
    out << endl;
    out << "f_best " << f_best << "\n";
    out << "f_avg " << setprecision(1) << double(f_avg)/run_times << "\n";
    out << "succ " << succ << "\n"; 
    out << "t_avg " << setprecision(1) << t_avg/succ << "\n";
    out << "init_cost_time " << setprecision(1) << init_cost_time/run_times << "\n";
    out << "func_time " << setprecision(1) << func_time/run_times << "\n";
    out << "iter " << iter << "\n";
}

int main() {
    for(int i = 0; i < parent_num + 1; ++i) indexs[i] = i;
    vector<string> file_names = {"BenchMarks/cnd/WattsStrogatz_n500.txt", "BenchMarks/cnd/ErdosRenyi_n2500.txt", 
	"BenchMarks/RealInstances/powergrid.txt", "BenchMarks/RealInstances/Hamilton5000.txt"};
	vector<int> Ks = {125, 200, 494, 500};
	string result_file_name = "results_MA.txt";
    time_out = 3600;
    run_times = 10;
	out.open(result_file_name);
	for(int i = 0; i < 4; ++i) one_benchmark(file_names[i], Ks[i]);
	system("pause");
	return 0;
}
