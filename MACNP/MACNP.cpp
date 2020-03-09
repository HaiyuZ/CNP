#include <iostream>
#include <iomanip>
#include <sstream>
#include <fstream>
#include <cmath>
#include <ctime>
#include <algorithm>
#include <string>
#include <cstring>
#include <cstdlib>
#include <vector>
#include <stack>
#include <set>
#include <map>
#include <queue>
using namespace std;

int K;
double time_out = 3600;//每次运行函数允许使用的最大时间
int run_times = 10;//运行次数

#define SP0 85
#define maxn 30100
#define BETA 0.6
#define MaxIdleIters 1000//是否太大了
#define parent_num 20

ofstream out;

vector<int> min_cnty;
vector<vector<int>> adjlist;//整个图的邻接矩阵
int vertex_num;//图中顶点总数

int cnty_operating;//当前操作的解的连通度
vector<int> solution_operating;//当前操作的解
vector<int> best_solution_once;//单次最优解
int min_connectivity_once;//单次最优解的连通度
vector<int> best_solution;//所有次数里的最佳解
int f_best;//最优解的连通度
int f_avg;//所有单次最优解的平均连通度
int succeed_times;//达到最优解的次数
int exch;//交换次数

long long weight[maxn];//每个顶点的权重，每次local search时都更新，还是全程只要一次初始化
int vertex_component_id[maxn];//每个顶点所属的子图的id
bool deleted[maxn];//删除的点/在当前操作的解中的顶点

vector<int> components[maxn];//连通子图
vector<int> solutions[parent_num + 10];//解的集合

stack<int> unused_component_id;//未使用的子图id
set<int> used_component_id;//已使用的子图id

double t_avg;//找到最优解所用的平均时间
double init_cost_time;//初始化使用的时间
double func_time;//调用函数解决所用的时间
long long iter;//迭代次数，即交换次数
clock_t start_time;//用于计算时间

vector<int> connectivities(parent_num + 1, 0);//每个解的连通度
int* key_vertexs = new int[maxn];//每个子图中权重最大的顶点
vector<int> tmp_dis(parent_num + 1, 0);
vector<int> total_distances(parent_num + 1, 0);//解与其他解的总距离
vector<int> rank_connectivity(parent_num + 1);//解的连通度排名
vector<int> rank_distance(parent_num + 1);//解的总距离排名

vector<int> visited_vertex;//分割出新的component时记录其中的顶点

inline double time_cost() {
	return (double)(clock() - start_time) / CLOCKS_PER_SEC;
}

inline bool timeout() {
	return time_cost() > time_out;
}

void read_graph(string filename) {
	ifstream in;
	in.open(filename);
	string line;
	getline(in, line);
	istringstream iss(line);
	iss >> vertex_num;
	adjlist.clear();
	adjlist.resize(vertex_num);
	int tmp;
	char c;
	for (int i = 0; i < vertex_num; ++i) {
		getline(in, line);
		istringstream iss(line);
		iss >> tmp >> c;
		while(iss >> tmp) adjlist[i].push_back(tmp);
	}
}

int deth_first_search_split(int start, vector<bool>& visited, bool add_weight) {//component信息记录
	int cpn_id = unused_component_id.top();//新component用的id
	visited_vertex.clear();//新component包含的顶点
	stack<int> to_visit;
	to_visit.push(start);
	visited[start] = true;
	int key_vertex = start;//权重最大的顶点
	int vertex;
	while(!to_visit.empty()) {//深度优先遍历，注意每个点在加入stack时就要把visited置为true
		vertex = to_visit.top();
		to_visit.pop();
		visited_vertex.push_back(vertex);
		vertex_component_id[vertex] = cpn_id;//每个顶点所属的component的id
		if(add_weight) weight[vertex]++;//如果是添加顶点到solution里，则剩余的点的权重要++
		if (weight[vertex] > weight[key_vertex]//权重较大或权重相等但是度比较大
			|| (weight[vertex] == weight[key_vertex] && adjlist[vertex].size() > adjlist[key_vertex].size()))
			key_vertex = vertex;
		for(auto &neibor:adjlist[vertex]) 
			if(!deleted[neibor] && !visited[neibor]){
				visited[neibor] = true;
				to_visit.push(neibor);
			}
	}
	components[cpn_id] = visited_vertex;
	unused_component_id.pop();
	used_component_id.insert(cpn_id);
	key_vertexs[cpn_id] = key_vertex;
	return visited_vertex.size();
}

void seperate_graph() {//只要连通度而不用继续提高的话，可以调用get_cnty
	while (!unused_component_id.empty()) unused_component_id.pop();//初始化，后面只要将使用的重新push就好
	for (int i = 0; i < vertex_num; ++i) unused_component_id.push(i);
	used_component_id.clear();
	vector<bool> visited(vertex_num, false);
	cnty_operating = 0;
	for (int i=0; i<vertex_num; ++i)
		if (!deleted[i] && !visited[i]) {
			int size = deth_first_search_split(i, visited, false);
			cnty_operating += (size - 1) * size / 2;
		}
}

int select_large_component() {//每次都要遍历used_cpn_id来找到最大最小cpn_size，因为每次加点进solution，可能分割了最大的cpn，
	int max_component_size = 0;//如果想要不用每次遍历used_cpn_id来找到最大，最小的size，要用set，而且要更改set的排列函数（比较大小的函数）
	int min_component_size = vertex_num;//实测使用了set但是实际上并没有维持有序的大小，是因为cpn_size修改时没有相对应更新该set？另起数组记录cpn_size
	for (auto it = used_component_id.begin(); it != used_component_id.end(); ++it) {//可以每次都遍历，因为只需要O(n)的复杂度
		int cpn_size = components[*it].size();
		if(cpn_size > max_component_size) max_component_size = cpn_size;
		if(cpn_size < min_component_size) min_component_size = cpn_size;
	}
	int mean_cpn_size = (max_component_size + min_component_size) / 2;
	vector<int> large_component_id;
	for(auto &id:used_component_id)
		if (components[id].size() >= mean_cpn_size)
			large_component_id.push_back(id);
	return large_component_id[rand() % large_component_id.size()];
}

void add_to_solution(int add_vertex) {//add vertex to solution_operating
	deleted[add_vertex] = true;
	int cpn_size = 1;
	int sub_cpn_size;
	vector<bool> visited(vertex_num, false);
	for (auto &num:adjlist[add_vertex])
		if (!deleted[num] && !visited[num]) {
			sub_cpn_size = deth_first_search_split(num, visited, true);//重新分割原来的component
			cnty_operating += sub_cpn_size * (sub_cpn_size - 1) / 2;
			cpn_size += sub_cpn_size;
		}
	cnty_operating -= (cpn_size - 1) * cpn_size / 2;
	int cpn_id = vertex_component_id[add_vertex];
	components[cpn_id].clear();
	unused_component_id.push(cpn_id);
	used_component_id.erase(cpn_id);
}

int remove_from_solution() {//remove the optimal node from solution 
	int min_increase = vertex_num * vertex_num;
	int remove_vertex = -1;
	int idx = -1;
	for (int i = 0; i < solution_operating.size(); ++i) {//遍历解内所有成员，找放回后使连通度上升最少的
		int cnty_increase = 0;
		int cpn_id;
        int size;
		int cpn_size = 1;
		vector<bool> visited(vertex_num, false);
		for (auto &adj:adjlist[solution_operating[i]])
			if (!deleted[adj] && !visited[cpn_id = vertex_component_id[adj]]) {
				visited[cpn_id] = true;
                cpn_size += (size = components[cpn_id].size());
				cnty_increase -= size * (size - 1) / 2;
			}
		cnty_increase += cpn_size * (cpn_size - 1) / 2;
		if (cnty_increase <= min_increase) {
			min_increase = cnty_increase;
			idx = i;
		}
	}
	cnty_operating += min_increase;
	remove_vertex = solution_operating[idx];
	solution_operating.erase(solution_operating.begin() + idx);
	deleted[remove_vertex] = false;
	weight[remove_vertex] = 0;
	int cpn_id;
	vector<bool> visited(vertex_num, false);
	for (auto &neibor:adjlist[remove_vertex])//更新component的id使用情况
		if (!deleted[neibor] && !visited[cpn_id = vertex_component_id[neibor]]) {
			visited[cpn_id] = true;
			components[cpn_id].clear();
			unused_component_id.push(cpn_id);
			used_component_id.erase(cpn_id);
		}
	vector<bool> tmp_visited(vertex_num, false);
	deth_first_search_split(remove_vertex, tmp_visited, false);//更新component
	return remove_vertex;
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

//只需要得到连通度，不需要将原图分割、记录子图信息时，使用该函数
int get_connectivity() {
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

void component_based_neghborhood_search() {
    clock_t func_start_time = clock();
    fill(weight, weight + vertex_num, 0);
	/*
	for(int i = 0; i < vertex_num; ++i) {
		weight[i] = adjlist[i].size();
	}*/
	vector<int> local_best_solution = solution_operating;
	seperate_graph();
	int local_min_connectivity = cnty_operating;
	int idle_iter = 0;
	int add_vertex, remove_vertex;
	while (idle_iter < MaxIdleIters) {//无论新得到的解是否比原来的好，这里都直接更新了
		add_vertex = key_vertexs[select_large_component()];
		solution_operating.push_back(add_vertex);//增加顶点
		add_to_solution(add_vertex);
		remove_vertex = remove_from_solution();
		++iter;
		if (cnty_operating < local_min_connectivity) {//增量式更新连通度使用的地方
			local_min_connectivity = cnty_operating;
			local_best_solution = solution_operating;
			idle_iter = 0;
		}
		else idle_iter++;
	}
	for (auto &v:solution_operating) deleted[v] = false;
	solution_operating = local_best_solution;
	for (auto &v:solution_operating) deleted[v] = true;
	seperate_graph();
    func_time += (double)(clock() - func_start_time) / CLOCKS_PER_SEC;
}

void population_initialization() {//初始化的连通度相差较大，可以尝试加大人口，或者加大local search迭代次数，提高初始化连通度
	for (int i = 0; i < parent_num; ++i) {
		fill(deleted, deleted + vertex_num, false);
		//fill(conf_changed, conf_changed + vertex_num, false);
		solution_operating.resize(K);
		for (int j = 0; j < K; ++j) {
			solution_operating[j] = rand() % vertex_num;
			while (deleted[solution_operating[j]]) solution_operating[j] = rand() % vertex_num;
			deleted[solution_operating[j]] = true;
		}//为什么每次初始化得到的解的连通度都一样，而且每次都只剩下一个cpn？运行时间间隔太小导致srand()函数没有发挥作用，而导致得到的解都一样
		component_based_neghborhood_search();//还是图的关系，初始化得到的解都一样差？
		while (true) {
			bool differ = true;
			vector<bool> visited(vertex_num, false);
			for(auto &v : solution_operating) visited[v] = true;
			for (int j = 0; j < i; ++j) {
				int dis = 0;
				for(auto &v:solutions[j]) dis += visited[v];
				dis = K - dis;
				if (dis == 0) {//可以设为小于某个阈值，则进行交换操作？
					differ = false;
					break;
				}
			}
			if (differ) break;
			int idx = rand() % K;
			int add_vertex = rand() % vertex_num;
			while(deleted[add_vertex]) add_vertex = rand() % vertex_num;
			deleted[solution_operating[idx]] = false;
			deleted[add_vertex] = true;
			solution_operating[idx] = add_vertex;
		}
		solutions[i] = solution_operating;
		int cnty = (connectivities[i] = get_connectivity());
		cout << i <<  " initialization connectivity : " << cnty << endl;
		if(cnty < min_connectivity_once) {//记录单次最优解
			min_connectivity_once = cnty;
			best_solution_once = solution_operating;
		}
		for(int j = 0; j < i; ++j) {//初始化距离矩阵与总距离
            int common = 0;
            for(int m = 0; m < K; ++m) common += deleted[solutions[j][m]];
            int dis = K - common;
            total_distances[j] += dis;
            total_distances[i] += dis;
        }
	}
}

void double_backbone_based_crossover(vector<int> &S1, vector<int> &S2) {
	vector<int> XB;
	fill(deleted, deleted + vertex_num, false);//重置del数组，表示所有点都未放进S
	//fill(conf_changed, conf_changed + vertex_num, false);
	solution_operating.clear();
	vector<bool> visited(vertex_num, false);
	for (auto &v:S1) visited[v] = true;
	for (auto &v:S2)
		if (visited[v]) {
			solution_operating.push_back(v);//在s1也在s2的点
			deleted[v] = true;
			visited[v] = false;
		}
		else XB.push_back(v);//在s2但是不在s1里的点
	for (auto &v:S1)
		if (visited[v]) XB.push_back(v);//在s1但是不在s2里的点
	for (auto &v : XB)
		if (rand() % 100 <= SP0) {
			solution_operating.push_back(v);
			deleted[v] = true;
		}
	if(solution_operating.size() == K) return;
	seperate_graph();//划分cpn
	for (auto &v:S1) visited[v] = true;
	for (auto &v:S2) visited[v] = true;//记录XC
	while (solution_operating.size() < K) {//不够K的话要加顶点到后代
		int large_idx = select_large_component();
		vector<int>& large_cpn = components[large_idx];
		int idx = rand() % large_cpn.size();
		int add_vertex = large_cpn[idx];
		if (!visited[add_vertex] && !deleted[add_vertex]) {
			solution_operating.push_back(add_vertex);
			add_to_solution(add_vertex);
		}
	}
	while (solution_operating.size() > K) remove_from_solution();
}

bool distance_compare(int i, int j) {return total_distances[i] > total_distances[j];}
bool cnty_compare(int i, int j) {return connectivities[i] < connectivities[j];}

void rank_based_pool_updating(int connectivity) {//尝试不要直接加进去再算要不要加，而是根据原本的解，构建一个阈值，不用每次计算这么多
	solutions[parent_num] = solution_operating;
	connectivities[parent_num] = connectivity;
	vector<int> index(parent_num + 1, -1);
	for(int i = 0; i < parent_num + 1; ++i) index[i] = i;
	stable_sort(index.begin(), index.end(), cnty_compare);
	for(int i = 0; i < parent_num + 1; ++i) rank_connectivity[index[i]] = i;
	vector<int> diss(parent_num);//新产生的解与其他解之间的距离
	int dis;
	//int tmp = 0;
	total_distances[parent_num] = 0;
	for(int i = 0; i < parent_num; ++i) {//求总距离
		dis = 0;
		for(auto &v : solutions[i]) dis += deleted[v];
		dis = K - dis;
		diss[i] = dis;
		total_distances[parent_num] += dis;
		total_distances[i] += dis;
		//cout << total_distances[i] << " ";
		//tmp += total_distances[i];
	}
	//cout << total_distances[parent_num] << " " << (tmp + total_distances[parent_num]) / (parent_num + 1) << endl;
	stable_sort(index.begin(), index.end(), distance_compare);
	for(int i = 0; i < parent_num + 1; ++i) rank_distance[index[i]] = i;
	/*
	for(auto &r : rank_distance) cout << r << " ";
	cout << endl;
	for(auto &cnty : connectivities) cout << cnty << " ";
	cout << endl;
	for(auto &r : rank_connectivity) cout << r << " ";
	cout << endl;
	*/
	int idx = -1;
	double max_score = -1, score;
	for(int i = 0; i < parent_num + 1; ++i) {//找出加权排名最低的解
		score = BETA * rank_connectivity[i] + (1 - BETA) * rank_distance[i];//求加权排名
		if(score > max_score) {
			idx = i;
			max_score = score;
		}
	}
	if(idx == parent_num) {
		for(int i = 0; i < parent_num; ++i) total_distances[i] -= diss[i];
		return;
	}
	vector<bool> visited(vertex_num, false);
	for(auto &v : solutions[idx]) visited[v] = true;
	for(int i = 0; i < parent_num + 1; ++i) {
		int dis = 0;
		for(auto &v : solutions[i]) dis += visited[v];
		dis = K - dis;
		total_distances[i] -= dis;
	}
	swap(solutions[idx], solutions[parent_num]);
	total_distances[idx] = total_distances[parent_num];//total_distances需要更新
	connectivities[idx] = connectivities[parent_num];//交换connectivity，交换rank
}

void Critical_Node_Problem() {
	srand(time(0));
	min_connectivity_once = vertex_num * vertex_num;//该次最小的连通度
	best_solution_once.clear();
	start_time = clock();
	population_initialization();//初始化所有解
	init_cost_time += time_cost();
	start_time = clock();
	double cost_time;
	fill(weight, weight + vertex_num, 0);
	while (!timeout()) {
		int Si = rand() % parent_num;
		int Sj = rand() % parent_num;
		while (Si == Sj) Si = rand() % parent_num, Sj = rand() % parent_num;
		double_backbone_based_crossover(solutions[Si], solutions[Sj]);
		component_based_neghborhood_search();
		if (cnty_operating < min_connectivity_once) {
			best_solution_once = solution_operating;
			min_connectivity_once = cnty_operating;
			cost_time = time_cost();
		}
		cout << "min connectivity once : " << min_connectivity_once << " / " << cnty_operating << endl;
		cout << "best ever : " << f_best << endl;
		rank_based_pool_updating(cnty_operating);
	}
	if (min_connectivity_once < f_best) {//更新所有次数最优解
        best_solution = best_solution_once;
        f_best = min_connectivity_once;
        t_avg = cost_time;
        succeed_times = 1;
    }
    else if (min_connectivity_once == f_best) {
		t_avg += cost_time;
		succeed_times++;
	}
	min_cnty.push_back(min_connectivity_once);
    f_avg += min_connectivity_once;
	out << min_connectivity_once << endl;
}

void one_benchmark(string filename, int k) {
	K = k;
	read_graph(filename);
    f_best = vertex_num * vertex_num;
	f_avg = 0;
	succeed_times = 0;
    t_avg = 0;
	init_cost_time = 0;
	func_time = 0;
	iter = 0;

	min_cnty.clear();
    for (int i = 0; i < run_times; ++i) Critical_Node_Problem();
	out << filename << endl;
	for (int i = 0; i < run_times; ++i) out << min_cnty[i] << " ";
	out << endl;
	out << fixed;
    out << "f_best " << f_best << endl;
    out << "f_avg " << setprecision(1) << double(f_avg)/run_times << endl;
    out << "succeed_times " << succeed_times << endl; 
    out << "t_avg " << setprecision(1) << t_avg / succeed_times << endl;
    out << "init_cost_time " << setprecision(1) << init_cost_time / run_times << endl;
    out << "func_time " << setprecision(1) << func_time / run_times << endl;
    out << "iter " << iter << endl << endl << endl;

	for (int i = 0; i < run_times; ++i) cout << min_cnty[i] << " ";
	cout << endl;
    cout << fixed;
	cout << "SP0 = " << SP0 << endl;
    cout << "f_best " << f_best << endl;
    cout << "f_avg " << setprecision(1) << double(f_avg)/run_times << endl;
    cout << "succeed_times " << succeed_times << endl; 
    cout << "t_avg " << setprecision(1) << t_avg / succeed_times << endl;
    cout << "init_cost_time " << setprecision(1) << init_cost_time / run_times << endl;
    cout << "func_time " << setprecision(1) << func_time / run_times << endl;
    cout << "iter " << iter << endl;
}


int main() {
	vector<string> file_names = {"BenchMarks/cnd/WattsStrogatz_n500.txt", "BenchMarks/cnd/ErdosRenyi_n2500.txt", 
	"BenchMarks/RealInstances/powergrid.txt", "BenchMarks/RealInstances/Hamilton5000.txt"};
	vector<int> Ks = {125, 200, 494, 500};
	string results_filename = "results_MA.txt";
	out.open(results_filename);
	for(int i = 0; i < 4; ++i) one_benchmark(file_names[i], Ks[i]);
	system("pause");
	return 0;
}
