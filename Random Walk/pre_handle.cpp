
//增量式更新连通度使用的方法：维护一个connectivity变量，对应为solution_operting的连通度，
//然后在add_to_solution和remove_from_solution两个函数更新子图信息时，同时更新连通度而不用再计算

//经常重复分配visited数组比较需要比较多时间还是维护visited数组需要比较多时间

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

#define maxn 30100
#define BETA 0.6
#define SP0 85
#define MaxIdleIters 1000//是否太大了
#define parent_num 20

int kbv;//目前已知的最小连通度
int K;//可以删去的最大定点数
vector<vector<int>> adjlist;//整个图的邻接矩阵
int vertex_num;//图中顶点总数

int run_times;//运行次数
vector<int> solution_operting;//当前操作的解
vector<int> best_solution_once;//单次最优解
int min_connectivity_once;//单次最优解的连通度
vector<int> best_solution;//所有次数里的最佳解
int f_best;//最优解的连通度
int f_avg;//所有单次最优解的平均连通度
int succeed_times;//达到最优解的次数
int exch;//交换次数

int weight[maxn];//每个顶点的权重，每次local search时都更新，还是全程只要一次初始化
int vertex_component_id[maxn];//每个顶点所属的子图的id
bool deleted[maxn];//删除的点/在当前操作的解中的顶点

int XB[maxn];//s1, s2有且仅有一个包含的顶点
vector<int> components[maxn];//连通子图
vector<int> solutions[parent_num + 10];//解的集合

int min_component_size;//最小的子图的大小
int max_component_size;//最大子图的大小
stack<int> unused_component_id;//未使用的子图id
set<int> used_component_id;//已使用的子图id

double t_avg;//找到最优解所用的平均时间
double init_cost_time;//初始化使用的时间
double func_time;//调用函数解决所用的时间
long long iter;//迭代次数，即交换次数
clock_t start_time;//用于计算时间
double time_out;//每次运行函数允许使用的最大时间

vector<int> connectivities(parent_num + 1, 0);//每个解的连通度
int* key_vertexs = new int[maxn];//每个子图中权重最大的顶点
vector<int> tmp_dis(parent_num + 1, 0);
vector<vector<int>> distances(parent_num + 1, tmp_dis);//解与解之间的距离矩阵
vector<int> total_distances(parent_num + 1, 0);//解与其他解的总距离
vector<int> rank_connectivity(parent_num + 1, 0);//解的连通度排名

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
	unused_component_id.pop();
	used_component_id.insert(cpn_id);
	visited_vertex.clear();//新component包含的顶点

	//深度优先遍历，注意每个点在加入stack时就要把visited置为true
	stack<int> to_visit;
	to_visit.push(start);
	visited[start] = true;
	int key_vertex = start;//权重最大的顶点
	int vertex;
	while(!to_visit.empty()) {
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
	key_vertexs[cpn_id] = key_vertex;

	//记录最大的cpn的size与最小的size
	int cpn_size = visited_vertex.size();
	if(cpn_size > max_component_size) max_component_size = cpn_size;
	if(cpn_size < min_component_size) min_component_size = cpn_size;

	return cpn_size;
}

int seperate_graph() {//可以采用蔡泽杰的方法求连通度
	min_component_size = vertex_num;
	max_component_size = 0;

	while (!unused_component_id.empty()) unused_component_id.pop();
	for (int i = 0; i <= vertex_num; ++i) unused_component_id.push(i);  //add one more
	used_component_id.clear();

	vector<bool> visited(vertex_num, false);
	int connectivity = 0;
	for (int i=0; i<vertex_num; ++i)
		if (!deleted[i] && !visited[i]) {
			int size = deth_first_search_split(i, visited, false);
			connectivity += (size - 1) * size / 2;
		}
	return connectivity;
}

int select_large_component() {
	int mean_cpn_size = (max_component_size + min_component_size) / 2;
	vector<int> large_component_id;
	for (auto &num:used_component_id)
		if (components[num].size() >= mean_cpn_size)
			large_component_id.push_back(num);
	return large_component_id[rand() % large_component_id.size()];
}

void remove_from_solution() {                        //remove the optimal one 
	int min_increase = vertex_num * vertex_num;
	int remove_vertex = -1;
	int idx = -1;
	for (int i = 0; i < solution_operting.size(); ++i) {//遍历解内所有成员，找放回后使连通度上升最少的
		int cnty_increase = 0;
		int cnt = 0;
		int cur;
		int cpn_size = 0;
		vector<bool> visited(vertex_num, false);
		for (auto &adj:adjlist[solution_operting[i]])
			if (!deleted[adj])
				if (!visited[cur = vertex_component_id[adj]]) {//这里的visited有没有被其他函数修改了，修改为参数传递过来而不是全局变量？
					visited[cur] = true;//直接每次要用visited都初始化为false，如果是同一个visited，就作为参数传递过去
					cnty_increase += components[cur].size() * cpn_size;
					cpn_size += components[cur].size();
				}
		cnty_increase += cpn_size;
		for (auto &adj:adjlist[solution_operting[i]])
			if (!deleted[adj]) visited[vertex_component_id[adj]] = false;
		if (cnty_increase <= min_increase) {
			min_increase = cnty_increase;
			idx = i;
		}
	}
	remove_vertex = solution_operting[idx];
	solution_operting.erase(solution_operting.begin() + idx);
	deleted[remove_vertex] = false;
	weight[remove_vertex] = 0;
	
	//更新component的id使用情况
	int cpn_id;
	vector<bool> visited(vertex_num, false);
	for (auto &neibor:adjlist[remove_vertex])
		if (!deleted[neibor] && !visited[cpn_id = vertex_component_id[neibor]]) {
			visited[cpn_id] = true;
			unused_component_id.push(cpn_id);
			used_component_id.erase(cpn_id);
		}

	//更新component
	vector<bool> tmp_visited(vertex_num, false);
	deth_first_search_split(remove_vertex, tmp_visited, false);
}

void add_to_solution(int add_vertex) {         //remove the specific one
	int cur = vertex_component_id[add_vertex];
	deleted[add_vertex] = true;
	for (auto &num:adjlist[add_vertex])
		if (!deleted[num]) {
			vector<bool> visited(vertex_num, false);
			deth_first_search_split(num, visited, true);//重新分割原来的component
		}
	unused_component_id.push(cur);
	used_component_id.erase(cur);
}

void component_based_neghborhood_search() {
    clock_t func_start_time = clock();
    fill(weight, weight + vertex_num, 0);

	int connectivity = seperate_graph();
	int idle_iter = 0;
	int tmp;
	while (idle_iter < MaxIdleIters) {
		int remove_vertex = key_vertexs[select_large_component()];
		solution_operting.push_back(remove_vertex);//增加顶点
		add_to_solution(remove_vertex);
		remove_from_solution();
        ++iter;
		if ((tmp = seperate_graph()) < connectivity) {//增量式更新连通度使用的地方
			connectivity = tmp;
			idle_iter = 0;
		}
		else idle_iter++;
	}
    func_time += (double)(clock() - func_start_time) / CLOCKS_PER_SEC;
}

double get_distance(vector<int> &S1, vector<int> &S2) {
	int common = 0;
	vector<bool> visited(vertex_num, false);
	for (auto &num:S1) visited[num] = true;
	for (auto &num:S2) common += visited[num];
	return K - common;
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

void population_initialization() {//初始化的连通度相差较大，可以尝试加大人口，或者加大local search迭代次数，提高初始化连通度
	for (int i = 0; i < parent_num; ++i) {
		fill(deleted, deleted + vertex_num, false);
		solution_operting.resize(K);
		for (int j = 0; j < K; ++j) {
			solution_operting[j] = rand()%vertex_num;
			while (deleted[solution_operting[j]]) solution_operting[j] = rand() % vertex_num;
			deleted[solution_operting[j]] = true;
		}
		component_based_neghborhood_search();
		while (true) {
			bool differ = true;
			for (int j = 0; j < i; ++j)
				if (get_distance(solution_operting, solutions[j]) == 0) {//可以设为小于某个阈值，则进行交换操作？
					differ = false;
					break;
				}
			if (differ) break;
			int idx = rand() % K;
			int add_vertex = rand() % vertex_num;
			while(deleted[add_vertex]) add_vertex = rand() % vertex_num;
			deleted[solution_operting[idx]] = false;
			deleted[add_vertex] = true;
			solution_operting[idx] = add_vertex;
		}
		solutions[i] = solution_operting;
		int cnty = (connectivities[i] = get_connectivity());
		cout << i <<  " initialization connectivity : " << cnty << endl;

		//记录单次最优解
		if(cnty < min_connectivity_once) {
			min_connectivity_once = cnty;
			best_solution_once = solution_operting;
		}
		
		//初始化距离矩阵与总距离
		for(int j = 0; j < i; ++j) {
            int common = 0;
            for(int m = 0; m < K; ++m) common += deleted[solutions[j][m]];
            int dis = K - common;
            distances[i][j] = (distances[j][i] = dis);
            total_distances[j] += dis;
            total_distances[i] += dis;
        }
	}

	//初始化各个解的连通度排名
	vector<int> v_connectivity(connectivities.begin(), connectivities.end() - 1);
	sort(v_connectivity.begin(), v_connectivity.end());//手写用二分插入方法而不用排序。
	for(int i = 0; i < parent_num; ++i) {
		auto it = find(v_connectivity.begin(), v_connectivity.end(), connectivities[i]);
		rank_connectivity[i] = distance(v_connectivity.begin(), it);
	}
}

void double_backbone_based_crossover(vector<int> &S1, vector<int> &S2) {
	int cnt = 0;
	fill(deleted, deleted + vertex_num, false);//重置del数组，表示所有点都未放进S
	solution_operting.clear();
	vector<bool> visited(vertex_num, false);
	for (auto &num:S1) visited[num] = true;
	for (auto &num:S2)
		if (visited[num]) {
			solution_operting.push_back(num);//在s1也在s2的点
			visited[num] = false;
		}
		else XB[cnt++] = num;//在s2但是不在s1里的点
	for (auto &num:S1)
		if (visited[num]) XB[cnt++] = num;//在s1但是不在s2里的点
	for (int i=0; i<cnt; ++i)
		if (rand() % 100 <= SP0) solution_operting.push_back(XB[i]);

	for (auto &num:solution_operting) deleted[num] = true;
	if(solution_operting.size() == K) return;
	seperate_graph();
	if (solution_operting.size() < K) {
		for (auto &num:S1) visited[num] = true;
		for (auto &num:S2) visited[num] = true;
		while (solution_operting.size() < K) {
			int large_idx = select_large_component();
			vector<int>& cur = components[large_idx];
			int idx = rand() % components[large_idx].size();
			if (!visited[cur[idx]] && !deleted[cur[idx]]) {
				solution_operting.push_back(cur[idx]);
				add_to_solution(solution_operting.back());
			}
		}
	}
	while (solution_operting.size() > K) remove_from_solution();
}

bool compare(int a, int b) {return a > b;}

void rank_based_pool_updating(int connectivity) {//尝试不要直接加进去再算要不要加，而是根据原本的解，构建一个阈值，不用每次计算这么多
	solutions[parent_num] = solution_operting;

	//更新连通度以及连通度排名
	connectivities[parent_num] = connectivity;
	int count = 0;
	for(int i = 0; i < parent_num; ++i)
		if(connectivities[i] > connectivity) {
			rank_connectivity[i]++;
			count++;
		}
	rank_connectivity[parent_num] = parent_num - count;

	//求总距离
	for(int i = 0; i < parent_num; ++i) {
		int dis = 0;
		for(int j = 0; j < K; ++j) dis += deleted[solutions[i][j]];
		dis = K - dis;
		distances[parent_num][i] = dis;
		distances[i][parent_num] = dis;
		total_distances[parent_num] += dis;
		total_distances[i] += dis;
	}//get_distance已经优化为，总是求同一个解与其他不同的解时的距离时
	vector<int> v_distance = total_distances;
	sort(v_distance.begin(), v_distance.end(), compare);

	//找出加权排名最低的解
	int idx = -1;
	double max_score = -1;
	for(int i = 0; i < parent_num + 1; ++i) {
		auto it = find(v_distance.begin(), v_distance.end(), total_distances[i]);//返回该total_distance在排序后的数组中的迭代器
		double score = BETA * rank_connectivity[i] + (1 - BETA) * distance(v_distance.begin(), it);//求加权排名
		if(score > max_score) {
			idx = i;
			max_score = score;
		}
	}

	if(idx == parent_num) return;

	//更新距离矩阵distances，总距离total_distances
	//total_distance需要更新，distances上三角与下三角都要更新
	vector<int> delete_distances = distances[idx];
	for(int i = 0; i < idx; ++i) 
		distances[i][idx] = (distances[idx][i] = distances[parent_num][i]);
	for(int i = idx + 1; i < parent_num; ++i) 
		distances[idx][i] = (distances[i][idx] = distances[parent_num][i]);
	total_distances[idx] = total_distances[parent_num];
	total_distances[parent_num] = 0;
	for(int i = 0; i < parent_num; ++i) 
		if(i != idx)
			total_distances[i] -= delete_distances[i];
		else total_distances[i] -= delete_distances[parent_num];
	swap(solutions[idx], solutions[parent_num]);

	//交换connectivity，交换rank
	int delete_connectivtiy = connectivities[idx];
	connectivities[idx] = connectivities[parent_num];
	rank_connectivity[idx] = rank_connectivity[parent_num];
	for(int i = 0; i < parent_num + 1; ++i) 
		if(connectivities[i] >= delete_connectivtiy) rank_connectivity[i]--;
}

void Critical_Node_Problem() {
	srand(time(0));
	min_connectivity_once = vertex_num * vertex_num;//该次最小的连通度
	best_solution_once.clear();

	//初始化所有解
	start_time = clock();
	population_initialization();
	init_cost_time += time_cost();

	start_time = clock();
	double cost_time;

	fill(weight, weight + vertex_num, 0);
	while (!timeout()) {
		int Si = rand() % parent_num, Sj = rand() % parent_num;
		while (Si == Sj) Si = rand() % parent_num, Sj = rand() % parent_num;
		double_backbone_based_crossover(solutions[Si], solutions[Sj]);
		component_based_neghborhood_search();
		int offspring_connectvity = seperate_graph();
		if (offspring_connectvity < min_connectivity_once) {
			best_solution_once = solution_operting;
			min_connectivity_once = offspring_connectvity;
			cost_time = time_cost();
		}
		cout << "find solution objective value so far this time : " << min_connectivity_once << endl;
		cout << "best ever : " << f_best << endl;
		if (offspring_connectvity <= kbv) {
			cout << "find best solution " << kbv << endl;
			cout << "time_cost : " << time_cost() << endl;
			//break;
		}
		rank_based_pool_updating(offspring_connectvity);
	}

	//更新所有次数最优解
	if (min_connectivity_once < f_best) {
        best_solution = best_solution_once;
        f_best = min_connectivity_once;
        t_avg = cost_time;
        succeed_times = 1;
    }
    else if (min_connectivity_once == f_best) {
		t_avg += cost_time;
		succeed_times++;
	}
    f_avg += min_connectivity_once;
}

void print(vector<int> &S){
	sort(S.begin(), S.end());
	for (auto &vertex:S) cout << vertex << " ";
	fill(deleted, deleted + vertex_num, false);
	for (auto &num:S) deleted[num]=true;
	cout << "\n" << seperate_graph() << endl;
}

void show_adjlist() {
	for(int i = 0; i < vertex_num; ++i) {
		cout << i << " : ";
		for(int j = 0; j < adjlist[i].size(); ++j) {
			cout << adjlist[i][j] << " ";
		}
		cout << endl;
	}
}

int main() {
	K = 125;
	kbv = 2078;
	string filename = "BenchMarks/cnd/WattsStrogatz_n500.txt";
	read_graph(filename);
	time_out = 3600;
	run_times = 30;
    f_best = vertex_num * vertex_num;
	f_avg = 0;
	succeed_times = 0;
    t_avg = 0;
	init_cost_time = 0;
	func_time = 0;
	iter = 0;
    for (int i = 0; i < run_times; ++i) Critical_Node_Problem();
    cout << fixed;
    cout << "f_best " << f_best << endl;
    cout << "f_avg " << setprecision(1) << double(f_avg)/run_times << endl;
    cout << "succeed_times " << succeed_times << endl; 
    cout << "t_avg " << setprecision(1) << t_avg / succeed_times << endl;
    cout << "init_cost_time " << setprecision(1) << init_cost_time / run_times << endl;
    cout << "func_time " << setprecision(1) << func_time / run_times << endl;
    cout << "iter " << iter << endl;
    return 0;
}
