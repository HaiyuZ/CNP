#include <iostream>
#include <sstream>
#include <fstream>
#include <string.h>
#include <vector>
#include <set>
#include <time.h>
#include <stdlib.h>
#include <assert.h>
#include <stack>
#include <algorithm>
#include <iomanip>
#include <math.h>
using namespace std;

const int vertex_num = 2585569;
const int N = 2302925;
const double mined_percentage = 0.01;
const double Alpha = 2.7;
int D = 0;//设置为const 

int steps = mined_percentage * N;
int m = 0.025 * steps;

int** adjlist = new int*[vertex_num + 1];
int* vertex_degree = new int[vertex_num + 1];
double* w = new double[vertex_num + 1];
int* R = new int[steps];

void read_adj(string file_name) {
	ifstream FIC;
	FIC.open(file_name);
	string line;
	for (int i = 0; i < N; ++i) {
		getline(FIC, line);
		istringstream iss(line);
		int cur_node;
		iss >> cur_node;
		int neibor;
		vector<int> neibors;
		while(iss >> neibor) {
			neibors.push_back(neibor);
		}
		adjlist[cur_node] = new int[neibors.size()];
		for(int i = 0; i < neibors.size(); ++i) adjlist[cur_node][i] = neibors[i];
		vertex_degree[cur_node] = neibors.size();
		D += neibors.size();
		if (i % 100000 == 0) cout << cur_node << endl;
	}
}

int random_walk() {
	srand((unsigned)time(NULL)*100);
	
	int rand_int = rand() % D;
	int sum_degree = 0;
	int first_node = -1;
	for (int i = 1; i < vertex_num + 1; ++i) {
		if (rand_int >= sum_degree && rand_int < sum_degree + vertex_degree[i]) {
			first_node = i;//generate the first node
			break;
		}
		else sum_degree += vertex_degree[i];
	}
	R[0] = first_node;
	int last_node = first_node;
	for (int i = 1; i < steps; ++i) {
		R[i] = adjlist[R[i - 1]][rand() % vertex_degree[R[i - 1]]];//random walk
	}
	
	unsigned long long int P = 0, Q = 0;
	for (int i = 0; i < steps - m + 1; ++i) 
		for (int j = i + m; j < steps; ++j) {//calculate P and Q
			P += (w[R[i]] + w[R[j]]) * (R[i] == R[j] ? 1 : 0);
			Q += w[R[i]] * vertex_degree[R[i]] / vertex_degree[R[j]] +
				 w[R[j]] * vertex_degree[R[j]] / vertex_degree[R[i]];
		}
	return Q / P;
}

int main() {
	for(int i = 0; i < vertex_num + 1; ++i) {
		vertex_degree[i] = 0;
		adjlist[i] = NULL;
	}//initialize the arrays;
	
	string file_name = "Flickr_Handled.txt";
	read_adj(file_name);//read the pre-handled file; 
	
	for(int i = 1; i < vertex_num + 1; ++i) {
		w[i] = pow(vertex_degree[i], Alpha);//set weight function Alpha; 权重函数形式可变？ 
	}
	
	ofstream out;
	out.open("Alpha2.7Mined1.txt");
	int times = 200;
	while(times) {
		time--;
		int tmp = random_walk() - N;
		out << tmp << endl;
		cout << tmp << endl;
	}
}
