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
int steps = 0.01 * N;
int D = 0;//ÉèÖÃÎªconst 
int m = 0.025 * steps;

int** adjlist = new int*[vertex_num + 1];
int* vertex_degree = new int[vertex_num + 1];

double alpha = 1;
int* w = new int[vertex_num + 1];

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
		w[i] = neibors.size();
		D += neibors.size();
		if (i % 100000 == 0) cout << cur_node << endl;
	}
}

int random_walk() {
	srand((unsigned)time(NULL)*100);
	
	int rand_int = rand() % D;
	int sum_degree = 0;
	int first_node = -1;
	for (int i = 1; i < vertex_num + 1; ++i) {//Ï¸½ÚË¼¿¼ 
		if (rand_int >= sum_degree && rand_int < sum_degree + vertex_degree[i]) {
			first_node = i;
			break;
		}
		else sum_degree += vertex_degree[i];
	}
	//cout << "first_node : " << first_node << endl; 
	int* R = new int[steps];
	R[0] = first_node;
	int last_node = first_node;
	for (int i = 0; i < steps; ++i) {
		last_node = adjlist[last_node][rand() % vertex_degree[last_node]];
		R[i] = last_node;
		//cout << i << " " << last_node << endl;
	}
	//cout << "here" << R[steps - 1] << endl;
	unsigned long long int P = 0, Q = 0;
	for (int i = 0; i < steps - m + 1; ++i) {
		for (int j = i + m; j < steps; ++j) {
			P += w[R[i]] * (R[i] == R[j] ? 1 : 0);
			assert(vertex_degree[R[j]]);
			Q += w[R[i]] * vertex_degree[R[i]] / vertex_degree[R[j]];
		}
	}
	delete [] R;
	return Q / P;
}

int main() {
	for(int i = 0; i < vertex_num + 1; ++i) {
		vertex_degree[i] = 0;
		adjlist[i] = NULL;
	}
	string file_name = "Flickr_Handled.txt";
	read_adj(file_name);
	ofstream out;
	out.open("version0_results4.txt");
	while(true) {
		int tmp = random_walk() - N;
		out << tmp << endl;
		cout << tmp << endl;
	}
}

