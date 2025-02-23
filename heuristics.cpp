#include <iostream>
#include <fstream>
#include <cmath>
#include "stdlib.h"
#include "stdio.h"
#include <string>
#include "string.h"
#include "omp.h"
#include "global.h"
#include "naive.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <cstdlib>

using namespace std;

int checkInverse(int *a, int* iap, int* ia, int N, int P) {
	for (int p = 0; p < P; p++) {
		for (int i = 0; i < N; i++) {
			int target = a[p + i * P];

			int found = 0;
			for (int iaptr = iap[p * (N + 1) + target]; iaptr < iap[p * (N + 1) + target + 1]; ++iaptr) {
				int incoming = ia[p * N + iaptr];
				if (i == incoming) {
					found = 1;
					break;
				}
			}

			if (!found) {
				out << "something is wrong " << i << " goes to " << target << " with " << p << " but it is not in the inverse automata\n";
				exit(1);
			}
		}
	}

	for (int p = 0; p < P; p++) {
		for (int i = 0; i < N; i++) {
			for (int iaptr = iap[p * (N + 1) + i]; iaptr < iap[p * (N + 1) + i + 1]; ++iaptr) {
				int source = ia[p * N + iaptr];
				if (a[p + source * P] != i) {
					out << "something is wrong " << i << " has " << source << " in inverse automata but it " << source << " goes to " << a[p + source * P] << " with " << p << "\n";
					exit(1);
				}
			}
		}
	}

	return 0;
}

int main(int argc, char** argv) {
	if (argc < 5 || !(strcmp(argv[4], "rand") == 0 || argc == 5 + atoi(argv[2]) * atoi(argv[1]) && strcmp(argv[4], "arg") == 0)) {
		cout << "Usage: " << argv[0] << " no_states alphabet_size rand_seed rand weight_upper_bound\n" << endl;
		cout << "Usage: " << argv[0] << " no_states alphabet_size rand_seed arg weight_1 ... weight_P\n" << endl;
		return 1;
	}

	char* filename = new char[256];
	snprintf(filename, 256, "synchrop1_%s_%s_%s_%s.txt", argv[1], argv[2], argv[3], argv[5]);
	out.open(filename);

	int N = atoi(argv[1]);
	int P = atoi(argv[2]);
	unsigned int seed = atoi(argv[3]);
	int wd = atoi(argv[5]);

#ifdef LOG_LEVEL
	char* filename = new char[256];

	struct stat st = { 0 };

	sprintf(filename, "results/%s_%s", argv[1], argv[2]);
	if (stat("results", &st) == -1) {
		mkdir("results", 0700);
	}

#if LOG_LEVEL & TIME_ANALYSIS
	sprintf(filename, "%s_time_and_length", filename);
#endif
#if LOG_LEVEL & DATA_ANALYSIS
	sprintf(filename, "%s_data", filename);
#endif
#if LOG_LEVEL & LEVEL_ANALYSIS
	sprintf(filename, "%s_level", filename);
#endif
	sprintf(filename, "%s.csv", filename);

	out.open(filename, ios::app);
	free(filename);
#endif

	int* automata = new int[P * N];
	int* weights = new int[P];

	unsigned int tseed = (omp_get_thread_num() + 1) * (seed + 1912812);


#ifdef __GNUC__
		for (int i = 0; i < P * N; ++i) {
			if(i != (P*N - 1))
			automata[(i*P)%(P*N-1)] = ((int)rand_r(&tseed)) % N;
			else
			automata[i] = ((int)rand_r(&tseed)) % N;
		}

		if (strcmp(argv[4], "rand") == 0) {
			for (int i = 0; i < P; i++) {
				//weights[i] = 1;
				weights[i] = ((int)rand_r(&tseed) % wd) + 1;
			}
		}
		/*
		automata[0] = 2;
		automata[2] = 0;
		automata[4] = 0;
		automata[6] = 3;
		automata[1] = 2;
		automata[3] = 1;
		automata[5] = 3;
		automata[7] = 2;
		weights[0] = 10;
		weights[1] = 15;
		*/
#endif

#ifdef _WIN32
		srand(tseed);/*
		automata[0] = 2;
		automata[1] = 2;
		automata[2] = 2;
		automata[3] = 1;
		automata[4] = 2;
		automata[5] = 2;*/

		for (int i = 0; i < P * N; ++i) {
			if(i != (P*N - 1))
			automata[(i*P)%(P*N-1)] = ((int)rand()) % N;
			else
			automata[i] = ((int)rand()) % N;
		}

		if (strcmp(argv[4], "rand") == 0) {
			for (int i = 0; i < P; i++) {
				//weights[i] = 1;
				weights[i] = ((int)rand() % wd) + 1;
			}
		}
		

		
		
		/*weights[0] = 10;
		weights[1] = 2;
		*/
#endif
		else {
			for (int i = 0; i < P; i++) {
				weights[i] = atoi(argv[i+5]);
			}
		}

#ifdef DEBUG
	printAutomata(automata, N, P, weights);
#endif

	/*out << P << " "<< N << endl;
	for(int i = 0; i < N; ++i) {
	for(int j = 0; j < P; ++j) {
	out << automata[j][i] << " ";
	}
	out << endl;
	}*/

	int* inv_automata_ptrs = new int[P * (N + 1)];
	int* inv_automata = new int[P * N];

#pragma omp parallel for schedule(static)
	for (int i = 0; i < P; ++i) {

		int *a = &(automata[i]);
		int *ia = &(inv_automata[i * N]);
		int *iap = &(inv_automata_ptrs[i * (N + 1)]);

		memset(iap, 0, sizeof(int) * (N + 1));
		for (int j = 0; j < N; j++) { iap[a[j * P] + 1]++; }
		for (int j = 1; j <= N; j++) { iap[j] += iap[j - 1]; }
		for (int j = 0; j < N; j++) { ia[iap[a[j * P]]++] = j; }
		for (int j = N; j > 0; j--) { iap[j] = iap[j - 1]; } iap[0] = 0;
	}

	checkInverse(automata, inv_automata_ptrs, inv_automata, N, P);

#ifdef DEBUG
	printInverseAutomata(inv_automata_ptrs, inv_automata, N, P);
#endif

	PNode *path;
	//sequential version
	if (true) {
		//out << "sequential:" << endl;
		path = NULL;
		greedyHeuristic_naive(automata, inv_automata_ptrs, inv_automata, N, P, path, weights);

		out << "SynchroP ";
		pathPrinter(automata, path, N, P, weights);
		if (applyPath(automata, path, N, P) != 1)
		{
			out << "No of reaminig active states is not 1" << endl;
		}
		out << endl;

		path = NULL;
		greedyHeuristic_naive_weighted(automata, inv_automata_ptrs, inv_automata, N, P, path, weights);

		out << "SynchroP Weighted ";
		pathPrinter(automata, path, N, P, weights);
		if (applyPath(automata, path, N, P) != 1)
		{
			out << "No of reaminig active states is not 1" << endl;
		}
		out << endl;
	}

#ifdef DEBUGA
	out << "Weights ----------------------" << endl;
	for (int i = 0; i < P; ++i) {
		out << weights[i] << " ";
		}
	out << endl << endl;
	printAutomata(automata, N, P, weights);
#endif

#ifdef DEBUG2
	PNode* sPath = NULL;
	shortestPath(automata, N, P, sPath, weights);
#endif

#ifdef LOG_LEVEL
	out << endl;
	out.close();
#endif

	free(automata);
	free(weights);
	free(inv_automata_ptrs);
	free(inv_automata);

	return 0;
}
