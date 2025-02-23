#include <iostream>
#include <fstream>
#include <cmath>
#include "stdlib.h"
#include "stdio.h"
#include <string>
#include "string.h"
#include "omp.h"
#include <sys/types.h>
#include <sys/stat.h>
#include <climits>
//#include <unistd.h>
#include <queue>

#define TIMER
#define DEBUGA
//#define DEBUG
//#define DEBUG2
#ifdef TIMER
#define TIME_ANALYSIS 1 //#define TIMER macro is required for time analysis
#endif
#define DATA_ANALYSIS 2
//#define LOG_LEVEL TIME_ANALYSIS
using namespace std;

#ifdef LOG_LEVEL
ofstream out;
#endif

#define Id(s1, s2) ((s1 > s2)?(((s1 * (s1 + 1))/2) + s2):(((s2 * (s2 + 1))/2) + s1)) //this is how we compute the ids
#define IdNaive(s1, s2, N) ((s1 > s2)?((s1 * N) + s2):((s2 * N) + s1)) //this is how we compute the ids
#define s1fromId(id) ((int)(sqrt((2.0 * id) +1.0) - 0.5));
#define s2fromId(id, s1) (id - ((s1 * (s1 + 1))/2));

ofstream out;

struct PNode {
	int letter;
	PNode* next;
	PNode(int _letter, PNode* _next) : letter(_letter), next(_next) {}
};

template <typename T>
struct DistID { //ege: to store pairs with their distances in min heap
	T id;
	T dist;
	T label;
	DistID(T i, T d, T l) : id(i), dist(d), label(l) {}

	bool operator<(const DistID& rhs) const {
		if (dist > rhs.dist)
			return true;
		else if (dist < rhs.dist)
			return false;
		else {
			if (label > rhs.label)
				return true;
			else
				return false;
		}//return dist > rhs.dist;
	}
};

template<bool memoryOpt>
void synchronizing_check(int* a, int N, int P, int* distance) { //ege
	int* levels = new int[200];
	memset(levels, 0, 200 * sizeof(int));

	for (int i = 0; i < N; ++i) {
		for (int j = 0; j <= i; ++j) {
			int id;
			if (memoryOpt)
				id = Id(i, j);
			else
				id = IdNaive(i, j, N);

			if (distance[id] == -1) {
				for (int p = 0; p < P; p++) {
					int ts1 = a[p + i * P];
					int ts2 = a[p + j * P];
					int tid;
					if (memoryOpt)
						tid = Id(ts1, ts2);
					else
						tid = IdNaive(ts1, ts2, N);
					//out << "tid " << tid << ": distance is " << distance[tid] << endl;
				}

				out << "automata is not synchronizing. pair " << id << " - (" << i << ", " << j << ") is not mergable\n";
				out << endl;
				exit(0);
				return;
			}
			else {
				levels[distance[id]]++;
			}
		}
	}

#ifdef DEBUG
	int lvl = 0;
	while (levels[lvl] > 0) {
		out << "lvl " << lvl++ << ": " << levels[lvl] << endl;
	}
	out << endl;
#endif

#if LOG_LEVEL & DATA_ANALYSIS
	out << levels[1];
	lvl = 2;
	while (levels[lvl] > 0) {
		out << "-" << levels[lvl++];
	}
#endif
	free(levels);
}

//////////////////////////////////

string alternative_seq = "";
int alternativeCounter = 1;

vector<string> combiantionGenerator(vector<string> inputs, int level) {
	int i = 0;
	vector<string> combinations;
	while (i < level) {
		if (combinations.size() == 0) {
			for (int j = 0; j < inputs.size(); j++) {
				combinations.push_back(inputs[j]);
			}
		}
		else {
			vector<string> levelCombs;

			for (int j = 0; j < combinations.size(); j++) {
				for (int k = 0; k < inputs.size(); k++) {
					string newComb = combinations[j];
					newComb.append(inputs[k]);
					levelCombs.push_back(newComb);
				}
			}

			for (int l = 0; l < levelCombs.size(); l++) {
				bool foundIn = false;
				for (int n = 0; n < combinations.size(); n++) {
					if (combinations[n] == levelCombs[l]) {
						foundIn = true;
					}
				}

				if (foundIn == false) {
					combinations.push_back(levelCombs[l]);
				}
			}
		}

		i++;

	}

	return combinations;

}

int trackSequence(int transitions[], string combination, int* activeStates, int totalStateNo, int activesSize) {
	vector<int> flagVector(totalStateNo, 0); // Flag vector initially all set to zero, to see if there are any states merging
	int* trackedStates = new int[activesSize]; // Dynamic array to keep tracked states, set equal to activeStates at the end
	int numTracked = 0; // To keep the info of where to add in the trackedStates array and to keep the number of relevant items in trackedStates array

	// For each active state
	for (int i = 0; i < activesSize; i++) {
		int currentState = activeStates[i];

		// Track the state through the combination
		for (int l = 0; l < combination.length(); l++) {
			int inputPlace = combination[l] - '0';
			int trackedLocation = (inputPlace * totalStateNo) + currentState;
			currentState = transitions[trackedLocation];
		}

		// If state has not been seen before in the tracking process
		// It is still set to 0 in the flagVector
		// In this case change it to 1, add it to the array of trackedStates and increase the number of states tracked
		if (flagVector[currentState] == 0) {
			flagVector[currentState] = 1;
			trackedStates[numTracked] = currentState;
			numTracked++;
		}
	}

	for (int j = 0; j < numTracked; j++) {
		activeStates[j] = trackedStates[j];
	}

	trackedStates = NULL;
	delete[] trackedStates;

	return numTracked;
}


string alternativeGreedy(int N, int* actives, int& no_actives, int level, int transitions[], vector<string>& combinations, int tempActives[], int& alternativeCounter) {

	alternativeCounter = 1;
	int notFound = alternativeCounter;
	string sequence = "";
	int currentLevel = 0;
	//int* tempActives = new int[no_actives];

	while (currentLevel < level && sequence == "") {
		for (int i = 0; i < combinations.size(); i++) {
			for (int l = 0; l < no_actives; l++) {
				tempActives[l] = actives[l];
			}
			int tempActivesSize = no_actives;

			if (combinations[i].length() == currentLevel + 1) {
				tempActivesSize = trackSequence(transitions, combinations[i], tempActives, N, tempActivesSize);

				if (tempActivesSize < no_actives) {
					sequence = combinations[i];

					no_actives = tempActivesSize;

					for (int j = 0; j < tempActivesSize; j++) {
						actives[j] = tempActives[j];
					}

					break;
				}
				else
				{
					notFound++;
				}
			}
		}
		currentLevel++;
	}

	//cout << "Inside: " << no_actives << endl;

  //tempActives = NULL;
  //delete[] tempActives;

	//if (sequence != "") {
		//cout << "Total number of iterations counted by alternative greedy at this step: " << notFound << "\n";
	//}

	alternativeCounter = notFound;

	return sequence;

}


/////////////////////////////
void insertToPath(int letter, PNode*& head, PNode*& last) {
	PNode* temp = new PNode(letter, NULL);
	if (head == NULL) {
		head = last = temp;
	}
	else {
		last = last->next = temp;
	}
}

void printAutomata(int* automata, int N, int p, int* w) {
	out << "Automata ----------------------" << endl;
	for (int i = 0; i < p; ++i) {
		out << "letter " << (char)(i + 97) << " (" << w[i] << "):\t";
		for (int j = 0; j < N; ++j) {
			out << automata[i * N + j] << "," << w[i] << "\t";
		}
		out << endl;
	}
}

void printInverseAutomata(int* inv_automata_ptrs, int* inv_automata, int N, int p) {
	out << "Inverse Automata --------------" << endl;
	for (int i = 0; i < p; ++i) {
		out << "letter " << (char)(i + 97) << ":\n";
		for (int j = 0; j <= N; ++j) {
			out << inv_automata_ptrs[i * (N + 1) + j] << "\t";
		}
		out << endl;
		for (int j = 0; j < N; ++j) {
			out << inv_automata[i * N + j] << "\t";
		}
		out << endl << endl;
	}
}

void greedyHeuristic_naive(int* a, int* iap, int* ia, int N, int P, PNode*& path, int* w) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = -1;
	}

	//BFS queue for the pairs
	int qs = 0;
	int qe = 0;

	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que[qe++] = id;
	}

	//there are more nodes in the queue
	while (qs < qe && qe < noOfPair) {
		int q_id = que[qs++];
		int q_dist = distance[q_id];

		//will process the pair with id q_id now
		int q_s1 = s1fromId(q_id); //the first state in the pair
		int q_s2 = s2fromId(q_id, q_s1); //the second state in the pair (we are sure that q_s1 >= q_s2)

#ifdef DEBUG
		out << "will process " << q_s1 << " " << q_s2 << " with id  " << q_id << " with distance " << q_dist << endl;
#endif

		for (int p = 0; p < P; p++) {
			int* p_ia = &ia[p * N]; //this is the inverse automata for letter p
			int* p_iap = &iap[p * (N + 1)]; //and its state pointers
			int iap_s1_limit = p_iap[q_s1 + 1];
			int iap_s2_limit = p_iap[q_s2 + 1];

			if (p_iap[q_s2] == iap_s2_limit) continue;

			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < iap_s1_limit; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < iap_s2_limit; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];
					int ia_id = Id(ia_s1, ia_s2);

					if (distance[ia_id] < 0) { //we found an unvisited pair. so we need to add this to the queue
						distance[ia_id] = q_dist + 1;
						next[ia_id] = q_id;
						letter[ia_id] = p;
						que[qe++] = ia_id;
					}
				}
			}
		}
	}
#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "BFS tree generation takes " << time << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif

	int* levels = new int[200];
	memset(levels, 0, 200 * sizeof(int));

	for (int i = 0; i < N; ++i) {
		for (int j = 0; j <= i; ++j) {
			int id = Id(i, j);

			if (distance[id] == -1) {
				for (int p = 0; p < P; p++) {
					int ts1 = a[p * N + i];
					int ts2 = a[p * N + j];

					int tid = Id(ts1, ts2);
					//out << "tid " <<  tid << ": distance is " << distance[tid] << endl;
				}

				out << "automata is not synchronizing. pair " << id << " - (" << i << ", " << j << ") is not mergable\n";
				exit(1);
			}
			else {
				levels[distance[id]]++;
			}
		}
	}

#ifdef DEBUG
	int lvl = 0;
	while (levels[lvl] > 0) {
		out << "lvl " << lvl++ << ": " << levels[lvl] << endl;
	}
	out << endl;
#endif

#if LOG_LEVEL == DATA_ANALYSIS
	out << levels[1];
	lvl = 2;
	while (levels[lvl] > 0) {
		out << "-" << levels[lvl++];
	}
#endif

#ifdef TIMER
	t1 = omp_get_wtime();
#endif

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	/////////////DEFINE LEVEL/////////
	int level = 2;
	/////////////DEFINE LEVEL/////////



	vector<string> inputs;

	for (int k = 0; k < P; k++) {
		inputs.push_back(to_string(k));
	}

	vector<string> combinations = combiantionGenerator(inputs, level);

	int globalCounter = 0;
	int notFound = 0;

	int step = 1;
	vector<int> remActives;
	vector<string> syncSubseq;
	vector<int> weightSubseq;
	remActives.push_back(no_actives);
	int* tempActives = new int[no_actives];

	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance

		////////////////////////////////////////////////////////////////////////

		alternative_seq = alternativeGreedy(N, actives, no_actives, level, a, combinations, tempActives, alternativeCounter);

		if (alternative_seq == "")
		{
      globalCounter = globalCounter + alternativeCounter-1;
			notFound++;
			//cout << "No Path found!" << endl;
		}
		else
		{
			syncSubseq.push_back(alternative_seq);
			//cout << "Chunk found: " << alternative_seq << endl;
			//cout << no_actives << endl;
			globalCounter = globalCounter + alternativeCounter;

				//apply the path and store it for alternative greedy

				for (int i = 0; i < alternative_seq.length(); i++) {
					insertToPath(alternative_seq[i] - '0', path, last);
				}



			continue;

		}
		////////////////////////////////////////////////////////////////////////

		int min_distance = N * N;
		int min_id;
		int countPairs = 0;
		for (int i = 0; i < no_actives; i++) {
			for (int j = 0; j < i; j++) {
				int s1 = actives[i];
				int s2 = actives[j];

				int id = Id(s1, s2);

				//++
				countPairs++;


				if (min_distance > distance[id]) {
					min_distance = distance[id];
					min_id = id;
					if (min_distance == level+1) break;
				}
			}
			if (min_distance == level+1) break;
		}


		//cout << "Total number of pairs counted by naive greedy at this step: " << countPairs << "\n";
		globalCounter = globalCounter + countPairs;


#if LOG_LEVEL == DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif
		// out << "merging pair from level " << min_distance << endl;

		//apply the path and store it
		int pid = min_id;
		string s = "";
		int we = 0;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
			s += char(let)+97; //+97
			we += w[let];
		}

		syncSubseq.push_back(s);
		weightSubseq.push_back(we);

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
		remActives.push_back(no_actives);

	}

  out << "Alternative Greedy test level: " << level<<"\n";
	out << "Alternative Greedy could not find a sequence: " << notFound << " times\n";
	out << "Total number of iterations for globalCounter: " << globalCounter << " times\n";


	tempActives = NULL;
	delete[] tempActives;

	for (int i = 0; i < remActives.size(); i++) {
		out << remActives[i] << " ";
	}
	out << endl << step << endl;
	for (int i = 0; i < syncSubseq.size(); i++) {
		out << syncSubseq[i] << " ";
	}
	out << endl;
	for (int i = 0; i < weightSubseq.size(); i++) {
		out << weightSubseq[i] << " ";
	}
	out << endl;


#ifdef TIMER
	time = omp_get_wtime() - t1;
	out << "Path generation takes " << time << " seconds\n";
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	out << "," << (N * (N - 1)) / 2 << "," << lvl - 1 << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter;
#endif
	free(distance);
	free(next);
	free(letter);
	free(que);
	free(actives);
	free(active_marker);
}

//a is automata a[i][j] -> state j goes to a[i][j] with letter j
//iap is inverse automata pointers -> ia[i][iap[i][j] ... ia[i][j+1]] keeps the state ids which go to state j with letter i
//there are N states and p letters in the automata
void greedyHeuristic_naive_weighted(int* a, int* iap, int* ia, int N, int P, PNode*& path, int* w) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	priority_queue< DistID<int> > que; //ege: min heap for the weighted tree
	/*int * orderedInputs = new int[P];
	int * tempw = new int[P];

	for(int i = 0; i <P; i++) tempw[i] = w[i];

	for(int x = 0; x < P; x++)
	{
		int order;
		int min_weight = INT_MAX;
		for(int i = 0; i < P; i++)
		{
			if(tempw[i] < min_weight)
			{
				min_weight = tempw[i];
				order = i;
			}
		}

		orderedInputs[x] = order;
		tempw[order] = INT_MAX;
	}

	delete [] tempw;	*/

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = INT_MAX;
	}

	//dijkstra queue for the pairs
	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que.push(DistID<int>(id, distance[id], i)); //ege
	}

	//there are more nodes in the queue
	int counter = 0;
	while (!que.empty()) {
		int q_id = (que.top()).id; //ege
		que.pop();
		int q_dist = distance[q_id];

		//will process the pair with id q_id now
		int q_s1 = s1fromId(q_id); //the first state in the pair
		int q_s2 = s2fromId(q_id, q_s1); //the second state in the pair (we are sure that q_s1 >= q_s2)

#ifdef DEBUG
		out << "will process " << q_s1 << " " << q_s2 << " with id  " << q_id << " with distance " << q_dist << endl;
#endif
		for (int p = 0; p < P; p++) {
			//int p = orderedInputs[i];
			int* p_ia = ia + p * N; //this is the inverse automata for letter p
			int* p_iap = iap + p * (N + 1); //and its state pointers
			int iap_s1_limit = p_iap[q_s1 + 1];
			int iap_s2_limit = p_iap[q_s2 + 1];

			if (p_iap[q_s2] == iap_s2_limit) continue;

			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < iap_s1_limit; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < iap_s2_limit; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];
					int ia_id = Id(ia_s1, ia_s2);

					if (distance[ia_id] > q_dist + w[p]) { //berk: key change
						distance[ia_id] = q_dist + w[p];
						next[ia_id] = q_id;
						letter[ia_id] = p;
						que.push(DistID<int>(ia_id, distance[ia_id], counter++));
					}
				}
			}
		}
	}
#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "Dijsktra tree generation takes " << time << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif

	/*#ifdef DEBUG
		int lvl = 0;
		while (levels[lvl] > 0) {
			out << "lvl " << lvl++ << ": " << levels[lvl] << endl;
		}
		out << endl;
	#endif*/

#if LOG_LEVEL == DATA_ANALYSIS
	out << levels[1];
	lvl = 2;
	while (levels[lvl] > 0) {
		out << "-" << levels[lvl++];
	}
#endif

#ifdef TIMER
	t1 = omp_get_wtime();
#endif

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	vector<int> remActives;
	vector<string> syncSubseq;
	vector<int> weightSubseq;
	remActives.push_back(no_actives);
	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance
		int min_distance = INT_MAX;
		int min_id;
		for (int i = 0; i < no_actives; i++) {
			for (int j = 0; j < i; j++) {
				int s1 = actives[i];
				int s2 = actives[j];

				int id = Id(s1, s2);

				if (min_distance > distance[id]) {
					min_distance = distance[id];
					min_id = id;
					if (min_distance == 1) break;
				}
			}
			if (min_distance == 1) break;
		}

#if LOG_LEVEL == DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif
		// out << "merging pair from level " << min_distance << endl;

		//apply the path and store it
		int pid = min_id;
		string s = "";
		int we = 0;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
			s += char(let) + 97;
			we += w[let];
		}

		syncSubseq.push_back(s);
		weightSubseq.push_back(we);

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
		remActives.push_back(no_actives);
	}

	for (int i = 0; i < remActives.size(); i++) {
		out << remActives[i] << " ";
	}
	out << endl << step << endl;
	for (int i = 0; i < syncSubseq.size(); i++) {
		out << syncSubseq[i] << " ";
	}
	out << endl;
	for (int i = 0; i < weightSubseq.size(); i++) {
		out << weightSubseq[i] << " ";
	}
	out << endl;


#ifdef TIMER
	time = omp_get_wtime() - t1;
	out << "Path generation takes " << time << " seconds\n";
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	out << "," << (N * (N - 1)) / 2 << "," << lvl - 1 << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter;
#endif
	free(distance);
	free(next);
	free(letter);
	free(actives);
	free(active_marker);
}

void shortestPath(int* a, int N, int P, PNode*& path, int* w) {
	unsigned long long int noOfNodes = pow(2.0, double(N));
	unsigned long long int* distance = new unsigned long long int[noOfNodes];
	unsigned long long int* prev = new unsigned long long int[noOfNodes];
	unsigned long long int* letter = new unsigned long long int[noOfNodes];
	priority_queue< DistID<unsigned long long int> > que; //ege: min heap for the weighted tree
	/*unsigned long long int * orderedInputs = new unsigned long long int[P];
	unsigned long long int * tempw = new unsigned long long int[P];

	for(unsigned long long int i = 0; i <P; i++) tempw[i] = w[i];

	for(unsigned long long int x = 0; x < P; x++)
	{
		unsigned long long int order;
		unsigned long long int min_weight = ULLONG_MAX;
		for(int i = 0; i < P; i++)
		{
			if(tempw[i] < min_weight)
			{
				min_weight = tempw[i];
				order = i;
			}
		}

		orderedInputs[x] = order;
		tempw[order] = ULLONG_MAX;
	}

	delete [] tempw;*/

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (unsigned long long int i = 0; i < noOfNodes; i++) {
		distance[i] = ULLONG_MAX;
	}

	//dijkstra queue for the pairs
	distance[noOfNodes - 1] = 0;
	prev[noOfNodes - 1] = noOfNodes - 1;
	que.push(DistID<unsigned long long int>(noOfNodes - 1, 0, 0));

	unsigned long long int* q_sN = new unsigned long long int[N];
	unsigned long long int* nextState = new unsigned long long int[N];
	//there are more nodes in the queue
	unsigned long long int counter = 1;
	while (!que.empty()) {
		unsigned long long int q_id = (que.top()).id; //ege
		if (q_id < 0) out << q_id << endl;
		que.pop();
		unsigned long long int q_dist = distance[q_id];
		unsigned long long int temp_q_id = q_id;
		//int bin_id = 0;

		//will process the pair with id q_id now
		for (unsigned long long int i = 0; i < N; i++)
		{
			q_sN[i] = temp_q_id % 2;
			temp_q_id = temp_q_id >> 1;
			//if(q_sN[i] != 0)
			//	bin_id += pow(10,N-i-1);
		}
#ifdef DEBUG
		//out << "will process\t" << bin_id << "\twith id\t" << q_id << "\twith distance\t" << q_dist << endl;
#endif
		for (unsigned long long int p = 0; p < P; p++) {
			//unsigned long long int p = orderedInputs[j];
			memset(nextState, 0, sizeof(unsigned long long int) * N);

			for (unsigned long long int i = 0; i < N; i++)
			{
				if (q_sN[i] != 0)
				{
					nextState[a[p * N + i]] = 1;
				}

			}
			unsigned long long int id = 0;
			for (unsigned long long int i = 0; i < N; i++)
			{
				if (nextState[i] == 1)
				{
					id += (1 << i);
				}
			}

			if (distance[id] > q_dist + w[p]) //berk: key change
			{
				distance[id] = q_dist + w[p];
				prev[id] = q_id;
				letter[id] = p;
				que.push(DistID<unsigned long long int>(id, distance[id], counter++));
			}
		}
	}

	delete[] q_sN;
	delete[] nextState;

	unsigned long long int mindist = ULLONG_MAX;
	unsigned long long int minid;
	for (unsigned long long int i = 0; i < N; i++) {
		unsigned long long int pw = pow(2, i);
		if (distance[pw] < mindist) {
			mindist = distance[pw];
			minid = pw;
		}
	}

	unsigned long long int weight = 0;
	unsigned long long int length = 0;
	unsigned long long int s = minid;
	unsigned long long int limit = pow(2, N) - 1;
	vector<char> seq;
	while (s < limit) {
		unsigned long long int p = letter[s];
		seq.push_back(char(p + 97));
		s = prev[s];
		weight += w[p];
		length++;
	}

	out << "Shortest Path: ";
	for (unsigned long long int i = seq.size() - 1; i >= 0; i--) {
		out << seq[i] << " ";
	}
	out << endl << "Shortest Path Length:" << length << endl;
	out << "Shortest Path Weight:" << weight << endl; //todo: insert to path
}
/*
#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "BFS tree generation takes " << time << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif

	synchronizing_check<true>(a, N, P, distance);

	int* levels = new int[200];
	memset(levels, 0, 200 * sizeof(int));

	for (int i = 0; i < N; ++i) {
		for (int j = 0; j <= i; ++j) {
			int id = Id(i, j);

			if (distance[id] == -1) {
				for (int p = 0; p < P; p++) {
					int ts1 = a[p * N + i];
					int ts2 = a[p * N + j];

					int tid = Id(ts1, ts2);
					out << "tid " <<  tid << ": distance is " << distance[tid] << endl;
				}

				out << "automata is not synchronizing. pair " << id << " - (" << i << ", " << j << ") is not mergable\n";
				exit(1);
			} else {
				levels[distance[id]]++;
			}
		}
	}

#ifdef DEBUG
	int lvl = 0;
	while (levels[lvl] > 0) {
		out << "lvl " << lvl++ << ": " << levels[lvl] << endl;
	}
	out << endl;
#endif

#if LOG_LEVEL == DATA_ANALYSIS
	out << levels[1];
	lvl = 2;
	while (levels[lvl] > 0) {
		out << "-" << levels[lvl++];
	}
#endif

#ifdef TIMER
	t1 = omp_get_wtime();
#endif

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance
		int min_distance = N * N * 20; //ege: worst case cost for initialization
		int min_id;
		for (int i = 0; i < no_actives; i++) {
			for (int j = 0; j < i; j++) {
				int s1 = actives[i];
				int s2 = actives[j];

				int id = Id(s1, s2);

				if (min_distance > distance[id]) {
					min_distance = distance[id];
					min_id = id;
					if (min_distance == 1) break;
				}
			}
			if (min_distance == 1) break;
		}

#if LOG_LEVEL == DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif
		// out << "merging pair from level " << min_distance << endl;

		//apply the path and store it
		int pid = min_id;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
		}

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
	}


#ifdef TIMER
	time = omp_get_wtime() - t1;
//out << "Path generation takes " << time << " seconds\n";
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	out << "," << (N * (N - 1 )) / 2 << "," << lvl - 1 << ","
		<< max_of_min_distances  << "," << float(min_distance_sum) / min_distance_counter;
#endif
	free(distance);
	free(next);
	free(letter);
	free(actives);
	free(active_marker);

}
*/
int processUntilActive(int* iap, int* ia, int N, int P,
	int* que, int* distance, int* next, int* letter, int& qs, int& qe,
	int* active_marker, int marker) {
	int noOfPair = (N * (N + 1)) / 2;

	while (qs < qe && qe < noOfPair) {
		int q_id = que[qs++];
		int q_dist = distance[q_id];

		//will process the pair with id q_id now
		int q_s1 = s1fromId(q_id); //the first state in the pair
		int q_s2 = s2fromId(q_id, q_s1); //the second state in the pair (we are sure that q_s1 >= q_s2)
#ifdef DEBUG
		out << "will process " << q_s1 << " " << q_s2 << " with id  " << q_id << " with distance " << q_dist << " " << qs << " " << qe << endl;
#endif

		int found = -1;
		for (int p = 0; p < P; p++) {
			int* p_ia = &ia[p * N]; //this is the inverse automata for letter p
			int* p_iap = &iap[p * (N + 1)]; //and its state pointers

			int iap_s1_limit = p_iap[q_s1 + 1];
			int iap_s2_limit = p_iap[q_s2 + 1];

			if (p_iap[q_s2] == iap_s2_limit) continue;

			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < iap_s1_limit; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < iap_s2_limit; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];

					int ia_id = Id(ia_s1, ia_s2);

					if (distance[ia_id] < 0) { //we found an unvisited pair. so we need to add this to the queue
						distance[ia_id] = q_dist + 1;
						next[ia_id] = q_id;
						letter[ia_id] = p;
						que[qe++] = ia_id;

						if (found == -1 && active_marker[ia_s1] == marker && active_marker[ia_s2] == marker) {
							found = ia_id;
						}
					}
				}
			}
		}
		if (found != -1) {
			return found;
		}
	}
	return -1;
}

int processUntilActive_economic(int* iap, int* ia, int N, int P,
	/*int* que*/ queue<int>& que, int* distance, int* next, int* letter/*, int& qs*/, int& qe,
	int* active_marker, int marker) {
	int noOfPair = (N * (N + 1)) / 2;
	while (/*qs < qe*/ !que.empty() && qe < noOfPair) {
		//int q_id = que[qs++];
		int q_id = que.front();
		que.pop();
		int q_dist = distance[q_id];

		//will process the pair with id q_id now
		int q_s1 = s1fromId(q_id); //the first state in the pair
		int q_s2 = s2fromId(q_id, q_s1); //the second state in the pair (we are sure that q_s1 >= q_s2)
#ifdef DEBUG
		out << "will process " << q_s1 << " " << q_s2 << " with id  " << q_id << " with distance " << q_dist << endl;
#endif

		int found = -1;
		for (int p = 0; p < P; p++) {
			int* p_ia = &ia[p * N]; //this is the inverse automata for letter p
			int* p_iap = &iap[p * (N + 1)]; //and its state pointers

			int iap_s1_limit = p_iap[q_s1 + 1];
			int iap_s2_limit = p_iap[q_s2 + 1];

			if (p_iap[q_s2] == iap_s2_limit) continue;

			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < iap_s1_limit; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < iap_s2_limit; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];

					int ia_id = Id(ia_s1, ia_s2);

					if (distance[ia_id] < 0) { //we found an unvisited pair. so we need to add this to the queue
						distance[ia_id] = q_dist + 1;
						next[ia_id] = q_id;
						letter[ia_id] = p;
						//que[qe++] = ia_id;
						qe++;
						que.push(ia_id);

						if (found == -1 && active_marker[ia_s1] == marker && active_marker[ia_s2] == marker) {
							found = ia_id;
						}
					}
				}
			}
		}
		if (found != -1) {
			return found;
		}
	}
	return -1;
}


void greedyHeuristic_economic(int* a, int* iap, int* ia, int N, int P, PNode*& path) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];
	//queue<int> que;

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = -1;
	}

	//BFS queue for the pairs
	int qs = 0;
	int qe = 0;

	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que[qe++] = id;
		//que.push(id);
		qe++;
	}

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance
		int min_distance = N * N;
		int min_id = -1;
		if (no_actives < N) {
			for (int i = 0; i < no_actives; i++) {
				for (int j = 0; j < i; j++) {
					int s1 = actives[i];
					int s2 = actives[j];

					int id = Id(s1, s2);

					if (distance[id] != -1 && min_distance > distance[id]) {
						min_distance = distance[id];
						min_id = id;
						if (min_distance == 1) break;
					}
				}
				if (min_distance == 1) break;

			}
		}

		if (min_id == -1) {
			min_id = processUntilActive(iap, ia, N, P, que, distance, next, letter, qs, qe, active_marker, step - 1);

			if (min_id == -1) {
				out << "automata is not synchronizing " << endl;
				exit(1);
			}
		}

#if LOG_LEVEL == DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif
		//apply the path and store it
		int pid = min_id;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
		}

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
	}

#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	qe--;
	int firstOut = queue.back();
	out << qe - N << "," << /*distance[que[qe]]*/ distance[firstOut] << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter;
#endif
	delete[] distance;
	delete[] next;
	delete[] letter;
	//free(que);
	delete[] actives;
	delete[] active_marker;
}

void greedyHeuristic_economic_lookahead(int* a, int* iap, int* ia, int N, int P, PNode*& path) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = -1;
	}

	//BFS queue for the pairs
	int qs = 0;
	int qe = 0;

	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que[qe++] = id;
	}

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance
		int min_distance = N * N;
		int min_id = -1;
		if (no_actives < N) {
			for (int i = 0; i < no_actives; i++) {
				for (int j = 0; j < i; j++) {
					int s1 = actives[i];
					int s2 = actives[j];

					int id = Id(s1, s2);

					if (distance[id] != -1 && min_distance > distance[id]) {
						min_distance = distance[id];
						min_id = id;
						if (min_distance == 1) break;
					}
				}
				if (min_distance == 1) break;
			}
		}

		if (min_id == -1) {
			int min_p = -1;
			//time with and without this and report
			int early_exit_distance = distance[que[qs]];
			for (int i = 0; i < no_actives && min_distance != early_exit_distance; i++) {
				for (int j = 0; j < i && min_distance != early_exit_distance; j++) {
					int s1 = actives[i];
					int s2 = actives[j];
					for (int p = 0; p < P; p++) {
						int* ap = &a[p * N];
						int ts1 = ap[s1];
						int ts2 = ap[s2];

						int tid = Id(ts1, ts2);
						if (distance[tid] != -1 && distance[tid] < min_distance) {
							min_id = tid;
							min_distance = distance[tid];
							min_p = p;

							if (min_distance == early_exit_distance) {
								break;
							}
						}
					}
				}
			}

			if (min_id != -1) {
				int* ap = &a[min_p * N];
				for (int k = 0; k < no_actives; k++) {
					actives[k] = ap[actives[k]];
				}
				insertToPath(min_p, path, last);
			}
		}

		if (min_id == -1) {
			min_id = processUntilActive(iap, ia, N, P, que, distance, next, letter, qs, qe, active_marker, step - 1);

			if (min_id == -1) {
				out << "automata is not synchronizing " << endl;
				exit(1);
			}
		}
#if LOG_LEVEL == DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif

		//apply the path and store it
		int pid = min_id;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
		}

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
	}


#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif

#if LOG_LEVEL == DATA_ANALYSIS
	qe--;
	out << qe - N << "," << distance[que[qe]] << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter;
#endif

	free(distance);
	free(next);
	free(letter);
	free(que);
	free(actives);
	free(active_marker);
}

int recursivePathGrow(int* actives, int no_actives, int* a, int* lookahead_parent, int* lookahead_path, int id, PNode*& path, PNode*& last, int N) {
	int parent = lookahead_parent[id];
	if (parent == -1) {
		return 0;
	}
	int retVal = recursivePathGrow(actives, no_actives, a, lookahead_parent, lookahead_path, parent, path, last, N);

	int p = lookahead_path[id];

	int* ap = &a[p * N];
	for (int k = 0; k < no_actives; k++) {
		actives[k] = ap[actives[k]];
	}
	insertToPath(p, path, last);
	return retVal + 1;
}

void greedyHeuristic_economic_lookahead_further(int* a, int* iap, int* ia, int N, int P, PNode*& path, int max_state, int max_lookahead_count) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];

	int* lookahead_queue = new int[noOfPair];
	int* lookahead_marker = new int[noOfPair];
	int* lookahead_path = new int[noOfPair];
	int* lookahead_parent = new int[noOfPair];
	int  lookahead_length = 0;

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
	int lookahead_counter = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = lookahead_marker[i] = -1;
	}

	//BFS queue for the pairs
	int qs = 0;
	int qe = 0;

	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que[qe++] = id;
	}

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	while (no_actives > 1) {
		int lqe = 0;
		/*		out << "no active states is " << no_actives << endl;
		if(no_actives < 10) {
		  for(int i = 0; i < no_actives; i++) {
			out << actives[i] << " ";
		  }
		  out << "\n";
		  }*/
		  //find the pair id with minimum distance
		int min_distance = N * N;
		int min_id = -1;
		if (no_actives < N) {
			if (no_actives > max_state) {
				for (int i = 0; i < no_actives; i++) {
					for (int j = 0; j < i; j++) {
						int s1 = actives[i];
						int s2 = actives[j];

						int id = Id(s1, s2);

						if (distance[id] != -1 && min_distance > distance[id]) {
							min_distance = distance[id];
							min_id = id;
							if (min_distance == 1) break;
						}
					}
					if (min_distance == 1) break;
				}
			}
			else {
				for (int i = 0; i < no_actives; i++) {
					for (int j = 0; j < i; j++) {
						int s1 = actives[i];
						int s2 = actives[j];

						int id = Id(s1, s2);

						if (distance[id] != -1 && min_distance > distance[id]) {
							min_distance = distance[id];
							min_id = id;
							if (min_distance == 1) break;
						}

						lookahead_marker[id] = step;
						lookahead_parent[id] = -1;
						lookahead_queue[lqe++] = id;
					}
					if (min_distance == 1) break;
				}
			}

			if (min_id == -1 && (no_actives <= max_state)) {
				int lqs = 0;
				int end_level = lqe;
				while (lqs < end_level) {
#if LOG_LEVEL == DATA_ANALYSIS
					lookahead_counter++;
#endif
					int l_id = lookahead_queue[lqs++];

					int l_s1 = s1fromId(l_id);
					int l_s2 = s2fromId(l_id, l_s1);

					for (int p = 0; p < P; p++) {
						int* ap = &a[p * N];
						int ts1 = ap[l_s1];
						int ts2 = ap[l_s2];

						int tid = Id(ts1, ts2);
						if (distance[tid] != -1 && distance[tid] < min_distance) { //there is a path from an active pair to one in the queue
							min_distance = distance[tid];
							lookahead_path[tid] = p;
							lookahead_parent[tid] = l_id;
							min_id = tid;
						}
						else if (lookahead_marker[tid] != step) {
							lookahead_queue[lqe++] = tid;
							lookahead_parent[tid] = l_id;
							lookahead_marker[tid] = step;
							lookahead_path[tid] = p;
						}
					}

					if (lqs == end_level && end_level < max_lookahead_count && min_id == -1) {
						end_level = lqe;
					}
				}

				if (min_id != -1) {
					lookahead_length = recursivePathGrow(actives, no_actives, a, lookahead_parent, lookahead_path, min_id, path, last, N);
				}
				else
					lookahead_length = 0;
			}
		}

		if (min_id == -1) {
			min_id = processUntilActive(iap, ia, N, P, que, distance, next, letter, qs, qe, active_marker, step - 1);

			if (min_id == -1) {
				out << "automata is not synchronizing " << endl;
				exit(1);
			}
		}

#if LOG_LEVEL == DATA_ANALYSIS
		int distance_id = distance[min_id] + lookahead_length;
		if (max_of_min_distances < distance_id)
			max_of_min_distances = distance_id;
		min_distance_counter++;
		min_distance_sum += distance_id;
#endif

		//apply the path and store it
		int pid = min_id;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
		}

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
	}


#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif

#if LOG_LEVEL == DATA_ANALYSIS
	qe--;
	out << qe - N << "," << distance[que[qe]] << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter << "," << lookahead_counter << ",";
#endif

	free(distance);
	free(next);
	free(letter);
	free(que);
	free(actives);
	free(active_marker);
	free(lookahead_queue);
}

void greedyHeuristic_economic_lookahead_further_smart(int* a, int* iap, int* ia, int N, int P, PNode*& path, int max_state, int max_lookahead_count) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfPair];
	int* next = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];

	int* lookahead_queue = new int[noOfPair];
	int* lookahead_marker = new int[noOfPair];
	int* lookahead_path = new int[noOfPair];
	int* lookahead_parent = new int[noOfPair];
	int  lookahead_length = 0;

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
	int lookahead_counter = 0;
#endif

	for (int i = 0; i < noOfPair; i++) {
		distance[i] = lookahead_marker[i] = -1;
	}

	//BFS queue for the pairs
	int qs = 0;
	int qe = 0;

	for (int i = 0; i < N; ++i) {
		int id = Id(i, i);
		distance[id] = 0;
		que[qe++] = id;
	}

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int step = 1;
	while (no_actives > 1) {
		int lqe = 0;
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum distance
		int min_distance = N * N;
		int min_id = -1;
		if (no_actives < N) {
			if (no_actives > max_state) {
				if (2 * (qe - N) > no_actives * (no_actives - 1)) {
					for (int i = 0; i < no_actives; i++) {
						for (int j = 0; j < i; j++) {
							int s1 = actives[i];
							int s2 = actives[j];

							int id = Id(s1, s2);

							if (distance[id] != -1 && min_distance > distance[id]) {
								min_distance = distance[id];
								min_id = id;
								if (min_distance == 1) break;
							}
						}
						if (min_distance == 1) break;
					}
				}
				else {
					int marker = step - 1;
					for (int i = N; i < qe; i++) {
						int q_id = que[i];
						int q_s1 = s1fromId(q_id);
						int q_s2 = s2fromId(q_id, q_s1);
						if (active_marker[q_s1] == marker && active_marker[q_s2] == marker) {
							min_distance = distance[q_id];
							min_id = q_id;
							break;
						}
					}
				}
			}
			else {
				for (int i = 0; i < no_actives; i++) {
					for (int j = 0; j < i; j++) {
						int s1 = actives[i];
						int s2 = actives[j];

						int id = Id(s1, s2);

						if (distance[id] != -1 && min_distance > distance[id]) {
							min_distance = distance[id];
							min_id = id;
							if (min_distance == 1) break;
						}

						lookahead_marker[id] = step;
						lookahead_parent[id] = -1;
						lookahead_queue[lqe++] = id;
					}
					if (min_distance == 1) break;
				}
			}

			if (min_id == -1 && (no_actives <= max_state)) {
				int lqs = 0;
				int end_level = lqe;
				while (lqs < end_level) {
#if LOG_LEVEL == DATA_ANALYSIS
					lookahead_counter++;
#endif
					int l_id = lookahead_queue[lqs++];

					int l_s1 = s1fromId(l_id);
					int l_s2 = s2fromId(l_id, l_s1);

					for (int p = 0; p < P; p++) {
						int* ap = &a[p * N];
						int ts1 = ap[l_s1];
						int ts2 = ap[l_s2];

						int tid = Id(ts1, ts2);
						if (distance[tid] != -1 && distance[tid] < min_distance) { //there is a path from an active pair to one in the queue
							min_distance = distance[tid];
							lookahead_path[tid] = p;
							lookahead_parent[tid] = l_id;
							min_id = tid;
						}
						else if (lookahead_marker[tid] != step) {
							lookahead_queue[lqe++] = tid;
							lookahead_parent[tid] = l_id;
							lookahead_marker[tid] = step;
							lookahead_path[tid] = p;
						}
					}

					if (lqs == end_level && end_level < max_lookahead_count && min_id == -1) {
						end_level = lqe;
						//out << end_level << endl;
					}
				}

				if (min_id != -1) {
					lookahead_length = recursivePathGrow(actives, no_actives, a, lookahead_parent, lookahead_path, min_id, path, last, N);
				}
				else
					lookahead_length = 0;
			}
		}

		if (min_id == -1) {
			min_id = processUntilActive(iap, ia, N, P, que, distance, next, letter, qs, qe, active_marker, step - 1);

			if (min_id == -1) {
				out << "automata is not synchronizing " << endl;
				exit(1);
			}
		}

#if LOG_LEVEL == DATA_ANALYSIS
		int distance_id = distance[min_id] + lookahead_length;
		if (max_of_min_distances < distance_id)
			max_of_min_distances = distance_id;
		min_distance_counter++;
		min_distance_sum += distance_id;
#endif

		//apply the path and store it
		int pid = min_id;
		while (distance[pid] > 0) {
			int let = letter[pid];
			insertToPath(let, path, last);

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let * N + actives[i]];
			}

			pid = next[pid];
		}

		//reduce the number of active states
		int active_count = 0;
		for (int i = 0; i < no_actives; i++) {
			int act = actives[i];
			if (active_marker[act] != step) {
				actives[active_count++] = act;
				active_marker[act] = step;
			}
		}
		no_actives = active_count;
		step++;
	}


#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL == TIME_ANALYSIS
	out << total << ",";
#endif
#endif


#if LOG_LEVEL == DATA_ANALYSIS
	qe--;
	out << qe - N << "," << distance[que[qe]] << ","
		<< max_of_min_distances << "," << float(min_distance_sum) / min_distance_counter << "," << lookahead_counter;
#endif

	free(distance);
	free(next);
	free(letter);
	free(que);
	free(actives);
	free(active_marker);
	free(lookahead_queue);
}

int applyPath(int* a, PNode* path, int N) {
	int* actives = new int[N];
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	PNode* pnode = path;
	while (pnode) {
		int let = pnode->letter;
		for (int i = 0; i < N; i++) {
			actives[i] = a[let * N + actives[i]];
		}
		pnode = pnode->next;
	}

	int* active_marker = new int[N];
	for (int i = 0; i < N; i++) {
		active_marker[i] = 0;
	}

	int active_count = 0;
	for (int i = 0; i < N; i++) {
		int act = actives[i];
		if (active_marker[act] != 1) {
			active_marker[act] = 1;
			active_count++;
		}
	}

	free(active_marker);
	free(actives);
	return active_count;
}

int checkInverse(int* a, int* iap, int* ia, int N, int P) {
	for (int p = 0; p < P; p++) {
		for (int i = 0; i < N; i++) {
			int target = a[p * N + i];

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
				if (a[p * N + source] != i) {
					out << "something is wrong " << i << " has " << source << " in inverse automata but it " << source << " goes to " << a[p * N + source] << " with " << p << "\n";
					exit(1);
				}
			}
		}
	}

	return 0;
}

int main(int argc, char** argv) {
	if (argc < 5 || !((argc == 4 && strcmp(argv[2], "cerny") == 0) || (argc == 7 && strcmp(argv[5], "rand") == 0) || (argc = 6 + atoi(argv[2]) * atoi(argv[1]) && strcmp(argv[5], "arg") == 0))) {
		cout << "Usage: " << argv[0] << " no_states alphabet_size algorithm_level rand_seed rand weight_upper_bound\n" << endl;
		cout << "Usage: " << argv[0] << " no_states alphabet_size algorithm_level rand_seed arg weight_1 ... weight_P\n" << endl;
		cout << "Usage: " << argv[0] << " no_states cerny algorithm_level\n" << endl;
		return 1;
	}


	char* filename = new char[256];
	snprintf(filename, 256, "extreme_test_level_2/greedy1_%s_%s_%s_%s.txt", argv[1], argv[2], argv[4], argv[6]);  //file path
	out.open(filename);

	int N = atoi(argv[1]);
	int level = atoi(argv[3]);
	int wd = atoi(argv[6]);

#ifdef LOG_LEVEL
	struct stat st = { 0 };
	if (stat("results_greedy", &st) == -1) {
		mkdir("results_greedy", 0700);
	}
	char* filename = new char[256];
#if LOG_LEVEL == TIME_ANALYSIS
	sprintf(filename, "results_greedy/timeAndLength_%s_%s.csv", argv[1], argv[2]);
#elif LOG_LEVEL == DATA_ANALYSIS
	sprintf(filename, "results_greedy/data_%s_%s.csv", argv[1], argv[2]);
#endif
	if (argc == 5 && strcmp(argv[4], "HEADER") == 0) {
		out.open(filename);
		if (level & 1) {
#if LOG_LEVEL == TIME_ANALYSIS
			out << "bfs_time_naive,";
			out << "time_naive,";
			out << "length_naive";
#elif LOG_LEVEL == DATA_ANALYSIS
			out << "allnodes_naive,";
			out << "nodes_naive,";
			out << "level_naive,";
			out << "maxlevel_naive,";
			out << "meanlevel_naive";
#endif
			if ((level ^ 1) > 1)
				out << ",";
		}
		if (level & 2) {
#if LOG_LEVEL == TIME_ANALYSIS
			out << "time_economic,";
			out << "length_economic";
#elif LOG_LEVEL == DATA_ANALYSIS
			out << "nodes_economic,";
			out << "level_economic,";
			out << "maxlevel_economic,";
			out << "meanlevel_economic";
#endif

			if ((level ^ 2) > 2)
				out << ",";
		}
		if (level & 4) {
#if LOG_LEVEL == TIME_ANALYSIS
			out << "time_further,";
			out << "length_further,";
			out << "time_smart,";
			out << "length_smart";
#elif LOG_LEVEL == DATA_ANALYSIS
			out << "nodes_further,";
			out << "level_further,";
			out << "maxlevel_further,";
			out << "meanlevel_further,";
			out << "lookahead_counter_further,";
			out << "nodes_smart,";
			out << "level_smart,";
			out << "maxlevel_smart,";
			out << "meanlevel_smart,";
			out << "lookahead_counter_smart";
#endif
			if ((level ^ 4) > 4)
				out << ",";
		}
		out << endl;
		out.close();
		return 0;
	}
	out.open(filename, ios::app);
	delete[] filename;
#endif

	int P = atoi(argv[2]);
	unsigned int seed;
	int* automata;
	int* weights = new int[P];
	if ((strcmp(argv[2], "cerny") == 0)) {
		seed = 0;
		P = 2;
		automata = new int[P * N];

#pragma omp parallel
		{
#pragma omp for schedule(static)
			for (int i = 0; i < N; ++i) {
				automata[i] = i;
				automata[i + N] = (i + 1) % N;
			}
			automata[0] = 1;
		}
	}
	else {

		seed = atoi(argv[4]);
		automata = new int[P * N];


		//#pragma omp parallel
		//{
		unsigned int tseed = (omp_get_thread_num() + 1) * (seed + 1912812);
		//#pragma omp  schedule(static)

#ifdef __GNUC__


		for (int i = 0; i < P * N; ++i) {
			automata[i] = ((int)rand_r(&tseed)) % N;
		}
		/*

		automata[0] = 1;
		automata[1] = 1;
		automata[2] = 2;
		automata[3] = 3;
		automata[4] = 1;
		automata[5] = 2;
		automata[6] = 3;
		automata[7] = 0;
		*/

		if (strcmp(argv[5], "rand") == 0) {
			for (int i = 0; i < P; i++) {
				//weights[i] = 1;
				weights[i] = ((int)rand_r(&tseed) % wd) + 1;
			}
		}

#endif

#ifdef _WIN32
		srand(tseed);

		for (int i = 0; i < P * N; ++i) {
			automata[i] = ((int)rand()) % N;
		}



		/*// Cerny with n=4
		automata[0] = 1;
		automata[1] = 1;
		automata[2] = 2;
		automata[3] = 3;
		automata[4] = 1;
		automata[5] = 2;
		automata[6] = 3;
		automata[7] = 0;*/

		/*
		automata[0] = 2;
		automata[1] = 2;
		automata[2] = 2;
		automata[3] = 1;
		automata[4] = 2;
		automata[5] = 2;
		*/

		if (strcmp(argv[5], "rand") == 0) {
			for (int i = 0; i < P; i++) {
				//weights[i] = 1;
				weights[i] = ((int)rand() % wd) + 1;
			}
		}


#endif	

		else {
			for (int i = 0; i < P; i++) {
				weights[i] = atoi(argv[i + 6]);
			}
		}
		//}
	}
#ifdef DEBUG
	printAutomata(automata, N, P, weights);
#endif

	/*out << P << " "<< N << endl;
	for(int i = 0; i < N; ++i) {
	for(int j = 0; j < P; ++j) {
		out << automata[j * N + i]  << " ";
	}
	out << endl;
	}*/

	int* inv_automata_ptrs = new int[P * (N + 1)];
	int* inv_automata = new int[P * N];

#pragma omp parallel for schedule(static)
	for (int i = 0; i < P; ++i) {
		int* a = &(automata[i * N]);
		int* ia = &(inv_automata[i * N]);
		int* iap = &(inv_automata_ptrs[i * (N + 1)]);

		memset(iap, 0, sizeof(int) * (N + 1));
		for (int j = 0; j < N; j++) { iap[a[j] + 1]++; }
		for (int j = 1; j <= N; j++) { iap[j] += iap[j - 1]; }
		for (int j = 0; j < N; j++) { ia[iap[a[j]]++] = j; }
		for (int j = N; j > 0; j--) { iap[j] = iap[j - 1]; } iap[0] = 0;
	}

	checkInverse(automata, inv_automata_ptrs, inv_automata, N, P);

#ifdef DEBUG
	printInverseAutomata(inv_automata_ptrs, inv_automata, N, P);
#endif

	if (level & 1) {
		PNode* path = NULL;
		greedyHeuristic_naive(automata, inv_automata_ptrs, inv_automata, N, P, path, weights);

		out << "Greedy path is found: ";
		PNode* pnode = path;
		int plength = 0;
		int pweight = 0;
		while (pnode) {


			///////////path control////////
			//cout << "Path Control:" << endl;
			//cout << (char)(pnode->letter + 97) << " "<<endl;
			///////////



			out << (char)(pnode->letter + 97) << " ";
			plength += 1;
			pweight += weights[pnode->letter];
			pnode = pnode->next;
		}
		out << endl << "Greedy path length is " << plength << endl;
		out << "Greedy path weight is " << pweight << endl;
		if (applyPath(automata, path, N) != 1)
		{
			out << "No of reaminig active states is not 1" << endl;
		}
		out << endl;
		path = NULL;
		greedyHeuristic_naive_weighted(automata, inv_automata_ptrs, inv_automata, N, P, path, weights);

		out << "Greedy Weighted path is found: ";
		pnode = path;
		plength = 0;
		pweight = 0;
		while (pnode) {
			out << (char)(pnode->letter + 97) << " ";
			plength += 1;
			pweight += weights[pnode->letter];
			pnode = pnode->next;
		}
		out << endl << "Greedy Weighted path length is " << plength << endl;
		out << "Greedy weightes path weight is " << pweight << endl;
		if (applyPath(automata, path, N) != 1)
		{
			out << "No of reaminig active states is not 1" << endl;
		}
		out << endl;

#ifdef DEBUGA
		out << "Weights ----------------------" << endl;
		for (int i = 0; i < P; ++i) {
			out << weights[i] << " ";
		}
		out << endl << endl;
		printAutomata(automata, N, P, weights);
#endif

#ifdef DEBUG2
		path = NULL;
		shortestPath(automata, N, P, path, weights);
#endif
#if LOG_LEVEL == TIME_ANALYSIS
		out << plength;
#endif
#ifdef LOG_LEVEL
		if ((level ^ 1) > 1)
			out << ",";
#endif
	}
	/*
	if (level & 2) {
		PNode* path2 = NULL;
		greedyHeuristic_economic(automata, inv_automata_ptrs, inv_automata, N, P, path2);

		out << "Path is found: ";
		PNode* pnode2 = path2;
		int plength2 = 0;
		while (pnode2) {
			out << pnode2->letter << " ";
			pnode2 = pnode2->next;
			plength2 += weights[pnode2->letter];
		}
		out << endl << "Path length is " << plength2 << endl;
		out << "no remaining actives is: " << applyPath(automata, path2, N) << endl << endl;
#if LOG_LEVEL == TIME_ANALYSIS
		out << plength2;
#endif


		/*PNode* path3 = NULL;
		greedyHeuristic_economic_lookahead(automata, inv_automata_ptrs, inv_automata, N, P, path3);

		out << "Path is found: ";
		PNode* pnode3 = path3;
		int plength3 = 0;
		while (pnode3) {
			out << pnode3->letter << " ";
			pnode3 = pnode3->next;
			plength3++;
		}
		out << endl << "Path length is " << plength3 << endl;
		out << "no remaining actives is: " << applyPath(automata, path3, N) << endl << endl;

		#if LOG_LEVEL == TIME_ANALYSIS
		out << plength3;
		#endif

#ifdef LOG_LEVEL
		if ((level ^ 2) > 2)
			out << ",";
#endif
	}*/
	/*
	if (level & 4) {
		PNode* path4 = NULL;
		greedyHeuristic_economic_lookahead_further(automata, inv_automata_ptrs, inv_automata, N, P, path4, (log(N) / log(2)), N);

		out << "Path is found: ";
		PNode* pnode4 = path4;
		int plength4 = 0;
		while (pnode4) {
			out << pnode4->letter << " ";
			pnode4 = pnode4->next;
			plength4 += weights[pnode4->letter];
		}
		out << endl << "Path length is " << plength4 << endl;
		out << "no remaining actives is: " << applyPath(automata, path4, N) << endl << endl;
#if LOG_LEVEL == TIME_ANALYSIS
		out << plength4 << ",";
#endif
		PNode* path5 = NULL;
		greedyHeuristic_economic_lookahead_further_smart(automata, inv_automata_ptrs, inv_automata, N, P, path5, (log(N) / log(2)), N);

		out << "Path is found: ";
		PNode* pnode5 = path5;
		int plength5 = 0;
		while (pnode5) {
			out << pnode5->letter << " ";
			pnode5 = pnode5->next;
			plength5 += weights[pnode5->letter];
		}
		out << endl << "Path length is " << plength5 << endl;
		out << "no remaining actives is: " << applyPath(automata, path5, N) << endl << endl;

#if LOG_LEVEL == TIME_ANALYSIS
		out << plength5 ;
#endif
#ifdef LOG_LEVEL
		if ((level ^ 4) > 4)
			out << ",";
#endif
	}*/
#ifdef LOG_LEVEL
	out << endl;
	out.close();
#endif
	return 0;
}
