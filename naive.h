#ifndef _NAIVE_H_
#define _NAIVE_H_

#include <iostream>
#include <fstream>
#include <iomanip>
#include "global.h"
#include "limits.h"
#include <cfloat>
#include <queue> //ege

using namespace std;

ofstream out;

enum AlgorithmType { topDown, bottomUp, hybrid };
enum CudaOpt { naive, memory, warp };

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
void synchronizing_check(int *a, int N, int P, int *distance) {
	int* levels = new int[N * (N+1) / 2];
	memset(levels, 0, N * (N + 1) / 2 * sizeof(int));
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
					//out << "tid " << tid << ": distance is " << distance[tid] << endl; //berk
				}

				cout << "automata is not synchronizing. pair " << id << " - (" << i << ", " << j << ") is not mergable\n";
				cout << endl;
				exit(0);
				return;
			}
			else {
				levels[distance[id]]++;
			}
		}
	}

	cout << "automata is synchronizing.\n";
	cout << endl;

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

template<bool memoryOpt>
long long costPhi(int *a, int *distance, int *letter, int *actives, int *active_marker, int N, int P, int id, int no_actives, int step)
{
	while (distance[id] > 0) {
		//out << id << " " << no_actives << endl;
		int let = letter[id];

		for (int i = 0; i < no_actives; i++) {
			actives[i] = a[let + actives[i] * P];
		}

		int s1, s2;

		if (memoryOpt) {
			s1 = s1fromId(id);
			s2 = s2fromId(id, s1);
			id = Id(a[let + s1 * P], a[let + s2 * P]);
		}
		else {
			s1 = id / N;
			s2 = id % N;
			id = IdNaive(a[let + s1 * P], a[let + s2 * P], N);
		}
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

#if ALGORITHM == SP || ALGORITHM == PL || ALGORITHM == FR
	long long finalTotalDist = 0;
	for (int i = 0; i < no_actives; i++) {
		for (int j = 0; j < i; j++) {
			int s1 = actives[i];
			int s2 = actives[j];

			int tid;
			if (memoryOpt)
				tid = Id(s1, s2);
			else
				tid = IdNaive(s1, s2, N);

			finalTotalDist += distance[tid];
		}
	}

	return finalTotalDist;
#elif ALGORITHM == CR
	return no_actives;
#endif
}

template<bool memoryOpt>
void greedyHeuristic_finding(int *a, int *distance, int *letter, int *actives, int * active_marker, int N, int P, PNode* &path, int* w) {

	PNode* last = NULL;
	memset(active_marker, 0, sizeof(int) * N);

	int no_actives = N;
	for (int i = 0; i < N; ++i) {
		actives[i] = i;
	}

	int* cp_actives = new int[N];
	int* cp_active_marker = new int[(N * (N + 1)) / 2];
	int step = 1;
	vector<int> remActives;
	vector<string> syncSubseq;
	vector<int> weightSubseq;
	remActives.push_back(no_actives);
	while (no_actives > 1) {
		//out << "no active states is " << no_actives << endl;
		//find the pair id with minimum phi-cost value 

		long long int min_cost = LLONG_MAX;

		int min_id;

		for (int i = 0; i < no_actives; i++) {
			for (int j = 0; j < i; j++) {
				int s1 = actives[i];
				int s2 = actives[j];

				int id;
				if (memoryOpt)
					id = Id(s1, s2);
				else
					id = IdNaive(s1, s2, N);

				memcpy((void*)cp_actives, (void*)actives, sizeof(int) * N);
				memcpy((void*)cp_active_marker, (void*)active_marker, sizeof(int) * (N * (N + 1)) / 2);
        
        long long int cost = costPhi<memoryOpt>(a, distance, letter, cp_actives, cp_active_marker, N, P, id, no_actives, step);

				if (min_cost > cost) {
					min_cost = cost;
					min_id = id;
				}
			}
		}
		//out << min_id << " " << min_cost << " "; //berk

#if LOG_LEVEL & DATA_ANALYSIS
		if (max_of_min_distances < distance[min_id])
			max_of_min_distances = distance[min_id];
		min_distance_counter++;
		min_distance_sum += distance[min_id];
#endif
		// out << "merging pair from level " << min_distance << endl;

		//apply the path and store it
		int pid = min_id;
		int added = 0;
		string s = "";
		int we = 0;
		while (distance[pid] > 0) {
			//printf("%d, %d\n" , distance[pid], pid); //berk
			int let = letter[pid];
			insertToPath(let, path, last);
			added++;

			for (int i = 0; i < no_actives; i++) {
				actives[i] = a[let + actives[i] * P];
			}

			int s1, s2;

			if (memoryOpt) {
				s1 = s1fromId(pid);
				s2 = s2fromId(pid, s1);
				pid = Id(a[let + s1 * P], a[let + s2 * P]);
			}
			else {
				s1 = pid / N;
				s2 = pid % N;
				pid = IdNaive(a[let + s1 * P], a[let + s2 * P], N);
			}

			s += char(let) + 97;
			we += w[let];
		}
		syncSubseq.push_back(s);
		weightSubseq.push_back(we);

		//out << added << endl; //berk

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

	free(cp_actives);
	free(cp_active_marker);
}

void greedyHeuristic_naive(int* a, int* iap, int* ia, int N, int P, PNode* &path, int* w) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];

	int* distance = new int[noOfPair];
	int* letter = new int[noOfPair];
	int* que = new int[noOfPair];

	int* active_marker = new int[noOfPair];

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif

#if LOG_LEVEL & DATA_ANALYSIS
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
	while (qs < qe) {
		int q_id = que[qs++];
		int q_dist = distance[q_id];

		//will process the pair with id q_id now
		int q_s1 = s1fromId(q_id); //the first state in the pair
		int q_s2 = s2fromId(q_id, q_s1); //the second state in the pair (we are sure that q_s1 >= q_s2)

#ifdef DEBUG
		out << "will process " << q_s1 << " " << q_s2 << " with id  " << q_id << " with distance " << q_dist << endl;
#endif

		int* p_ia = ia; //this is the inverse automata for letter p
		int* p_iap = iap; //and its state pointers

		for (int p = 0; p < P; p++) {

			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < p_iap[q_s1 + 1]; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < p_iap[q_s2 + 1]; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];
					int ia_id = Id(ia_s1, ia_s2);
					if (distance[ia_id] < 0) { //we found an unvisited pair. so we need to add this to the queue
						distance[ia_id] = q_dist + 1;
						letter[ia_id] = p;
						que[qe++] = ia_id;
					}
				}
			}
			p_ia += N; //this is the inverse automata for letter p
			p_iap += (N + 1); //and its state pointers
		}
	}
#ifdef TIMER
	double time = omp_get_wtime() - t1;
	total += time;
	out << "BFS tree generation takes " << time << " seconds\n";
#if LOG_LEVEL & TIME_ANALYSIS
	out << time << " ";
#endif
#endif

	synchronizing_check<true>(a, N, P, distance);

#ifdef TIMER
	t1 = omp_get_wtime();
#endif

	greedyHeuristic_finding<true>(a, distance, letter, actives, active_marker, N, P, path, w);

#ifdef TIMER
	time = omp_get_wtime() - t1;
	out << "Path generation takes " << time << " seconds\n";
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL & TIME_ANALYSIS
	out << total << " ";
#endif
#endif
#if LOG_LEVEL & DATA_ANALYSIS
	out << " " << (N * (N - 1)) / 2 << " " << lvl - 1 << " "
		<< max_of_min_distances << " " << float(min_distance_sum) / min_distance_counter;
#endif
	free(distance);
	free(letter);
	free(que);
	free(actives);
	free(active_marker);
}

//a is automata a[i][j] -> state j goes to a[i][j] with letter j
//iap is inverse automata pointers -> ia[i][iap[i][j] ... ia[i][j+1]] keeps the state ids which go to state j with letter i
//there are N states and p letters in the automata
void greedyHeuristic_naive_weighted(int* a, int* iap, int* ia, int N, int P, PNode* &path, int* w) {
	int noOfPair = (N * (N + 1)) / 2;
	int* actives = new int[N];

	int* distance = new int[noOfPair];
	int* letter = new int[noOfPair];
	priority_queue<DistID< int> > que; //ege: min heap for the weighted tree
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

	int* active_marker = new int[noOfPair];

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif

#if LOG_LEVEL & DATA_ANALYSIS
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
		que.push(DistID<int>(id, 0, i)); //ege
	}

	//there are more nodes in the queue
	int counter = N;
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
			int* p_iap = iap + p * (N+1); //and its state pointers
			for (int iap_s1_ptr = p_iap[q_s1]; iap_s1_ptr < p_iap[q_s1 + 1]; ++iap_s1_ptr) {
				int ia_s1 = p_ia[iap_s1_ptr];
				for (int iap_s2_ptr = p_iap[q_s2]; iap_s2_ptr < p_iap[q_s2 + 1]; ++iap_s2_ptr) {
					int ia_s2 = p_ia[iap_s2_ptr];
					int ia_id = Id(ia_s1, ia_s2);
					if (distance[ia_id] > q_dist + w[p]) { //berk: key change
						distance[ia_id] = q_dist + w[p]; 
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
	out << "Dijkstra tree generation takes " << time << " seconds\n";
#if LOG_LEVEL & TIME_ANALYSIS
	out << time << " ";
#endif
#endif

#ifdef TIMER
	t1 = omp_get_wtime();
#endif

	greedyHeuristic_finding<true>(a, distance, letter, actives, active_marker, N, P, path, w);

#ifdef TIMER
	time = omp_get_wtime() - t1;
	out << "Path generation takes " << time << " seconds\n";
	total += time;
	out << "The heuristic takes " << total << " seconds\n";
#if LOG_LEVEL & TIME_ANALYSIS
	out << total << " ";
#endif
#endif
#if LOG_LEVEL & DATA_ANALYSIS
	out << " " << (N * (N - 1)) / 2 << " " << lvl - 1 << " "
		<< max_of_min_distances << " " << float(min_distance_sum) / min_distance_counter;
#endif
	free(distance);
	free(letter);
	free(actives);
	free(active_marker);
}


#endif //_NAIVE_H_

void shortestPath(int* a, int N, int P, PNode* &path, int* w) {
	unsigned long long int noOfNodes = pow (2.0, double(N));
	unsigned long long int* distance = new unsigned long long int[noOfNodes];
	unsigned long long int* prev = new unsigned long long int[noOfNodes];
	unsigned long long int* letter = new unsigned long long int[noOfNodes];
	priority_queue<DistID< unsigned long long int> > que; //ege: min heap for the weighted tree
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
		distance[i] =  ULLONG_MAX;
	}

	//dijkstra queue for the pairs
	distance[noOfNodes-1] = 0;
	prev[noOfNodes - 1] = noOfNodes - 1;
	que.push(DistID<unsigned long long int>(noOfNodes - 1, 0, 0));

	unsigned long long int * q_sN = new unsigned long long int[N];
	unsigned long long int * nextState = new unsigned long long int[N];
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
		for(unsigned long long int i = 0; i < N ; i++)
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

			for(unsigned long long int i = 0; i < N; i++)
			{
				if(q_sN[i] != 0)
				{
					nextState[a[p*N+i]] = 1; 
				}
				
			}
			unsigned long long int id = 0;
			for(unsigned long long int i = 0; i < N; i++)
			{
				if(nextState[i] == 1)
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

/*void shortestPath(int* a, int N, int P, PNode* &path, int* w) {
	int noOfNodes = pow(2.0, double(N));
	int* actives = new int[N];
	int* active_marker = new int[N];

	int* distance = new int[noOfNodes];
	int* prev = new int[noOfNodes];
	int* letter = new int[noOfNodes];
	priority_queue<DistID> que; //ege: min heap for the weighted tree
	int * orderedInputs = new int[P];
	int * tempw = new int[P];

	for (int i = 0; i <P; i++) tempw[i] = w[i];

	for (int x = 0; x < P; x++)
	{
		int order;
		int min_weight = INT_MAX;
		for (int i = 0; i < P; i++)
		{
			if (tempw[i] < min_weight)
			{
				min_weight = tempw[i];
				order = i;
			}
		}

		orderedInputs[x] = order;
		tempw[order] = INT_MAX;
	}

	delete[] tempw;

#ifdef TIMER
	double t1 = omp_get_wtime();
	double total = 0;
#endif
#if LOG_LEVEL == DATA_ANALYSIS
	int max_of_min_distances = 0;
	int min_distance_counter = 0;
	int min_distance_sum = 0;
#endif

	for (int i = 0; i < noOfNodes; i++) {
		distance[i] = -1;
	}

	//dijkstra queue for the pairs

	distance[noOfNodes - 1] = 0;
	prev[noOfNodes - 1] = noOfNodes - 1;
	que.push(DistID(noOfNodes - 1, 0));

	int * q_sN = new int[N];
	int * nextState = new int[N];
	//there are more nodes in the queue
	while (!que.empty()) {
		int q_id = (que.top()).id; //ege
		que.pop();
		int q_dist = distance[q_id];
		int temp_q_id = q_id;
		int bin_id = 0;
		int q_bin_id = 0;
		int temp_id;

		//will process the pair with id q_id now
		for (int i = 0; i < N; i++)
		{
			q_sN[i] = temp_q_id % 2;
			temp_q_id = temp_q_id >> 1;
			if (q_sN[i] != 0)
				q_bin_id += pow(10, N - i - 1);
		}
#ifdef DEBUG
		out << "will process\t" << bin_id << "\twith id\t" << q_id << "\twith distance\t" << q_dist << endl;
#endif
		for (int j = 0; j < P; j++) {
			int p = orderedInputs[j];
			memset(nextState, 0, sizeof(int) * N);

			for (int i = 0; i < N; i++)
			{
				if (q_sN[i] != 0)
				{
					nextState[a[P*i + p]] = 1;
				}

			}
			int id = 0;
			for (int i = 0; i < N; i++)
			{
				if (nextState[i] == 1)
				{
					id += (1 << i);
					bin_id += pow(10, N - i - 1);
				}
			}
			
			if (distance[id] < 0)
			{
				distance[id] = q_dist + w[p];
				prev[id] = q_id;
				letter[id] = p;
#ifdef DEBUG
				out << bin_id << " is not visited before. Distance of it is " << distance[id] << ". It can be reached from " << q_bin_id << " with " << w[p] << " weight" << endl;
#endif
				que.push(DistID(id, distance[id]));
			}
			else if (distance[id] > q_dist + w[p]) //berk: key change
			{
				distance[id] = q_dist + w[p];
				prev[id] = q_id;
				letter[id] = p;
#ifdef DEBUG
				out << bin_id << "'s distance is changed. Distance of it is " << distance[id] << ". It can be reached from " << q_bin_id << " with " << w[p] << " weight" << endl;
#endif
				que.push(DistID(id, distance[id]));
			}
			bin_id = 0;
		}
#ifdef DEBUG
		out << endl;
#endif
	}

	delete[] q_sN;
	delete[] nextState;


	int mindist = INT_MAX;
	int minid;
	for (int i = 0; i < N; i++) {
		int pw = pow(2, i);
		if (distance[pw] < mindist && distance[pw] > -1) {
			mindist = distance[pw];
			minid = pw;
		}
	}

	int weight = 0;
	int length = 0;
	int s = minid;
	int limit = pow(2, N) - 1;
	vector<char> seq;
	while (s < limit) {
		int p = letter[s];
		seq.push_back(char(p + 97));
		s = prev[s];
		weight += w[p];
		length++;
	}
	
	out << "Shortest Path: ";
	for (int i = seq.size() - 1; i >= 0; i--) {
		out << seq[i] << " ";
	}
	out << endl << "Shortest Path Length:" << length << endl;
	out << "Shortest Path Weight:" << weight << endl; //todo: insert to path
}*/