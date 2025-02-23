CC=g++
CFLAGS=-O3 -fopenmp  -O3
FILES=heuristics.cpp global.h naive.h
heuristics: $(FILES)
	$(CC) -o heuristics heuristics.cpp $(CFLAGS);
greedy: $(FILES)
	$(CC) -o greedy greedy.cpp $(CFLAGS);
  
clean:
	rm -rf heuristics 
	rm -rf greedy 