all: states.pml
	spin -a states.pml; \
	gcc -o pan -D PRINTF pan.c;

bfs: states.pml
	spin -a states.pml; \
	gcc -o pan -D PRINTF -D BFS pan.c;

clean:
	rm pan*
