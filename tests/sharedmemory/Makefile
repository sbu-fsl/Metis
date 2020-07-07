all: sender receiver

receiver: receiver.o
	g++ receiver.o -o receiver -lrt

sender: sender.o
	g++ sender.o -o sender -lrt

receiver.o: receiver.cpp
	g++ -c receiver.cpp -std=c++17 -Wall -Wextra -pedantic-errors

sender.o: sender.cpp
	g++ -c sender.cpp -std=c++17 -Wall -Wextra -pedantic-errors

clean:
	rm *.o sender receiver