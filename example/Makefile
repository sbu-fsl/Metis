COMMON_DIR=../common
override CFLAGS += -I../include -lpthread

all: test.c
	gcc -g -o test test.c $(COMMON_DIR)/*.c $(CFLAGS)

clean:
	rm *.log *.json test
