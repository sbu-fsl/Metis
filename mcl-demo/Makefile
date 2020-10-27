COMMON_DIR=../common
EXPLODE_PATH=/profiling/explode-0.1pre
override CFLAGS += -g -I../include -I$(EXPLODE_PATH) -I$(EXPLODE_PATH)/mcl 
override LIBS += -lssl -lcrypto -lrt -lstdc++fs

all: example.cpp
	g++ -o example example.cpp $(COMMON_DIR)/*.c $(EXPLODE_PATH)/mcl/libmc.a $(CFLAGS) $(LIBS)

run: all
	./example

pathutils: $(COMMON_DIR)/path_utils.cpp
	g++ -fPIC -I../include -o path_utils.o -c $(COMMON_DIR)/path_utils.cpp
	ar rcs path_utils.a path_utils.o

clean:
	rm -rf test test.txt pan* *.log *.o *.a absfs *.trail \
	rm -rf /mnt/test-*/test*
