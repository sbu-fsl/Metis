COMMON_DIR := ./common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I./include -D PRINTF # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler

all: libmcfs

install: libmcfs
	sudo mkdir -p /usr/local/include/mcfs
	sudo cp include/*.h /usr/local/include/mcfs/
	sudo cp $^.so /usr/local/lib/
	sudo ldconfig

uninstall: libmcfs
	sudo rm -rf /usr/local/include/mcfs
	sudo rm /usr/local/lib/$^.so
	sudo ldconfig

libmcfs: $(COMMON_OBJ)
	ar rvs $@.a $^ 
	gcc -shared -fPIC -o $@.so $^ $(LIBS)

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm -f *.o *.so *.a

