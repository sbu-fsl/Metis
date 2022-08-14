OBJDIR := ../../fs-state
COMMON_DIR := ../../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,%.o,$(COMMON_SRC))
override CFLAGS += -g -I../../include # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz

all: absfs_test.c common-libs
	gcc -Wall -Werror -o absfs_test $< common-libs.a $(CFLAGS) $(LIBS)

$(OBJDIR)/init_globals.o: $(OBJDIR)/init_globals.c common-libs
	gcc -Wall -Werror -o $@ -c $< common-libs.a $(CFLAGS) $(LIBS)

common-libs: $(COMMON_OBJ)
	ar rvs $@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $@ -fPIC -c $< $(CFLAGS) $(LIBS)

absfs-set: $(OBJDIR)/set.cpp $(OBJDIR)/init_globals.o
	g++ -std=c++11 -o $(OBJDIR)/set.o -c $< $(CFLAGS) $(LIBS)

clean:
	rm absfs_test *.o *.a
