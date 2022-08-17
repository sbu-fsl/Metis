OBJDIR := ../../../fs-state
COMMON_DIR := ../../../common
COMMON_SRC := $(wildcard $(COMMON_DIR)/*.c) $(wildcard $(COMMON_DIR)/*.cpp)
COMMON_OBJ := $(patsubst $(COMMON_DIR)/%,$(OBJDIR)/%.o,$(COMMON_SRC))

override CFLAGS += -g -I../../../include # -D T_RAND -D P_RAND
override LIBS += -lssl -lcrypto -lrt -lstdc++ -lstdc++fs -lpthread -lprofiler -lxxhash -lz

test: driver
	sudo bash -x run_driver.sh 

driver: driver.c common-libs
	gcc -Wall -Werror -o driver $< $(OBJDIR)/common-libs.a $(CFLAGS) $(LIBS)

common-libs: $(COMMON_OBJ)
	ar rvs $(OBJDIR)/$@.a $^

%.c.o: $(COMMON_DIR)/%.c
	gcc -Wall -Werror -o $(OBJDIR)/$@ -fPIC -c $< $(CFLAGS) $(LIBS)

%.cpp.o: $(COMMON_DIR)/%.cpp
	g++ -std=c++11 -Wall -Werror -o $(OBJDIR)/$@ -fPIC -c $< $(CFLAGS) $(LIBS)

clean:
	rm driver
