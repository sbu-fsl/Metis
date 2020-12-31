override CFLAGS += -g -Wall -Werror -I../include

EXT = ../common/*.c

all: crmfs ckpt restore

crmfs: crmfs.c cr.cpp
	gcc $(CFLAGS) -o crmfs crmfs.c cr.cpp $(EXT) -lstdc++ -lrt -lfuse

ckpt: ckpt.c
	gcc $(CFLAGS) -o ckpt ckpt.c $(EXT)

restore: restore.c
	gcc $(CFLAGS) -o restore restore.c $(EXT)

clean:
	rm -f ckpt restore crmfs *.o *.log .*.swp

