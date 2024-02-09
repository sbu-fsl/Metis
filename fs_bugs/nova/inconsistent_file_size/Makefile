CC=gcc

override CFLAGS += -g
override LIBS += -lstdc++

driver: driver.c
	$(CC) -o driver driver.c  $(CFLAGS) $(LIBS)

clean:
	rm -f *.o *.a driver
