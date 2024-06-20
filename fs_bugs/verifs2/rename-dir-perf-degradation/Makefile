CC=gcc
CFLAGS=-Wall -g
TARGET=rename-dirs-test

all: $(TARGET)

$(TARGET): rename-dirs-test.c
	$(CC) $(CFLAGS) -o $(TARGET) rename-dirs-test.c

clean:
	rm -f $(TARGET)
