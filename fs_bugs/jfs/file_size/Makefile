CC = gcc
CFLAGS = -Wall

TARGET = driver

all: $(TARGET)

$(TARGET): driver.c
	$(CC) $(CFLAGS) $< -o $@

run: $(TARGET)
	./driver

clean:
	rm -f $(TARGET)
