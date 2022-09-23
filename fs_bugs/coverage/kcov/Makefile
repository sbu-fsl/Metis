CC=gcc

kcov_cmd: kcov_cmd.c
	$(CC) -o $@ $^

run: kcov_cmd
	./kcov_cmd

clean:
	rm kcov_cmd
