#include "nanotiming.h"
#include <linux/limits.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <pthread.h>
#include <unistd.h>
#include <signal.h>
#include <errno.h>

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>

#define EVENT_INIT_CAP	1024

struct test_event {
	struct timespec ts;
	ssize_t ret;
	int err;
	int workerid;
	char func[10];
	char *argstr;
};

struct {
	struct test_event *events;
	struct timespec starttime;
	size_t len;
	size_t cap;
} event_vec;

pthread_mutex_t __mtx;
bool stop;

extern char const * errnoname(int errno_);
void output_events(const char *logfile_name);

void handle_interrupt(int signal)
{
	if(signal == SIGINT) {
		printf("Keyboard interrupt...\n");
		stop = true;
	}
}

int msleep(long tms)
{
    struct timespec ts;
    int ret;
 
    if (tms < 0)
    {
        errno = EINVAL;
        return -1;
    }
 
    ts.tv_sec = tms / 1000;
    ts.tv_nsec = (tms % 1000) * 1000000;
 
    do {
        ret = nanosleep(&ts, &ts);
    } while (ret && errno == EINTR);
 
    return ret;
}

/* Sleep for 1~100ms */
void rand_delay()
{
	int randnum = rand();
	unsigned long int ms = 1 + (unsigned long int)randnum * 99 / RAND_MAX;
	usleep(ms * 1000);
}

static inline void init_event_vec()
{
	event_vec.len = 0;
	event_vec.cap = EVENT_INIT_CAP;
	event_vec.events = calloc(event_vec.cap, sizeof(struct test_event));
	assert(event_vec.events);
	current_utc_time(&event_vec.starttime);
}

static inline void expand_event_vec()
{
	event_vec.events = realloc(event_vec.events,
	    2 * event_vec.cap * sizeof(struct test_event));
	assert(event_vec.events);
	event_vec.cap *= 2;
}

static inline void add_event(char *func_name, int ret, int err, int worker,
			     char *argfmt, ...)
{
	if (event_vec.len >= event_vec.cap)
		expand_event_vec();

	struct timespec now, delta;
	struct test_event *e = &event_vec.events[event_vec.len];
	size_t length;
	char *argstring;
	va_list op_args, op_args2;
	
	/* Stop timer first */
	current_utc_time(&now);
	timediff(&delta, &now, &event_vec.starttime);

	/* Compose arg string */
	va_start(op_args, argfmt);
	va_copy(op_args2, op_args);
	length = vsnprintf(NULL, 0, argfmt, op_args) + 1;
	argstring = malloc(length);
	assert(argstring);
	vsnprintf(argstring, length, argfmt, op_args2);
	/* Syscall func name */
	e->func[9] = '\0';
	strncpy(e->func, func_name, 9);
	e->argstr = argstring;

	e->ts = delta;
	e->ret = ret;
	e->err = err;
	e->workerid = worker;
	event_vec.len++;
}

void init()
{
	struct sigaction handler_attr = {
		.sa_handler = handle_interrupt,
		.sa_mask = 0,
		.sa_flags = 0,
	};
	sigaction(SIGINT, &handler_attr, NULL);
	srand(time(NULL));
	init_event_vec();
	stop = false;
	pthread_mutex_init(&__mtx, NULL);
}

void cleanup()
{
	for (size_t i = 0; i < event_vec.len; ++i)
		free(event_vec.events[i].argstr);
	free(event_vec.events);
	pthread_mutex_destroy(&__mtx);
}

int my_open(int tid, const char *pathname, int flags, mode_t mode)
{
	int ret = 0, err = 0;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = open(pathname, flags, mode);
	err = errno;
	add_event("open", ret, err, tid, "{\"path\": \"%s\", \"flags\": %d, " 
		  "\"mode\": %d}", pathname, flags, mode);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;
}

ssize_t my_write(int tid, int fd, const void *buf, size_t count)
{
	ssize_t ret;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = write(fd, buf, count);
	add_event("write", ret, errno, tid, "{\"fd\": %d, \"bufaddr\": \"%p\""
		  ", \"count\": %zu}", fd, buf, count);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;
}

int my_close(int tid, int fd)
{
	int ret;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = close(fd);
	add_event("close", ret, errno, tid, "{\"fd\": %d}", fd);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;
}


int my_unlink(int tid, const char *pathname)
{
	int ret;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = unlink(pathname);
	add_event("unlink", ret, errno, tid, "{\"path\": \"%s\"}", pathname);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;
}

int my_mkdir(int tid, const char *pathname, mode_t mode)
{
	int ret;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = mkdir(pathname, mode);
	add_event("mkdir", ret, errno, tid, "{\"path\": \"%s\", \"mode\": %d}",
		  pathname, mode);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;

}

int my_rmdir(int tid, const char *pathname)
{
	int ret;
	rand_delay();
	pthread_mutex_lock(&__mtx);
	ret = rmdir(pathname);
	add_event("rmdir", ret, errno, tid, "{\"path\": \"%s\"}", pathname);
	errno = 0;
	pthread_mutex_unlock(&__mtx);
	return ret;
}

struct worker_arg {
	int worker_id;
	char *data;
	size_t dsize;
	const char *dirname;
	const char *filename;
};

void *worker(void *rawargs)
{
	struct worker_arg *args = rawargs;
	int fd;
	int myid = args->worker_id;

	my_mkdir(myid, args->dirname, 0755);
	my_rmdir(myid, args->dirname);
	fd = my_open(myid, args->filename, O_WRONLY | O_CREAT, 0777);
	my_write(myid, fd, args->data, args->dsize);
	my_close(myid, fd);
	my_unlink(myid, args->filename);

	return NULL;
}

static inline void cleanup_state(struct worker_arg *args)
{
	unlink(args->filename);
	rmdir(args->dirname);
}

void output_events(const char *logfile_name)
{
	char *jsonpath = malloc(PATH_MAX);
	assert(jsonpath);
	FILE *log = fopen(logfile_name, "w");
	assert(log);
	strncpy(jsonpath, logfile_name, PATH_MAX);
	strncat(jsonpath, ".json", PATH_MAX);
	FILE *json = fopen(jsonpath, "w");
	assert(json);

	int count = 1;
	fprintf(json, "[\n");
	fprintf(json, "\t[\n");
	for (int n = 0; n < event_vec.len; ++n) {
		struct test_event *e = &event_vec.events[n];

		fprintf(log, "[%4ld.%09ld] ", e->ts.tv_sec, e->ts.tv_nsec);
		if (e->workerid >= 0) {
			/* output json */
			fprintf(json, "\t\t{\n");
			fprintf(json, "\t\t\t\"ts\": %ld.%09ld,\n",
				e->ts.tv_sec, e->ts.tv_nsec);
			fprintf(json, "\t\t\t\"thread\": %d,\n", e->workerid);
			fprintf(json, "\t\t\t\"func\": \"%s\",\n", e->func);
			fprintf(json, "\t\t\t\"ret\": %zd,\n", e->ret);
			fprintf(json, "\t\t\t\"err\": %d,\n", e->err);
			fprintf(json, "\t\t\t\"args\": %s\n", e->argstr);
			fprintf(json, "\t\t}");
			if (n < event_vec.len - 1 && (e + 1)->workerid >= 0)
				fprintf(json, ",\n");
			else
				fprintf(json, "\n");
			/* output textual log */
			fprintf(log, "thread = %d, ", e->workerid);
			fprintf(log, "func = '\e[1;4m%s\e[0m', ", e->func);
			fprintf(log, "ret = ");
			if (e->ret < 0)
				fprintf(log, "\e[93m%zd\e[0m, ", e->ret);
			else if (e->ret > 0)
				fprintf(log, "\e[92m%zd\e[0m, ", e->ret);
			else
				fprintf(log, "%zd, ", e->ret);
			fprintf(log, "error = ");
			if (e->err != 0)
				fprintf(log, "\e[91m%s (%d)\e[0m\n",
					errnoname(e->err), e->err);
			else
				fprintf(log, "\e[92m%s (%d)\e[0m\n",
					errnoname(e->err), e->err);
		
		} else {
			fprintf(json, "\t]");
			if (n < event_vec.len - 1)
				fprintf(json, ",\n\t[\n");
			else
				fprintf(json, "\n");
			fprintf(log, "iter %d finished.\n", count);
			count++;
		}
	}
	fprintf(json, "]\n");
	fclose(log);
	fclose(json);
	free(jsonpath);
}

void get_random_bytes(size_t len, char *buffer)
{
	int rand_fd = open("/dev/urandom", O_RDONLY);
	if (rand_fd < 0)
		return;

	read(rand_fd, buffer, len);
	close(rand_fd);
}

int main(int argc, char **argv)
{
	const int iters = 1000;
	const int n_workers = 4;
	const size_t dsize = 16384;
	const char *filename = "./test_file";
	const char *dirname = "./test_dir";
	const char *logfile = "./test.log";
	struct worker_arg params[n_workers];
	pthread_t threads[n_workers];
	pthread_attr_t tattrs;

	init();

	/* Populate attributes and args */
	pthread_attr_init(&tattrs);
	for (int i = 0; i < n_workers; ++i) {
		params[i].worker_id = i;
		params[i].dirname = dirname;
		params[i].filename = filename;
		params[i].data = malloc(dsize);
		params[i].dsize = dsize;
		assert(params[i].data);
		get_random_bytes(dsize, params[i].data);
		pthread_create(&threads[i], &tattrs, worker, &params[i]);
	}

	for (int i = 0; i < iters && !stop; ++i) {
		for (int n = 0; n < n_workers; ++n) {
			pthread_create(&threads[n], &tattrs, worker, &params[n]);
		}

		for (int n = 0; n < n_workers; ++n) {
			pthread_join(threads[n], NULL);
		}

		cleanup_state(&params[0]);
		add_event("iter_end", 0, 0, -1, "");
	}
	
	for (int i = 0; i < n_workers; ++i)
		free(params[i].data);
	output_events(logfile);
	cleanup();
}
