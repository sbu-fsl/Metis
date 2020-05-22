#define EXISTS 1
#define NOT_EXISTS 0
#define CURRENT_DIR "./tmp/"
#define TEST_FILE "test.txt"


short test1_created;
short test1_deleted;

void doAbstraction() {
	if(test1_created > 1)
		test1_created  = 1;
	if(test1_deleted > 1)
		test1_deleted = 1;
}
