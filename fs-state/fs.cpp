#include<iostream>
#include<vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

using namespace std;
struct FileState{
	string _path;
	bool _isOpen;
	int _flag;
	int _fd;
	int _pos;
	FileState(string path, int flag, int fd){
		_path = path;
		_isOpen = true;
		_flag = flag;
		_fd = fd;
		_pos = 0;
	}
	void printme(){
		cout<<"Path : "<<_path<<" isOpen : "<<_isOpen<<" flag : "<<_flag<<" fd : "<<_fd<<" _pos : "<<_pos<<endl;
	}

};
vector<FileState> fslist;

void my_open(string path, int flag){
	int fd = open(path.c_str(), flag);
	FileState fs = FileState(path,flag,fd);
	fs.printme();
	fslist.push_back(fs);
}

int main(){
	my_open("hello.txt", O_CREAT);
	cout<<"fslist size "<<fslist.size();
	return 0;
}