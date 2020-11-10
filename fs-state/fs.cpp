#include <bits/stdc++.h>
#include<iostream>
#include<vector>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include<unistd.h>

using namespace std;
struct FileState{
	string _path;
	bool _isOpen;
	int _flag;
	int _fd;
	long int _pos;
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

int find_idx(string path) {
	auto find_fs = [path](const FileState & fs) {
    		return fs._path == path;
	};
	auto it = find_if(fslist.begin(), fslist.end(), find_fs);
	if(it != fslist.end()) {
		return it - fslist.begin();
	}
	return -1;
}

void my_lseek(string path, int offset, int whence) {
	// find the state of this file
	int idx = find_idx(path);
	int fd = -1, curr_pos = 0;
	if (idx == -1) {
		cout << "File " << path << " not opened\n";
	} else {
		fd = fslist[idx]._fd;
		curr_pos = fslist[idx]._pos;
	}
	lseek(fd, curr_pos + offset, whence);
	// update the current seek position of the opened file.
	if(idx != -1) {
		fslist[idx]._pos = lseek(fslist[idx]._fd, 0, SEEK_CUR);
		fslist[idx].printme();
	}
}

void my_close(string path) {
	int idx = find_idx(path);
	fslist.erase(
        	std::remove_if(fslist.begin(), fslist.end(), [&](FileState const & fs) {
            			return fs._path == path;}), fslist.end());
	if (idx != -1) {
		close(fslist[idx]._fd);
	}
}

int main(){
	string path = "hello.txt";
	my_open(path, O_RDONLY);
	my_lseek(path, 3, SEEK_SET);
        my_close(path);
	cout<<"fslist size "<<fslist.size();
	return 0;
}
