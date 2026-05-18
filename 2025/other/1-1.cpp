#include<iostream>
#include<fstream>
#include<string>

auto main() -> int {
	static constexpr short init_pos = 50, k = 100;
	short current_pos = init_pos;
	short res {};
	std::string file_name = "1-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		line.reserve(4);
		while(std::getline(read_stream, line)){
			current_pos = line.front() == 'R' ? 
				(current_pos + std::stoi(line.substr(1, line.size() - 1))) % k :
				(current_pos - std::stoi(line.substr(1, line.size() - 1)) + k) % k;
			if(!current_pos){++res;};
		};
		std::cout << res << " is the password\n";
		read_stream.close();
	}
	return 0;
};
