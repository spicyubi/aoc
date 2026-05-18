#include<iostream>
#include<fstream>
#include<string>

auto main() -> int {
	static constexpr int init_pos = 50, k = 100;
	int current_pos = init_pos;
	int res {}, base{};
	std::string file_name = "1-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		line.reserve(4);
		while(std::getline(read_stream, line)){
			int magnitude = std::stoi(line.substr(1));;
			res += magnitude / k;
			magnitude %= k;
			if(line.front() == 'R'){
				if(current_pos != 0 && current_pos + magnitude >= k){++res;};
				current_pos = (current_pos + magnitude) % k;
			} else {
				if(current_pos != 0 && current_pos - magnitude <= 0){++res;};
				current_pos = (current_pos - magnitude + k) % k;
			};
			if(current_pos == 0){++base;};
		};
		std::cout << base << " is the base\n";
		std::cout << res << " is the password\n";
		read_stream.close();
	}
	return 0;
};
