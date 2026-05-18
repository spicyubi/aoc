#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<cstring>
#include<unordered_map>

auto inline parse(const std::string& line) -> bool {
	int region = std::stoi(line.substr(0, 2)) * std::stoi(line.substr(3, 2));
	const int n = line.size();
	int i = 7, total {};
	while(i < n){
		total += 9 * std::stoi(line.substr(i, 2));
		i += 3;
	};
	return total <= region;
};

auto main() -> int{
	std::string file_name = "12.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		// Parse
		std::string line;
		int total {};
		while(std::getline(read_stream, line)){total += parse(line);};
		read_stream.close();
		std::cout << "Result: " << total << "\n";
	};
	return 0;
};
