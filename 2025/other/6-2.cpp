#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
auto main() -> int{
	std::string file_name = "6-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	static constexpr int og_cols = 3748;
	std::string groups[og_cols];
	if(read_stream.is_open()){
		std::string line;
		while(std::getline(read_stream, line) && line.front() != '+' & line.front() != '*'){
			for(int i{}; i < og_cols; ++i){
				if(line[i] != ' ' ){groups[i].push_back(line[i]);};
			};
		};
		std::vector<char> operations;
		int i{};
		const int n = line.size();
		while(i < n){
			operations.push_back(line[i]);
			++i;
			while(i < n && line[i] == ' '){++i;};
		};

		const int m = operations.size();
		std::vector<long long> res(m, 0);
		for(int j{}; j < m; ++j){if(operations[j] == '*'){res[j] = 1;};};

		i = 0;
		for(int j{}; j < m; ++j){
			const char operation = operations[j];
			if(operation == '*'){
				while(i < og_cols && groups[i].size() > 0){
					res[j] *= std::stol(groups[i]);
					++i;
				};
			} else {
				while(i < og_cols && groups[i].size() > 0){
					res[j] += std::stol(groups[i]);
					++i;
				};

			};
			++i;
		};

		long long total {};
		for(const long long& val: res){total += val;};
		std::cout << "Total: " << total;
		read_stream.close();
	};
	return 0;
};
