#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
auto main() -> int{
	std::string file_name = "6-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	std::vector<std::vector<long long>> groups;
	if(read_stream.is_open()){
		std::string line;
		while(std::getline(read_stream, line) && line.front() != '+' & line.front() != '*'){
			const int n = line.size();
			std::vector<long long> group;
			int i{};
			while(i < n){
				int end = line.find(' ', i);
				if(end == std::string::npos){
					group.push_back(std::stol(line.substr(i)));
					i = n;
				} else {
					group.push_back(std::stol(line.substr(i, end - i)));
					while(line[end] == ' '){++end;};
					i = end;
				};
			};
			groups.emplace_back(group);
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

		for(const std::vector<long long>& group: groups){
			for(int j{}; j < m; ++j){
				// std::cout << res[j] << " " <<  operations[j] << " " << group[j] << "\n";
				if(operations[j] == '+'){res[j] += group[j];}
				else {res[j] *= group[j];};
			};
		};
		long long total {};
		for(const long long& j: res){total += j;};
		std::cout << "Total: " << total << "\n";
		read_stream.close();
	};
	return 0;
};
