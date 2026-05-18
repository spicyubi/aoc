#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
#include<unordered_set>
auto main() -> int{
	std::string file_name = "7-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		std::getline(read_stream, line);
		const int n = line.size();
		std::unordered_set<int> beams;
		int i{};
		while(line[i] != 'S'){++i;};
		beams.insert(i);

		int splits {};
		while(std::getline(read_stream, line)){
			std::vector<int> ref {};
			for(const int val: beams){
				ref.push_back(val);
			};
			for(const int val: ref){
				if(line[val] == '^'){
					++splits;
					if(val > 0){beams.insert(val - 1);};
					if(val < n - 1){beams.insert(val + 1);};
					beams.erase(val);
				};
			};
		};

		std::cout << "Total splits: " << splits << "\n";
		read_stream.close();
	};
	return 0;
};
