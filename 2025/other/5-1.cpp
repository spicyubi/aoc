#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
auto main() -> int{
	std::string file_name = "5-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	std::vector<std::string> graph;
	std::vector<std::pair<long long, long long>> fresh_ranges;
	std::function<bool(const std::pair<long long, long long>&, const std::pair<long long, long long>&)> comp = [](const std::pair<long long, long long>& a, const std::pair<long long, long long>& b) -> bool {return a.first < b.first || (a.first == b.first && a.second < b.second);};
	if(read_stream.is_open()){
		std::string line;
		while(std::getline(read_stream, line) && !line.empty()){
			int partition = line.find('-');
			fresh_ranges.push_back({std::stol(line.substr(0, partition)), std::stol(line.substr(partition + 1))});
		};

		std::sort(fresh_ranges.begin(), fresh_ranges.end(), comp);
		long long prev {};
		long long total {};
		for(const auto& range: fresh_ranges){
			if(range.second > prev){
				total += range.second - range.first + 1;
				if(range.first <= prev){total -= prev - range.first + 1;};
				prev = range.second;
			};
		};
		std::cout << "Total Fresh: " << total << "\n";
		read_stream.close();
	};
	return 0;
};
