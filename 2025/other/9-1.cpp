#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
#include<unordered_set>
#include<cstring>
#include<queue>
#include<cstdlib>

auto main() -> int{
	std::string file_name = "9-1.txt";
	// std::string file_name = "test.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::vector<std::pair<int, int>> points;
		std::string line;
		while(std::getline(read_stream, line)){
			int comma_pos = line.find(',');
			points.push_back({std::stoi(line.substr(0, comma_pos)), std::stoi(line.substr(comma_pos + 1))});
		};

		const int n = points.size();
		long long leader {};
		for(int i{}; i < n - 1; ++i){
			int x1 = points[i].first, y1 = points[i].second;
			for(int j = i + 1; j < n; ++j){
				int x2 = points[j].first, y2 = points[j].second;
				long long area = 1ll * (std::abs(x2 - x1) + 1) * (std::abs(y2 - y1) + 1);
				if(area > leader){leader = area;};
			};
		};
		std::cout << "Result: " << leader << "\n";
		read_stream.close();
	};
	return 0;
};
