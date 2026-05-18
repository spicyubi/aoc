#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>


static constexpr std::pair<int,int> dirs[8] = {{-1,-1}, {-1, 0}, {-1, 1}, {0, -1}, {0, 1}, {1, -1}, {1, 0}, {1, 1}};
auto inline get_count(const std::vector<std::string>& graph, int m, int n, int r, int c) -> int {
	int total {};
	for(auto const& dir: dirs){
		int next_r = r + dir.first, next_c = c + dir.second;
		if(next_r > -1 && next_r < m && next_c > -1 && next_c < n && graph[next_r][next_c] == '@'){++total;};
	};
	return total;
};
auto main() -> int{
	std::string file_name = "4-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	std::vector<std::string> graph;
	if(read_stream.is_open()){
		std::string line;
		while(std::getline(read_stream, line)){
			graph.emplace_back(line);
		};
		read_stream.close();
	};
	const int m = graph.size(), n = graph.front().size();
	int leader = 0, prev = -1;
	const int limit = 4;
	int loops {};
	while(prev != leader){
		std::cout << "On loop: " << loops << "\n"; 
		prev = leader;
		for(int r{}; r < m; ++r){
			for(int c{}; c < n; ++c){
				if(graph[r][c] == '@'){
					int adjacent = get_count(graph, m, n, r, c);
					if(adjacent < limit){
						++leader;
						graph[r][c] = '.';
					};
				};
			};
		};
		++loops;
	};
	std::cout << "Total reachable rolls: " << leader << "\n";
	return 0;
};
