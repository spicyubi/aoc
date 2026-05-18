#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
#include<unordered_set>
#include<cstring>


static constexpr int ref_size = 141;
long long dp[ref_size][ref_size];
auto inline dfs(const std::vector<std::string>& graph, int r, int c) -> long long {
	if(r == graph.size()){return 1;};
	if(dp[r][c] != -1){return dp[r][c];};
	long long val = graph[r][c] == '^' ? dfs(graph, r + 1, c - 1) + dfs(graph, r + 1, c + 1) : dfs(graph, r + 1, c);
	dp[r][c] = val;
	return val;

};

auto main() -> int{
	std::memset(dp, -1, sizeof(dp));
	std::string file_name = "7-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		std::getline(read_stream, line);
		const int n = line.size();
		int i{};
		while(line[i] != 'S'){++i;};

		std::vector<std::string> graph;
		while(std::getline(read_stream, line)){
			graph.emplace_back(line);
		};

		std::cout << "starting: " << i  << "\n";
		long long total = dfs(graph, 0, i);
		std::cout << "Total paths: " << total  << "\n";
		// std::cout << graph.size() << "\n";
		// std::cout << graph.front().size() << "\n";
		read_stream.close();
	};
	return 0;
};
