#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<cstring>
#include<unordered_map>

template <typename T>
auto inline print_vector(const T& vec) -> void {
	for(auto it = vec.begin(); it != vec.end(); ++it){
		if(it != vec.end() - 1){
			std::cout << *it << "\t";
		} else {
			std::cout << *it << "\n";;
		};
	};
};

long long dp[26][26][26][2][2];
std::unordered_map<std::string, std::vector<std::string>> graph;
auto inline parse(const std::string& line) -> void {
	static constexpr int max_number_of_childs = 21, child_size = 3, starting_pos = 0;
	std::string key = line.substr(starting_pos, child_size);
	std::vector<std::string>& children = graph[key];
	children.reserve(max_number_of_childs);
	const int n = line.size();
	int i = 5;
	while(i < n){
		children.push_back(line.substr(i, child_size));
		i += 4;
	};
};

static constexpr int end_point_a = 'o' - 'a', end_point_b = 'u' - 'a', end_point_c = 't' - 'a';
static constexpr int dac_a = 'd' - 'a', dac_b = 'a' - 'a', dac_c = 'c' - 'a';
static constexpr int fft_a = 'f' - 'a', fft_b = 'f' - 'a', fft_c = 't' - 'a';
auto inline dfs(const std::string& key, bool passed_dac, bool passed_fft) -> long long {
	int a = key[0] - 'a', b = key[1] - 'a', c = key[2] - 'a';
	if(a == end_point_a && b == end_point_b && c == end_point_c){return passed_dac && passed_fft ? 1: 0;};
	if(dp[a][b][c][passed_dac][passed_fft] > -1){return dp[a][b][c][passed_dac][passed_fft];};
	if(!passed_dac && dac_a == a && dac_b == b && dac_c == c){passed_dac = true;};
	if(!passed_fft && fft_a == a && fft_b == b && fft_c == c){passed_fft = true;};
	long long val {};
	for(const std::string& node: graph[key]){val += dfs(node, passed_dac, passed_fft);};
	dp[a][b][c][passed_dac][passed_fft] = val;
	return val;
};

auto main() -> int{
	std::memset(dp, -1, sizeof(dp));
	static constexpr int max_line_size = 88;
	std::string file_name = "11.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		// Parse
		std::string line;
		line.reserve(max_line_size);
		while(std::getline(read_stream, line)){parse(line);};
		read_stream.close();

		// Solve
		std::string init_start = "svr";
		bool init_passed_dac = false, init_passed_fft = false;
		std::cout << "Result: " << dfs(init_start, init_passed_dac, init_passed_fft) << " paths from svr to out\n";
	};
	return 0;
};
