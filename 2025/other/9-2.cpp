#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
#include<set>
#include<unordered_set>
#include<unordered_map>
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
		std::set<int> row_set, col_set;
		std::unordered_map<int, int> row_map, col_map;
		while(std::getline(read_stream, line)){
			int comma_pos = line.find(',');
			int a = std::stoi(line.substr(0, comma_pos)), b = std::stoi(line.substr(comma_pos + 1));
			points.push_back({b, a});
			row_set.insert(b);
			col_set.insert(a);
		};

		int index {};
		for(auto it = row_set.begin(); it != row_set.end(); ++it){
			row_map[*it] = index;
			++index;
		};

		const int m = index;
		index = 0;
		for(auto it = col_set.begin(); it != col_set.end(); ++it){
			col_map[*it] = index;
			++index;
		};

		const int n = index;
		std::vector<std::vector<int>> grid(m, std::vector(n, 0));
		std::vector<std::vector<int>> prefix = grid;

		points.emplace_back(points.front());
		const int k = points.size();
		for(int i{}; i < k - 1; ++i){
			int r1 = row_map[points[i].first], c1 = col_map[points[i].second];
			int r2 = row_map[points[i + 1].first], c2 = col_map[points[i + 1].second];
			if(c1 == c2){
				int top_r = std::min(r1, r2);
				int bot_r = std::max(r1, r2);
				grid[top_r][c1] = 1;
				grid[bot_r][c1] = 2;
				for(int r = top_r + 1; r < bot_r; ++r){
					grid[r][c1] = 3;
				};
			};
		};

		// Generate 2-D prefix length
		for(int r{}; r < m; ++r){
			int prefix_xor {};
			for(int c{}; c < n; ++c){
				// std::cout << grid[r][c] << "  ";
				int top = r == 0 ? 0: prefix[r - 1][c];
				int left = c == 0 ? 0: prefix[r][c - 1];
				int diag = r == 0 || c == 0 ? 0: prefix[r - 1][c - 1];
				prefix[r][c] = grid[r][c] > 0 || prefix_xor > 0 ? 1 + top + left - diag: top + left - diag;
				prefix_xor ^= grid[r][c];
			};
			// std::cout << "\n";
		};


		// Sanity Check Prefix Grid
		// std::cout << "\n";
		// for(int r{}; r < m; ++r){
		// 	for(int c{}; c < n; ++c){
		// 		std::cout << prefix[r][c] << "  ";
		// 	};
		// 	std::cout << "\n";
		// };

		// Find Leader
		long long leader {};
		for(int i{}; i < k - 1; ++i){
			int r1 = row_map[points[i].first], c1 = col_map[points[i].second];
			for(int j = i + 1; j < k; ++j){
				int r2 = row_map[points[j].first], c2 = col_map[points[j].second];
				int min_r = std::min(r1, r2), min_c = std::min(c1, c2), max_r = std::max(r1, r2), max_c = std::max(c1, c2);
				int top = min_r == 0 ? 0 : prefix[min_r - 1][max_c];
				int left = min_c == 0 ? 0 : prefix[max_r][min_c - 1];
				int diag = min_r == 0 || min_c == 0 ? 0: prefix[min_r - 1][min_c - 1];
				long long expected_area = 1ll * (std::abs(c2 - c1) + 1) * (std::abs(r2 - r1) + 1);
				long long actual_area = prefix[max_r][max_c] - top - left + diag;
				if(actual_area == expected_area){
					long long og_area = 1ll * (std::abs(points[i].first - points[j].first) + 1) * (std::abs(points[i].second - points[j].second) + 1);
					leader = std::max(leader, og_area);
				};
			};
		};


		points.pop_back();
		std::cout << "\n";
		std::cout << "Result: " << leader << "\n";
		read_stream.close();
	};
	return 0;
};
