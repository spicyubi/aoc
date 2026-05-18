#include<iostream>
#include<fstream>
#include<string>
#include<vector>
#include<utility>
#include<functional>
#include<unordered_set>
#include<cstring>
#include<queue>



auto inline get_distance(int x1, int y1, int z1, int x2, int y2, int z2) -> long long {
	return 1ll * (x2 - x1) * (x2 - x1) + 1ll * (y2 - y1) * (y2 - y1) + 1ll * (z2 - z1) * (z2 - z1);
};

auto inline find(std::vector<int>& par, int node) -> int {
	int chain {}, res = node;
	while(res != par[res]){
		++chain;
		res = par[res];
	};
	for(int i = 1; i < chain; ++i){
		int nxt = par[node];
		par[node] = res;
		node = nxt;
	};
	return res;
};
auto main() -> int{
	std::string file_name = "8-1.txt";
	// std::string file_name = "test.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		std::vector<std::pair<int, std::pair<int,int>>> boxes;
		while(std::getline(read_stream, line)){
			int first_comma = line.find(',', 0);
			int second_comma = line.find(',', first_comma + 1);
			boxes.push_back({ std::stoi(line.substr(0, first_comma)), { std::stoi(line.substr(first_comma + 1, second_comma - first_comma - 1)), std::stoi(line.substr(second_comma + 1))} });
		};

		std::vector<std::pair<long long, std::pair<int, int>>> graph;
		const int n = boxes.size();
		for(int i{}; i < n - 1; ++i){
			int x1 = boxes[i].first, y1 = boxes[i].second.first, z1 = boxes[i].second.second;
			for(int j = i + 1; j < n; ++j){
				int x2 = boxes[j].first, y2 = boxes[j].second.first, z2 = boxes[j].second.second;
				long long distance = get_distance(x1,y1,z1,x2,y2,z2);
				graph.push_back({distance, {i, j}});
			};
		};

		std::sort(graph.begin(), graph.end());
		std::vector<int> par, rank(n, 1);
		par.reserve(n);
		for(int i{}; i < n; ++i){
			par.push_back(i);
		};

		int m = n;
		int k {};
		while(m > 1){
			const auto& g = graph[k];
			int a = find(par, g.second.first), b = find(par, g.second.second);
			if(a != b){
				--m;
				if(rank[a] > rank[b]){
					rank[a] += rank[b];
					par[b] = a;
				} else {
					rank[b] += rank[a];
					par[a] = b;
				};
			};
			++k;
		};
		--k;


		int x_first = boxes[graph[k].second.first].first, x_second = boxes[graph[k].second.second].first;
		std::cout << " Result: " << x_first << " * " << x_second << " = " << 1ll * x_first * x_second << "\n";
		read_stream.close();
	};
	return 0;
};
