#include<iostream>
#include<fstream>
#include<string>

auto main() -> int{
	std::string file_name = "3-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		long long res {};
		const int target_count = 12;
		while(std::getline(read_stream, line)){
			int n = line.size();
			char current = line[0];
			long long base = 1e11;
			int i = n - target_count, prev = -1;
			long long total = 0;
			for(int i = n - target_count; i < n; ++i){
				int index = i, mark = i;
				char leader = line[i];
				while(index > prev){
					if(line[index] >= leader){
						leader = line[index];
						mark = index;
					};
					--index;
				};
				prev = mark;
				total += base * (leader - '0');
				base /= 10;
			};
			res += total;
		};
		std::cout << "Final sum: " << res << "\n";
		read_stream.close();
	};
	return 0;
};
