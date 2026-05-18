#include<iostream>
#include<fstream>
#include<string>

auto inline is_valid(long long n) -> bool {
	long long ref = n;
	int length = 0;
	while(ref){++length; ref /= 10;};
	if(length % 2){return false;};
	int half = length / 2;
	long long base = 1;
	while(half){base *= 10;--half;};
	return n / base == n % base;
};

auto main() -> int{
	std::string file_name = "2-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		std::getline(read_stream, line);
		const int n = line.size();
		line.push_back(',');
		int i {};
		long long res{};
		int ref {};
		while(i < n){
			std::cout << "On range: " << ref << "\n";
			int r = line.find('-', i);
			long long start = std::stol(line.substr(i, r - i));
			i = r + 1;
			r = line.find(',', i);
			long long end = std::stol(line.substr(i, r - i));
			for(long long j = start; j < end + 1; ++j){
				if(is_valid(j)){res += j;};
			};
			i = r + 1;
			++ref;
		};
		std::cout << "Sum Invalid IDs: " << res << "\n";
		read_stream.close();
	};
	return 0;
};
