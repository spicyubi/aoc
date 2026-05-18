#include<iostream>
#include<fstream>
#include<string>

auto inline is_valid(long long n) -> bool {
	long long ref = n;
	int length = 0;
	while(ref){++length; ref /= 10;};
	if(length == 1){return false;};
	int base;
	if(length % 2){
		ref = n;
		base = ref % 10;
		while(ref && base == ref % 10){ref /= 10;};
		if(ref == 0){return true;};
		if(length != 9){return false;};
		ref = n;
		base = ref % 1000;
		while(ref && base == ref % 1000){ref /= 1000;};
		return ref == 0;
	};
	int half = length / 2;
	base = 1;
	while(half){base *= 10;--half;};
	if(n / base == n % base){return true;};
	if(length == 6 || length == 10){
		ref = n;
		base = ref % 100;
		while(ref && base == ref % 100){ref /= 100;};
		if(ref == 0){return true;};
	};
	return false;
};

auto main() -> int{
	// long long test = 2121212121;
	// std::cout << "is valid: " << test << "-> " << (is_valid(test) ? "yes" : "no") << "\n";
	std::string file_name = "2-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		std::getline(read_stream, line);
		const int n = line.size();
		line.push_back(',');
		int i {};
		long long res{};
		// int ref {};
		while(i < n){
			// std::cout << "On range: " << ref << "\n";
			int r = line.find('-', i);
			long long start = std::stol(line.substr(i, r - i));
			i = r + 1;
			r = line.find(',', i);
			long long end = std::stol(line.substr(i, r - i));
			for(long long j = start; j < end + 1; ++j){
				if(is_valid(j)){res += j;};
			};
			i = r + 1;
			// ++ref;
		};
		std::cout << "Sum Invalid IDs: " << res << "\n";
		read_stream.close();
	};
	return 0;
};
