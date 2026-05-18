#include<iostream>
#include<fstream>
#include<string>

auto main() -> int{
	std::string file_name = "3-1.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		short total {};
		while(std::getline(read_stream, line)){
			int n = line.size();
			char first = '0', second = '0';
			int i = 0;
			while(i < n){
				if(line[i] > first && i < n - 1){
					first = line[i];
					second = line[i + 1];
				} else if(line[i] > second) {second = line[i];};
				if(first == '9' && second == '9'){i = n;};
				++i;
			};
			short val = (first - '0') * 10 + (second - '0');
			total += val;
			// std::cout << line << "\n";
			// std::cout << "'" << first << second << "'\n";
			// std::cout << val << "\n";
			// std::cout << "Running Total: " << total << "\n\n";
		};
		std::cout << "Final sum: " << total << "\n";
		read_stream.close();
	};
	return 0;
};
