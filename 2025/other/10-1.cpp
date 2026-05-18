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
#include<climits>

auto inline get_count(const std::vector<int>& buttons, int target, int total, int val, int i) -> int {
	if(val == target){return total;};
	if(i == buttons.size()){return -1;};
	int a = get_count(buttons, target, total, val, i + 1);
	int b = get_count(buttons, target, total + 1, val ^ buttons[i], i + 1);
	return std::min(a == -1 ? INT_MAX: a, b == -1 ? INT_MAX: b);
};

auto main() -> int{
	std::string file_name = "10-1.txt";
	// std::string file_name = "test.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		int total {};
		while(std::getline(read_stream, line)){
			int target {};
			int i = 1;
			while(line[i] != ']'){
				target <<= 1;
				if(line[i] == '#'){
					target ^= 1;
				};
				++i;
			};
			int bit_length = i - 1;
			// std::cout << "Target: " << target << "\n";

			i = line.find('(', i);
			std::vector<int> buttons;
			while(i != std::string::npos){
				++i;
				int end = i;
				bool end_parenthesis = false;
				int button {};
				while(!end_parenthesis){
					while(line[end] != ',' && line[end] != ')'){++end;};
					int shifts = bit_length - std::stoi(line.substr(i, end - i)) - 1;
					int partial = 1;
					for(int j {}; j < shifts; ++j){partial <<= 1;};
					button ^= partial;
					if(line[end] == ')'){end_parenthesis = true;};
					i = ++end;
				};
				// std::cout << "Button: " << button << "\n";
				i = line.find('(', i + 1);
				buttons.push_back(button);
			};

			
			int leader = get_count(buttons, target, 0, 0, 0);
			total += leader;
			// std::cout << leader << " presses\n\n";

		};
		std::cout << "Result: " << total << " presses \n";
		read_stream.close();
	};
	return 0;
};
