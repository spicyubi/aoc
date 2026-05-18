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
#include<numeric>

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

auto inline parse(const std::string& line, std::vector<std::vector<int>>& buttons, std::vector<int>& power) -> void {
	// Parse part 1
	int i = 1;
	while(line[i] != ']'){
		++i;
	};
	int bit_length = i - 1;

	// Parse part 2
	i = line.find('(', i);
	int end;
	while(i != std::string::npos){
		++i;
		end = i;
		bool end_parenthesis = false;
		std::vector<int> button;
		button.reserve(15);
		while(!end_parenthesis){
			while(line[end] != ',' && line[end] != ')'){++end;};
			button.push_back(std::stoi(line.substr(i, end - i)));
			if(line[end] == ')'){end_parenthesis = true;};
			i = ++end;
		};
		i = line.find('(', i + 1);
		buttons.push_back(button);
	};

	// Parse part 3
	power.reserve(bit_length);
	i = line.find('{', end) + 1;
	end = i;
	bool end_parenthesis = false;
	while(!end_parenthesis){
		while(line[end] != ',' && line[end] != '}'){++end;};
		power.push_back(std::stoi(line.substr(i, end - i)));
		if(line[end] == '}'){end_parenthesis = true;};
		i = ++end;
	};
};

auto inline swap_columns(std::vector<std::vector<int>>& A, int a, int b) -> void {
	if(a == b){return;};
	for(int r {}; r < A.size(); ++r){
		int tmp = A[r][a];
		A[r][a] = A[r][b];
		A[r][b] = tmp;
	};
};

auto inline modified_gaussian_elimination(std::vector<std::vector<int>>& A, std::vector<int>& pivots) -> void {
	const int m = A.size(), n = A.front().size();
	int end = n - 2;
	bool pivot_exists = true;
	for(int row {}, pivot {}; row < m && pivot <= end && pivot_exists; ++row){
		// Find pivot and swap columns and rows
		auto& pivot_row = A[row];
		pivot_exists = pivot_row[pivot] != 0;
		while(!pivot_exists && pivot <= end){
			for(int r = row; !pivot_exists && r < m; ++r){
				if(A[r][pivot] != 0){
					std::swap(pivot_row, A[r]);
					pivot_exists = true;
				};
			};
			if(!pivot_exists){swap_columns(A, pivot, end--);};
		};

		// for(const auto& v: A){print_vector(v);};
		// std::cout << "\n\n";

		if(pivot_exists){
			pivots.push_back(pivot);
			// Make sure pivot positive
			if(pivot_row[pivot] < 0){
				for(int c = pivot; c < n; ++c){
					pivot_row[c] *= -1;
				};
			};

			// Make all values below pivot 0
			for(int r = row + 1; r < m; ++r){
				if(A[r][pivot] != 0){
					int standard = pivot_row[pivot] * A[r][pivot] / std::gcd(pivot_row[pivot], A[r][pivot]);
					int pivot_factor = standard / pivot_row[pivot];
					int row_factor = standard / A[r][pivot];
					for(int c = pivot; c < n; ++c){
						A[r][c] = A[r][c] * row_factor - pivot_row[c] * pivot_factor;
					};
				};
			};
			++pivot;
		};

	};
};

auto inline unique_back_substitution(const int n, const std::vector<std::vector<int>>& A, const std::vector<int>& pivots) -> int {
	int total {};
	std::cout << "Pivots:\n";
	print_vector(pivots);
	std::vector<int> X(A.front().size() - 1, 0);
	for(int pivot = pivots.size() - 1; pivot > -1; --pivot){
		const std::vector<int>& pivot_row = A[pivot];
		const int factor = pivot_row[pivot];
		long long res = pivot_row[n - 1];
		for(int c = pivot + 1; c < n - 1; ++c){
			res -= 1ll * pivot_row[c] * X[c];
		};
		res /= factor;
		X[pivot] = res;
		total += res;
	};
	print_vector(X);
	return total;
};

auto inline ceil_div(int a, int b) -> int {
	int q = a / b;
	if(a % b == 0){return q;};
	return ++q;
};
auto inline dfs(const int n, const std::vector<std::vector<int>>& A, const std::vector<int>& pivots, std::vector<int>& X, int pivot_ptr, int x_var, int total, int max_power) -> int {
	if(x_var == -1){return total;};
	const std::vector<int>& pivot_row = A[pivot_ptr];
	int pivot = pivots[pivot_ptr];
	if(x_var == pivot){
		const int factor = pivot_row[x_var];
		int res = pivot_row[n - 1];
		for(int c = pivot + 1; c < n - 1; ++c){
			res -= pivot_row[c] * X[c];
		};
		res /= factor;
		if(res < 0){return -1;};
		X[x_var] = res;
		return dfs(n, A, pivots, X, pivot_ptr - 1, x_var - 1, total + res, max_power);
	};

	int left_bound = 0, right_bound = max_power - total;
	// for(int r = pivot_ptr; r > -1; --r){
	// 	if(A[r][x_var] != 0){
	// 		const std::vector<int>& free_var_row = A[r];
	// 		bool is_right_bound = free_var_row[x_var] > 0;
	// 		const int factor = free_var_row[x_var];
	// 		int res = free_var_row[n - 1];
	// 		for(int c = pivot + 1; c < n - 1; ++c){
	// 			if(c != x_var){
	// 				res -=  free_var_row[c] * X[c];
	// 			};
	// 		};
	// 		// if(res % factor != 0){std::cout << "ISSUE\n";};
	// 		res = is_right_bound ? res / factor: ceil_div(res, factor);
	// 		if(is_right_bound){
	// 			if(res < right_bound){right_bound = res;};
	// 		} else {
	// 			if(res > left_bound){left_bound = res;};
	// 		};
	// 	};
	// };

	std::cout << "Variable: X-" << x_var << " : [" << left_bound << ", " << right_bound << "]\n";
	int leader = INT_MAX;
	for(int i = left_bound; i < right_bound + 1; ++i){
		X[x_var] = i;
		int val = dfs(n, A, pivots, X, pivot_ptr, x_var - 1, total + i, max_power);
		if(val != -1 && val < leader){leader = val;print_vector(X);};
	};
	return leader;
};

auto inline multi_back_substitution(const int n, const std::vector<std::vector<int>>& A, const std::vector<int>& pivots, const std::vector<int>& power) -> int {
	int total {};
	int max_power = power.front();
	for(auto it = power.begin(); it != power.end(); ++it){max_power = std::max(max_power, *it);};
	std::cout << "\n";
	std::cout << "Pivots:\n";
	print_vector(pivots);
	std::vector<int> X(n - 1, -1);
	int init_pivot_ptr = pivots.size() - 1;
	return dfs(n, A, pivots, X, init_pivot_ptr, n - 2, total, max_power);
};

auto main() -> int{
	// std::string file_name = "10-1.txt";
	// std::string file_name = "test.txt";
	std::string file_name = "test2.txt";
	std::ifstream read_stream(file_name, std::ios::in);
	if(read_stream.is_open()){
		std::string line;
		int total {};
		while(std::getline(read_stream, line)){
			// Generate Augmented A matrix
			std::vector<std::vector<int>> buttons;
			std::vector<int> power;
			parse(line, buttons, power);
			const int m = power.size(), n = buttons.size() + 1;
			std::vector<std::vector<int>> A(m, std::vector<int>(n, 0));
			for(int c{}; c < n - 1; ++c){
				const std::vector<int>& button = buttons[c];
				for(const int r: button){
					A[r][c] = 1;
				};
			};

			for(int r {}; r < m; ++r){A[r][n -1] = power[r];};


			std::vector<int> pivots;
			pivots.reserve(m);

			std::cout << "START:\n";
			for(const auto& v: A){print_vector(v);};
			std::cout << "\n";

			modified_gaussian_elimination(A, pivots);

			std::cout << "\nFINAL:\n";
			for(const auto& v: A){print_vector(v);};

			int val = pivots.size() == n - 1 ? unique_back_substitution(n, A, pivots): multi_back_substitution(n, A, pivots,power);
			if(pivots.size() == n - 1){
				std::cout << "UNIQUE SOLUTION DETECTED\n";
			} else {
				std::cout << "FREE VARIABLES DETECTED\n";
			};
			std::cout << val << " presses\n";
			std::cout << "\n\n";


			total += val;
			
		};
		std::cout << "Result: " << total << " presses \n";
		read_stream.close();
	};
	return 0;
};
