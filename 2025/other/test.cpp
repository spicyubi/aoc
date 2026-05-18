#include<iostream>
struct A {
	A() {std::cout << "1\n";};
	A(const A& a) {std::cout << "2\n";};
	virtual void f() {std::cout << "3\n";};
};
auto main() -> int {
	int b[3];
	for(const auto& i: b){
		std::cout << i << "\n";
	};
	A a[2];
	for(auto x: a){
		x.f();
	};
	return 0;
};
