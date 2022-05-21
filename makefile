
test : test.cpp
	rm test -f
	g++ test.cpp -o test
	./test
	rm test -f
