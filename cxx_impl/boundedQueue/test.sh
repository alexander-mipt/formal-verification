#!/bin/bash

clang++-15 -std=c++20 -pthread -latomic -fsanitize=thread main.cc

for i in {1..100}; do
	./a.out &> log.txt
	python3 test.py
	python3 test2.py > log2.txt
	python3 verifier.py
done
