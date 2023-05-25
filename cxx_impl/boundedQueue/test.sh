#!/bin/bash

clang++-15 -std=c++20 -pthread -latomic -fsanitize=thread main.cc

for i in {1..100}; do
	./a.out &> log.txt
	python3 test.py
done
