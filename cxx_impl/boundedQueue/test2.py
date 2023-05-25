"""
Queue task data is a single unique readale character ('!' or ':' for example).
Test Iterates over trace symbols and check that each symbol has only one sibling.
It emulates transmiter & reciever invarinat.

Use:
python3 test.py
Inputs:
Input is log.txt by default.
"""

def checkSymbols(string: str) -> bool:
	symbols1 = set()
	symbols2 = set()
	for s in string:
		if s not in symbols1:
			if s in symbols1:
				return False
			symbols1.add(s)
			print('p', end='')
		else:
			if s in symbols2:
				return False
			symbols2.add(s)
			print('c', end='')
	return symbols1 == symbols2

def testTrace(file: str):
	with open(file, '+r') as f:
		line = f.readline()
		while(f.readline()):
			print('Wrong log configuration')
			exit(2)
		return checkSymbols(line)


if (testTrace('log.txt')):
	exit(0)
else:
	exit(1)

