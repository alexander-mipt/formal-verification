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
			symbols1.add(s)
		else:
			symbols2.add(s)
	return symbols1 == symbols2

def testTrace(file: str):
	with open(file, '+r') as f:
		line = f.readline()
		while(f.readline()):
			print('Wrong log configuration')
			exit(2)
		return checkSymbols(line)


if (testTrace('log.txt')):
	print('OK')
	exit(0)
else:
	print('ERROR')
	exit(1)

