"""
Verifier iterates over trace symbols and check p->c, c->c, p->c, p->p endges.

Use:
python3 verifier.py
Inputs:
Input is log2.txt & model.hoa by default.
"""

import spot
import sys

def checkAutomata(curState : int, nxtState : int, file='model.hoa') -> bool:
  aut = spot.automaton(file)
  for s in range(aut.num_states()):
    for t in aut.out(s):
      if int(t.src) == curState and int(t.dst) == nxtState:
        return True
  return False

def sym2St(sym) -> int:
  if sym == 'p':
	  return 0
  if sym == 'c':
	  return 1
  raise RuntimeError('unknown state')

def processResult(result, idx, length, curState, nextState):
	if not result:
		print(f'Error at symbols {idx+1} in [1, {length}]: {curState} --> {nextState}')
		return False
	return True

def checkSymbols(string: str) -> bool:
	assert(len(string) >= 2 and len(string) % 2 == 0)
	cur = string[0]
	nxt = string[1]
	for i in range(1, len(string[1:])):
		cur = string[i]
		nxt = string[i+1]
		result = checkAutomata(sym2St(cur), sym2St(nxt))
		assert(processResult(result, i, len(string), cur, nxt) == True)

def testTrace(file = 'log2.txt'):
	with open(file, '+r') as f:
		line = f.readline()
		while(f.readline()):
			print('Wrong log configuration')
			exit(2)
		return checkSymbols(line)


if (testTrace()):
	exit(0)
else:
	exit(1)

