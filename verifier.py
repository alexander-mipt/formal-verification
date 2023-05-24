import spot
import sys

def check(curState : int, nxt : int, file) -> bool:
  aut = spot.automaton(file)
  for s in range(aut.num_states()):
    for t in aut.out(s):
      if int(t.src) == curState and int(t.dst) == nxt:
        return True
  return False

def parseTrace(line) -> int:
  if 'push' in line:
    return 0
  if 'pop' in line:
    return 1
  raise RuntimeError('unknown state')

if __name__ == '__main__':
  assert(len(sys.argv) == 3)

  model_file = sys.argv[2] # .hoa
  trace = open(sys.argv[1], "r").readlines() # trace.log
  counters = [0, 0] # push , pop
  curState = parseTrace(trace[0])

  # first should be only store.
  assert(curState == 0)
  counters[curState] += 1

  for line in trace[1:]:
    state = parseTrace(line)
    counters[state] += 1
    assert(check(curState, state, model_file) == True)
    curState = state

  # last should be only pop.
  assert(curState == 1)
  # counters of push and pop are equal.
  assert(counters[0] == counters[1])
