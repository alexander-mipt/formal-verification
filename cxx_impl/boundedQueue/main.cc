#include <atomic>
#include <chrono>
#include <iostream>
#include <mutex>
#include <thread>
#include <vector>

namespace {

constexpr bool DEF_VERBOSE = false;
constexpr int DEF_BUFSIZE = 64;
constexpr int DEF_NTASKS = 100;
constexpr int DEF_NPROD = 1;
constexpr int DEF_NCONS = 1;
constexpr int DEF_PTIME = 1;
constexpr int DEF_CTIME = 1;

struct Config {
  bool Verbose = DEF_VERBOSE;
  int BufSize = DEF_BUFSIZE;
  int NTasks = DEF_NTASKS;
  int NProd = DEF_NPROD;
  int NCons = DEF_NCONS;
};

} // namespace

namespace {


template <typename T> class lf_queue {
  Config Cfg;

  // using unsigned to allow legal wrap around
  struct CellTy {
    std::atomic<unsigned> Sequence;
    T Data;
  };

  // fixed cyclic buffer
  std::vector<CellTy> Buffer;
  unsigned BufferMask;
  // атомики не гарантируют lock-freenes, однако для большинства современных архитектур они поддержаны на аппаратном уровне
  std::atomic<unsigned> EnqueuePos, DequeuePos;

public:
  lf_queue(Config Cfg)
      : Cfg(Cfg), Buffer(Cfg.BufSize), BufferMask(Cfg.BufSize - 1) {
    if (Cfg.BufSize > (1 << 30))
      throw std::runtime_error("buffer size too large");

    if (Cfg.BufSize < 2)
      throw std::runtime_error("buffer size too small");

    // for increment optimization
    if ((Cfg.BufSize & (Cfg.BufSize - 1)) != 0)
      throw std::runtime_error("buffer size is not power of 2");

    // init ids for solving ABA problem
    for (unsigned i = 0; i != Cfg.BufSize; ++i)
      Buffer[i].Sequence.store(i);
    
    // for simplicity we make seq_ordering
    EnqueuePos.store(0);
    DequeuePos.store(0);
  }

  bool push(T Data) {
    CellTy *Cell;
    unsigned Pos;
    bool Res = false;

    // CAS Loop
    while (!Res) {
      // fetch the current Position where to enqueue the item
      Pos = EnqueuePos.load();
      Cell = &Buffer[Pos & BufferMask];
      auto Seq = Cell->Sequence.load();
      // long time ...........
      // save for ABA problem
      auto Diff = static_cast<int>(Seq) - static_cast<int>(Pos);

      // queue is full we cannot enqueue and just return false
      // another option: queue moved forward all way round
      if (Diff < 0)
        return false;

      // If its Sequence wasn't touched by other producers
      // check if we can increment the enqueue Position
      // CAS: atomic == #0 (expected) --> atomic = #1 (desired)
      //      atomic != #0            --> #0 = atomic
      // weak: может сработать как false при == - логически безвредная операция 
      if (Diff == 0)
        Res = EnqueuePos.compare_exchange_weak(Pos, Pos + 1);
    }

    // write the item we want to enqueue and bump Sequence
    Cell->Data = std::move(Data);
    Cell->Sequence.store(Pos + 1);
    return true;
  }

  bool pop(T &Data) {
    CellTy *Cell;
    unsigned Pos;
    bool Res = false;

    while (!Res) {
      // fetch the current Position from where we can dequeue an item
      Pos = DequeuePos.load();
      Cell = &Buffer[Pos & BufferMask];
      auto Seq = Cell->Sequence.load();
      auto Diff = static_cast<int>(Seq) - static_cast<int>(Pos + 1);

      // probably the queue is empty, then return false
      if (Diff < 0)
        return false;

      // Check if its Sequence was changed by a producer and wasn't changed by
      // other consumers and if we can increment the dequeue Position
      if (Diff == 0)
        Res = DequeuePos.compare_exchange_weak(Pos, Pos + 1);
    }

    // read the item and update for the next round of the buffer
    Data = std::move(Cell->Data);
    Cell->Sequence.store(Pos + BufferMask + 1);
    return true;
  }

  bool is_empty() const { return EnqueuePos.load() == DequeuePos.load(); }
};

std::atomic<int> NTasks;

void produce(lf_queue<int> &Q, Config Cfg) {
  for (;;) {
    int N = NTasks.load();

    // check if I need enter CAS loop at all
    if (N < 0)
      break;

    while (!NTasks.compare_exchange_weak(N, N - 1)) {
      // check if inside CAS loop other producers exhausted tasks
      if (N < 0)
        return;
      std::this_thread::yield();
    }

    //std::this_thread::sleep_for(Cfg.PTime);
    while (!Q.push(N))
      std::this_thread::yield();
  }
}

void consume(lf_queue<int> &Q, Config Cfg) {
  for (;;) {
    int N = NTasks.load();
    if (N < 0 && Q.is_empty())
      break;
    bool Succ = Q.pop(N);
    if (Succ) {
      //std::this_thread::sleep_for(Cfg.CTime);
    }
  }
}

} // namespace

int main(int argc, char **argv) try {
  Config Cfg{};
  NTasks = Cfg.NTasks;

  std::vector<std::thread> Producers;
  std::vector<std::thread> Consumers;
  lf_queue<int> Queue(Cfg);

  for (int N = 0; N < Cfg.NProd; ++N)
    Producers.emplace_back(produce, std::ref(Queue), Cfg);

  for (int N = 0; N < Cfg.NCons; ++N)
    Consumers.emplace_back(consume, std::ref(Queue), Cfg);

  for (auto &P : Producers)
    P.join();

  for (auto &C : Consumers)
    C.join();

} catch (const std::runtime_error &E) {
  std::cout << "Runtime error: " << E.what() << "\n";
  return -1;
} catch (...) {
  std::cout << "Unknown error\n";
  return -1;
}
