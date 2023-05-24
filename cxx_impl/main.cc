#include "queue.hpp"

#include <cstdlib>
#include <thread>
#include <vector>

namespace {
constexpr int TASKS_DEFAULT = 100;
constexpr int PRODUCERS_DEFAULT = 2;
constexpr int CONSUMERS_DEFAULT = 3;

std::atomic<int> pushedTaskCount{0};
std::atomic<int> poppedTaskCount{0};

using Queue = MichaelScottQueue<int>;

void produce(Queue &q, int countLim) {
    while (pushedTaskCount < countLim) {
        auto val = pushedTaskCount.load();
        if (pushedTaskCount.compare_exchange_strong(val, val + 1)) {
            q.push(val);
        }
    }
}

void consume(Queue &q, int countLim) {
    while (poppedTaskCount < countLim) {
        if (q.pop()) {
            ++poppedTaskCount;
        }
    }
}
} // namespace

int main(int argc, char *argv[]) {

    // Default tasks, producer, consumer value
    int tasks{TASKS_DEFAULT};
    int producers{PRODUCERS_DEFAULT};
    int consumers{CONSUMERS_DEFAULT};
    if (argc >= 2) {
        tasks = strtol(argv[1], nullptr, 10);
    }
    if (argc >= 3) {
        producers = strtol(argv[3], nullptr, 10);
    }
    if (argc >= 4) {
        consumers = strtol(argv[2], nullptr, 10);
    }

    if (!(tasks > 0 && consumers > 0 && producers > 0)) {
        std::cerr << "Wrong args\n";
        return -1;
    }

    int consumerJobs{0};
    int producerJobs{0};
    MichaelScottQueue<int> q{};

    { // scope for jthread
        std::vector<std::jthread> threads{};
        int i{0};
        while (consumerJobs + producerJobs < consumers + producers) {
            if (i % 2) {
                if (consumerJobs < consumers) {
                    consumerJobs++;
                    threads.emplace_back(consume, std::ref(q), tasks);
                }
            } else {
                if (producerJobs < producers) {
                    producerJobs++;
                    threads.emplace_back(produce, std::ref(q), tasks);
                }
            }
            ++i;
        }
    }

    // check
    auto diff = pushedTaskCount.load() - poppedTaskCount.load();
    if (diff != 0) {
        std::cerr << "Error: missed tasks: " << diff << std::endl;
    }
    return 0;
}
