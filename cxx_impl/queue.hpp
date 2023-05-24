#pragma once
#include <atomic>
#include <cassert>
#include <iostream>
#include <optional>

template <class T> class MichaelScottQueue {
    struct TaggedPointer;

    struct Node {
        T value{};
        std::atomic<TaggedPointer> next{};
    };

    struct TaggedPointer {
        Node *ptr{nullptr};
        unsigned refId{0u}; // for ABA problem safity
    };

    std::atomic<TaggedPointer> Head;
    std::atomic<TaggedPointer> Tail;

  public:
    // Tail == Head --> dummy node (if empty)
    MichaelScottQueue() {
        Node *dummy = new Node;
        Head.store(TaggedPointer{dummy});
        Tail.store(TaggedPointer{dummy});
    }
    ~MichaelScottQueue() {
        auto ptr = Head.load();
        delete ptr.ptr;
    }

    std::optional<T> pop() {
        TaggedPointer head = Head;
        T task{};

        // CAS loop
        while (true) {
            head = Head;
            TaggedPointer tail(Tail);

            // error case
            if (head.ptr == nullptr)
                return {};

            TaggedPointer next(head.ptr->next);

            if (head.refId == Head.load().refId &&
                head.ptr == Head.load().ptr) {
                if (head.ptr == tail.ptr) {
                    // queue is empty
                    if (next.ptr == nullptr)
                        return {};
                    // Tail should be shifted in a CAS
                    Tail.compare_exchange_strong(
                        tail, TaggedPointer{next.ptr, tail.refId + 1});
                } else {
                    task = next.ptr->value;
                    if (Head.compare_exchange_strong(
                            head, TaggedPointer{next.ptr, head.refId + 1})) {
                        // std::cerr << "pop\n";
                        break;
                    }
                }
            }
        }

        delete head.ptr;
        return task;
    }

    void push(T const &task) {
        Node *placeholder = new Node;
        placeholder->value = task;

        // CAS loop
        while (true) {
            // Read Tail.ptr and Tail.count together
            TaggedPointer tail(Tail);

            // Read next ptr and count fields together
            assert(tail.ptr != nullptr);
            TaggedPointer next{// ptr
                               tail.ptr->next.load().ptr,
                               // count
                               tail.ptr->next.load().refId};

            if (tail.refId == Tail.load().refId &&
                tail.ptr == Tail.load().ptr) {
                // append element to the end of queue
                if (next.ptr == nullptr) {
                    if (tail.ptr->next.compare_exchange_strong(
                            next, TaggedPointer{placeholder, next.refId + 1})) {
                        // std::cerr << "push\n";
                        break;
                    }
                    // increment Tail ptr while it is not queue tail in a CAS
                } else {
                    Tail.compare_exchange_strong(
                        tail, TaggedPointer{next.ptr, tail.refId + 1});
                }
            }
        }
    }
};
