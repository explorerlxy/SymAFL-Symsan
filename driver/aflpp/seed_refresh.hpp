#pragma once

#include <deque>
#include <string>
#include <utility>

namespace symafl {

enum class RefreshReady { Pending, Ready, Unavailable };

// Queue insertion starts an event; published learning completes it. Keep
// only affected parent/child pairs, including parents still being learned.
class SeedRefreshQueue {
 public:
  void enqueue(std::string child, std::string parent) {
    if (parent == child) parent.clear();
    events_.push_back({std::move(child), std::move(parent), false});
  }

  size_t size() const { return events_.size(); }

  template <class Resolve, class Refresh>
  size_t drain(Resolve resolve, Refresh refresh) {
    size_t completed = 0;
    const size_t count = events_.size();
    for (size_t i = 0; i < count; ++i) {
      Event event = std::move(events_.front());
      events_.pop_front();
      if (!event.child_done) {
        const auto state = resolve(event.child);
        if (state == RefreshReady::Unavailable) continue;
        if (state == RefreshReady::Pending || !refresh(event.child)) {
          events_.push_back(std::move(event));
          continue;
        }
        event.child_done = true;
      }
      if (!event.parent.empty()) {
        const auto state = resolve(event.parent);
        if (state == RefreshReady::Pending ||
            (state == RefreshReady::Ready && !refresh(event.parent))) {
          events_.push_back(std::move(event));
          continue;
        }
      }
      ++completed;
    }
    return completed;
  }

 private:
  struct Event {
    std::string child;
    std::string parent;
    bool child_done;
  };
  std::deque<Event> events_;
};

}  // namespace symafl
