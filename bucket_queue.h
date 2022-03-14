//
// Created on 12.10.21.
//

#ifndef CPP_BUCKET_QUEUE_H
#define CPP_BUCKET_QUEUE_H
#include<vector>
#include<boost/dynamic_bitset.hpp>

#include "planarity.h"

using namespace std;
using namespace boost;

namespace planarity {
    class BucketQueue {
    private:
        vector<dynamic_bitset<>> _queue;
        vector<size_t> _values;
        node_t _nodes;
        size_t _cmin;
        bool _increasing;
        inline void verify() {
            if (_increasing) {
                while (_cmin < _queue.size() && !_queue[_cmin].any()) {
                    _cmin++;
                }
            } else {
                while (_cmin > 0 && !_queue[_cmin].any()) {
                    _cmin--;
                }
            }
        }
    public:
        explicit BucketQueue(node_t nodes, bool increasing=true) : _nodes(nodes), _cmin(increasing ? nodes : 0), _increasing(increasing), _values(nodes) {
            _queue = vector<dynamic_bitset<>>();
            _queue.reserve(nodes);
        }

        void add(size_t priority, node_t node) {
            for (auto i = _queue.size(); i <= priority; i++)
                _queue.emplace_back(_nodes);

            if ((_increasing && priority < _cmin) || (!_increasing && priority > _cmin))
                _cmin = priority;

            _queue[priority][node] = true;
            _values[node] = priority;
        }

        void change(size_t old, size_t modified, node_t node) {
            for (auto i = _queue.size(); i <= modified; i++)
                _queue.emplace_back(_nodes);

            if ((_increasing && modified < _cmin) || (!_increasing && modified > _cmin))
                _cmin = modified;

            assert(_queue[old][node]);
            _queue[old][node] = false;
            _queue[modified][node] = true;
            _values[node] = modified;
            verify();
        }

        void change(size_t modified, node_t node) {
            for (auto i = _queue.size(); i <= modified; i++)
                _queue.emplace_back(_nodes);

            if ((_increasing && modified < _cmin) || (!_increasing && modified > _cmin))
                _cmin = modified;

            assert(_queue[_values[node]][node]);
            _queue[_values[node]][node] = false;
            _queue[modified][node] = true;
            _values[node] = modified;
            verify();
        }

        tuple<size_t, node_t> next() {
            auto new_node = _queue[_cmin].find_first();
            _queue[_cmin][new_node] = false;

            verify();

            return tuple<size_t, int>(_cmin, new_node);
        }

        bool empty() {
            return (_increasing && _cmin >= _queue.size()) || (!_increasing && _cmin == 0 && !_queue[0].any());
        }
    };
}
#endif //CPP_BUCKET_QUEUE_H
