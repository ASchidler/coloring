//
// Created on 12.10.21.
//

#ifndef CPP_HEURISTICS_H
#define CPP_HEURISTICS_H

#include "conflict_graph.h"
#include "solution.h"
#include <tuple>
#include <algorithm>
#include "bucket_queue.h"
#include <chrono>
#include <unordered_map>
#include <unordered_set>
#include <mutex>

using namespace std;

namespace planarity {
    class LimitedList {
    private:
        struct LimitedListNode {
            node_t value{};
            std::shared_ptr<LimitedListNode> prev = nullptr;
        };
        std::size_t _cnt = 0;
        std::shared_ptr<LimitedListNode> _first = nullptr;
        std::shared_ptr<LimitedListNode> _last = nullptr;
    public:
        std::size_t length;
        explicit LimitedList(std::size_t length) : length(length) {
        }
        node_t add(node_t value) {
            node_t ret = INVALID_NODE;
            if (_first == nullptr) {
                _first = std::make_shared<LimitedListNode>();
                _first->value = value;
                _last = _first;
                _cnt++;
            }
            else {
                auto newElement = std::make_shared<LimitedListNode>();
                _first->prev = newElement;
                newElement->value = value;
                _first = newElement;
                _cnt++;
                if (_cnt > length) {
                    ret = _last->value;
                    _last = _last->prev;
                    _cnt--;
                }
            }
            return ret;
        }

        void reset() {
            _first = nullptr;
            _last = nullptr;
        }
    };

    color_t greedyColoring(const ConflictGraph& g, const vector<tuple<int, node_t>>& ordering, vector<color_t>& coloring, color_t ub=INVALID_COLOR) {
        int target_size = 256;
        if (ub != INVALID_COLOR)
            target_size = ub;

        dynamic_bitset<> done(g.getNumNodes());
        dynamic_bitset<> taken;
        taken.reserve(target_size);

        color_t max_color = 0;

        for (auto cEntry: ordering) {
            auto n = get<1>(cEntry);
            auto modified = g.adjacency[n] & done;

            for(auto n2=modified.find_first(); n2 != boost::dynamic_bitset<unsigned long, std::allocator<unsigned long> >::npos; n2 = modified.find_next(n2)) {
                taken[coloring[n2]] = true;
            }

            taken.flip();
            auto cc = taken.find_first();

            if (cc == dynamic_bitset<>::npos) {
                if (taken.size() == taken.capacity()) {
                    taken.reserve(taken.capacity() + 256);
                }
                cc = taken.size();
                taken.push_back(false);
            }

            coloring[n] = static_cast<int>(cc);
            max_color = max(max_color, coloring[n]);
            done.set(n);
            taken.reset();
        }

        return max_color + 1;
    }

    Coloring greedyDegree(ConflictGraph& g) {
        vector<tuple<int, node_t>> nodes;
        vector<color_t> coloring(g.getNumNodes());
        fill(coloring.begin(), coloring.end(), -1);

        nodes.reserve(g.getNumNodes());

        for (int i=0; i < g.getNumNodes(); i++) {
            nodes.emplace_back(g.getDegree(i), i);
        }

        sort(nodes.rbegin(), nodes.rend());

        auto numColors = greedyColoring(g, nodes, coloring);
        return {coloring, numColors, nodes};
    }

    Coloring greedyDegeneracy(ConflictGraph& g) {
        BucketQueue q(g.getNumNodes());

        vector<tuple<int, node_t>> nodes;
        nodes.reserve(g.getNumNodes());
        vector<node_t> degeneracy;
        degeneracy.reserve(g.getNumNodes());
        auto done = dynamic_bitset<>(g.getNumNodes());

        vector<color_t> coloring(g.getNumNodes());
        fill(coloring.begin(), coloring.end(), -1);

        for(int i=0; i < g.getNumNodes(); i++) {
            auto degree = g.getDegree(i);
            q.add(degree, i);
            degeneracy.push_back(degree);
        }

        while(! q.empty()) {
            auto element = q.next();

            nodes.emplace_back(static_cast<int>(get<0>(element)), get<1>(element));
            done[get<1>(element)] = true;

            // TODO: This call is slow
            for (auto nb:g.getNeighborsExcept(get<1>(element), done)) {
                q.change(degeneracy[nb], degeneracy[nb]-1, nb);
                degeneracy[nb] -= 1;
            }
        }

        reverse(nodes.begin(), nodes.end());
        auto numColors = greedyColoring(g, nodes, coloring);
        return {coloring, numColors, nodes};
    }

    Coloring dsatur(const ConflictGraph& g) {
        vector<dynamic_bitset<>> restricted;
        dynamic_bitset<> done(g.getNumNodes());
        restricted.reserve(g.getNumNodes());
        BucketQueue q(g.getNumNodes(), false);
        vector<tuple<int, node_t>> ordering;
        ordering.reserve(g.getNumNodes());

        color_t max_color = 0;
        vector<color_t> coloring(g.getNumNodes(), INVALID_COLOR);

        vector<tuple<node_t, node_t>> by_degree;
        by_degree.reserve(g.getNumNodes());

        for(int i=0; i < g.getNumNodes(); i++) {
            q.add(0, i);
            by_degree.emplace_back(g.adjacency[i].count(), i);
        }

        sort(by_degree.rbegin(), by_degree.rend());
        unordered_map<node_t, node_t> r_node_map;
        vector<node_t> node_map;
        node_map.reserve(g.getNumNodes());

        for(int i=0; i < by_degree.size(); i++) {
            node_map.push_back(get<1>(by_degree[i]));
            r_node_map[get<1>(by_degree[i])] = i;
            restricted.emplace_back(dynamic_bitset<>());
        }

        while(! q.empty()) {
            auto entry = q.next();
            auto n = node_map[get<1>(entry)];
            ordering.emplace_back(ordering.size(), n);
            restricted[n].flip();
            auto cc = restricted[n].find_first();
            if (cc == dynamic_bitset<>::npos) {
                cc = restricted[n].size();
            }

            coloring[n] = cc;

            auto modified_nb = g.adjacency[n] - done;
            for(auto n2=modified_nb.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb.find_next(n2)) {
                if (restricted[n2].size() <= cc)
                    restricted[n2].resize(cc+1);
                if (!restricted[n2].test(cc)) {
                    restricted[n2].set(cc);
                    auto cnt = restricted[n2].count();
                    q.change(cnt-1, cnt, r_node_map[n2]);
                }
            }
            max_color = max(max_color, static_cast<color_t>(cc));
            done.set(n);
        }
        assert(g.verify(coloring));
        return Coloring(coloring, max_color+1, ordering);
    }

    void squeakyWheel(const ConflictGraph& g, Coloring& start, const string& export_path="", int iterations=50000, bool use_same=false, float budget_ratio=0.95, int budget_constant=-4) {
        vector<tuple<int, node_t>> current_order(start.ordering);
        vector<color_t> coloring(start.coloring);

        for(int i=0; i < iterations; i++) {
            int target = static_cast<int>(budget_ratio * (float) start.numColors);

            for(int n=0; n < g.getNumNodes(); n++) {
                get<0>(current_order[n]) = n;
                if (coloring[get<1>(current_order[n])] > target) {
                    get<0>(current_order[n]) += budget_constant * (coloring[get<1>(current_order[n])] - target);
                }
            }

            sort(current_order.begin(), current_order.end());
            std::fill(coloring.begin(), coloring.end(), -1);
            auto new_result = greedyColoring(g, current_order, coloring, start.numColors);

            cout << new_result << endl;

            if (0 <= new_result && (new_result < start.numColors or (use_same && new_result == start.numColors))) {
                start.numColors = new_result;
                start.ordering = current_order;
                start.coloring = coloring;

                if (!export_path.empty()) {
                    start.store(export_path, g);
                }
            }
        }
    }

    bool tabuSearchFlexible(const ConflictGraph& g, Coloring& start, color_t ub, const string& export_path="",
            unsigned int iterations=100000, unsigned int retention=10, unsigned int resetIterations=10000, color_t failed_limit=INVALID_COLOR) {
        auto c_retention = retention;
        int eliminatedColors = 0;
        unordered_set<int> usedColors(start.numColors);
        auto originalColors = start.numColors;

        while(usedColors.size() < start.numColors && usedColors.size() < failed_limit) {
            vector<dynamic_bitset<>> partitions;
            vector<dynamic_bitset<>> taboos;
            vector<tuple<unsigned int, node_t, color_t>> tabuQueue;
            vector<vector<node_t>> neighborhood_counts(g.getNumNodes(), vector<node_t>(start.numColors, 0));
            vector<vector<node_t>> neighborhood_counts_real(g.getNumNodes(), vector<node_t>(start.numColors, 0));

            taboos.reserve(g.getNumNodes() * start.numColors);
            node_t c_taboo_idx = 0;
            unsigned int iteration = 0;
            vector<color_t> current_coloring(start.coloring);
            dynamic_bitset<> flexible(g.getNumNodes());
            int selected_color = -1;

            std::function<void (node_t, bool)> setFlexibility = [&](node_t node, bool flexibility) {
                if (flexibility) {
                    if (flexible.test(node))
                        return;
                    flexible.set(node);
                } else {
                    if (!flexible.test(node))
                        return;
                    flexible.reset(node);
                }

                for (auto n2 = g.adjacency[node].find_first();
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {

                    if (flexibility) {
                        assert(neighborhood_counts[n2][current_coloring[node]] > 0);
                        neighborhood_counts[n2][current_coloring[node]] -= 1;
                    } else {
                        neighborhood_counts[n2][current_coloring[node]] += 1;
                    }
                }
            };

            auto changeColor = [&](node_t node, color_t oldColor, color_t newColor) {
                assert(current_coloring[node] == oldColor);
                current_coloring[node] = newColor;
                partitions[oldColor].reset(node);
                partitions[newColor].set(node);
                taboos[node].set(oldColor);
                tabuQueue.emplace_back(iteration + c_retention, node, oldColor);
                bool is_flex = flexible.test(node);

                // If node is flexible, it wasn't counted
                for (auto n2=g.adjacency[node].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {
                    neighborhood_counts_real[n2][newColor] += 1;
                    assert(neighborhood_counts_real[n2][oldColor] > 0);
                    neighborhood_counts_real[n2][oldColor] -= 1;

                    if (neighborhood_counts_real[n2][oldColor] == 0 && oldColor != selected_color &&
                        oldColor != current_coloring[n2]) {
                        if (!flexible.test(n2)) {
                            setFlexibility(n2, true);
                        }
                    }
                    // Removed possibility for flexibility
                    if (neighborhood_counts_real[n2][newColor] == 1 && flexible.test(n2)) {
                        bool found = false;
                        for (color_t k = 0; k < start.numColors; k++) {
                            if (k != selected_color && k != current_coloring[n2] &&
                                neighborhood_counts_real[n2][k] == 0) {
                                found = true;
                                break;
                            }
                        }
                        if (!found)
                            setFlexibility(n2, false);
                    }

                    if (! is_flex) {
                        neighborhood_counts[n2][newColor] += 1;
                        neighborhood_counts[n2][oldColor] -= 1;
                    }
                }
            };

            partitions.reserve(start.numColors);
            for (int k = 0; k < start.numColors; k++) {
                partitions.emplace_back(g.getNumNodes());
            }
            for (int n = 0; n < g.getNumNodes(); n++) {
                partitions[start.coloring[n]].set(n);
                taboos.emplace_back(start.numColors);
            }

            while (iteration < iterations) {
                for (int n = 0; n < g.getNumNodes(); n++) {
                    std::fill(neighborhood_counts[n].begin(), neighborhood_counts[n].end(), 0);
                    std::fill(neighborhood_counts_real[n].begin(), neighborhood_counts_real[n].end(), 0);
                }
                for (int n = 0; n < g.getNumNodes(); n++) {
                    for (auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                        neighborhood_counts[n2][start.coloring[n]] += 1;
                        neighborhood_counts_real[n2][start.coloring[n]] += 1;
                    }
                }

                flexible.reset();
                for(node_t n=0; n < g.getNumNodes(); n++) {
                    for(color_t k=0; k < start.numColors; k++) {
                        if (k != start.coloring[n] && neighborhood_counts_real[n][k] == 0) {
                            flexible.set(n);
                            break;
                        }
                    }
                }

                dynamic_bitset<>::size_type min_count;
                // Temporary coloring as to not mess up ours

                // Pick color with fewest elements
                for (int k = 0; k < partitions.size(); k++) {
                    if (partitions[k].empty() || usedColors.find(k) != usedColors.end())
                        continue;

                    auto count = (partitions[k] - flexible).count();
                    if (selected_color == -1 || count < min_count || (count == min_count && rand() % 2 == 0)) {
                        min_count = count;
                        selected_color = k;
                    }
                }
                flexible.reset();
                for(node_t n=0; n < g.getNumNodes(); n++) {
                    if (! flexible.test(n)) {
                        for (color_t k = 0; k < start.numColors; k++) {
                            if (k != selected_color && k != start.coloring[n] && neighborhood_counts_real[n][k] == 0) {
                                setFlexibility(n, true);
                                break;
                            }
                        }
                    }
                }

                auto &current_partition = partitions[selected_color];
                auto startCount = current_partition.count();
                bool swapped = false; // Used to limit the any calls on the partition
                c_retention = startCount * 6 / 10;

                // Try to eliminate color
                while (iteration < iterations && (swapped || partitions[selected_color].any())) {
                    swapped = false;
                    if (iteration % 100 == 0) {
                        if (iteration % 1000 == 0)
                            cout << "Count " << current_partition.count() << endl;
                        c_retention = current_partition.count() * 6 / 10;
                    }

                    // Remove tabus after retention
                    while (c_taboo_idx < tabuQueue.size() && get<0>(tabuQueue[c_taboo_idx]) < iteration) {
                        taboos[get<1>(tabuQueue[c_taboo_idx])].reset(get<2>(tabuQueue[c_taboo_idx]));
                        c_taboo_idx++;
                    }

                    node_t c_min = INVALID_NODE;
                    node_t c_min_node = INVALID_NODE;
                    color_t alternative_color = INVALID_COLOR;

                    // Find node with the smallest number of neighbors colored in an alternative color
                    for (auto n = current_partition.find_first();
                         n != boost::dynamic_bitset<>::npos && c_min != 0; n = current_partition.find_next(n)) {
                        for (auto k = 0; k < start.numColors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts[n][k];

                            // Non found, just change color
                            if (count == 0) {
                                if (neighborhood_counts_real[n][k] == 0) {
                                    changeColor(n, selected_color, k);
                                    c_min = INVALID_NODE;
                                    break;
                                } else {
                                    c_min = static_cast<int>(count);
                                    c_min_node = static_cast<int>(n);
                                    alternative_color = k;
                                }
                            }

                            if (taboos[n].test(k))
                                continue;

                            if (c_min_node == INVALID_NODE || count < c_min || (count == c_min && rand() % 2 == 0)) {
                                c_min_node = static_cast<int>(n);
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    // Change color of neighbors and propagate the change as long as there is only one
                    while (c_min == 1 && neighborhood_counts_real[c_min_node][alternative_color] == 1) {
                        // Switch colors
                        int next_n = static_cast<int>((g.adjacency[c_min_node] &
                                                       partitions[alternative_color]).find_first());

                        changeColor(c_min_node, selected_color, alternative_color);
                        changeColor(next_n, alternative_color, selected_color);

                        c_min = INVALID_NODE;
                        c_min_node = next_n;
                        alternative_color = INVALID_COLOR;

                        for (auto k = 0; k < start.numColors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty() || taboos[next_n].test(k))
                                continue;

                            auto count = neighborhood_counts[next_n][k];
                            // Non found, just change color
                            if (count == 0) {
                                if (neighborhood_counts_real[c_min_node][k] == 0) {
                                    changeColor(c_min_node, selected_color, k);
                                    c_min = INVALID_COLOR;
                                    break;
                                } else {
                                    c_min = static_cast<int>(count);
                                    alternative_color = k;
                                }
                            }

                            if (c_min == INVALID_NODE || count <= 1 || (count < c_min && (rand() % 2) == 0)) {
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    if (c_min != INVALID_COLOR && neighborhood_counts_real[c_min_node][alternative_color] >= 1 && current_coloring[c_min_node] == selected_color) {
                        swapped = true;
                        changeColor(c_min_node, selected_color, alternative_color);

                        auto colored_neighbors = partitions[alternative_color] & g.adjacency[c_min_node];

                        for (auto n = colored_neighbors.find_first();
                             n != boost::dynamic_bitset<>::npos; n = colored_neighbors.find_next(n)) {
                            changeColor(n, alternative_color, selected_color);
                        }
                    }

                    iteration++;
                    if (iteration >= iterations) {
                        auto newCount = current_partition.count();
                        if (newCount < startCount) {
                            startCount = newCount;
                            iteration -= resetIterations;
                        }
                    }
                }

                // Check if we eliminated all nodes, or if we ran out of iterations
                if (!current_partition.any()) {
                    cout << "Eliminated color " << selected_color << endl;
                    auto c_max_color = partitions.size() - 1;
                    if (selected_color != c_max_color) {
                        partitions[selected_color] = partitions[c_max_color];

                        for (int n = 0; n < g.getNumNodes(); n++) {
                            if (current_coloring[n] == c_max_color) {
                                current_coloring[n] = selected_color;
                            }
                            neighborhood_counts[n][selected_color] = neighborhood_counts[n][c_max_color];
                            taboos[n].reset(selected_color);
                        }
                    }

                    partitions.pop_back();
                    start.coloring = current_coloring;
                    start.numColors -= 1;
                    // TODO: Adapt ordering? For the return would be sufficient...
                    if (!export_path.empty() && start.numColors < ub) {
                        start.store(export_path, g);
                    }
                    eliminatedColors++;
                } else {
                    cout << "Failed to eliminate color " << selected_color << endl;
                    usedColors.insert(selected_color);
                }
            }
        }
        cout << "Eliminated " << eliminatedColors << " Colors from originally " << originalColors << endl;
        return eliminatedColors > 0;
    }

    node_t twwHeuristic(ConflictGraph& g) {
        dynamic_bitset<> done(g.getNumNodes());
        vector<dynamic_bitset<>> red_edges(g.getNumNodes(), dynamic_bitset<>(g.getNumNodes()));
        node_t tww = 0;
        BucketQueue q(g.getNumNodes(), false);
        vector<node_t> degrees(g.getNumNodes(), 0);

        for(node_t n=0; n < g.getNumNodes(); n++) {
            auto degree = g.adjacency[n].count();
            q.add(degree, n);
            degrees[n] = degree;
        }

        for(auto contracted=0; contracted < g.getNumNodes() - 1; contracted++) {
            node_t c_min = INVALID_NODE;
            node_t contract1 = INVALID_NODE;
            node_t contract2 = INVALID_NODE;

            auto not_done = ~done;
            // Find minimum nodes to contract
//            for (auto n = not_done.find_first(); n != dynamic_bitset<>::npos; n = not_done.find_next(n)) {
            auto nxt = q.next();

            auto n = get<1>(nxt);
                for(auto n2 = not_done.find_first(); n2 != dynamic_bitset<>::npos; n2 = not_done.find_next(n2)) {
                    if (n == n2)
                        continue;
                    auto new_reds = g.adjacency[n] ^ g.adjacency[n2];
                    new_reds.reset(n);
                    new_reds.reset(n2);
                    new_reds |= (red_edges[n] | red_edges[n2]);
                    auto new_red_cnt = new_reds.count();
                    if (c_min == INVALID_NODE || new_red_cnt < c_min) {
                        c_min = new_red_cnt;
                        contract1 = n;
                        contract2 = n2;
                    }
                }
            //}

            for(auto c_n = g.adjacency[contract1].find_first(); c_n != dynamic_bitset<>::npos; c_n = g.adjacency[contract1].find_next(c_n)) {
                if (! done.test(c_n)) {
                    q.change(degrees[c_n], degrees[c_n] - 1, c_n);
                    degrees[c_n] -= 1;
                }
            }

            // Contract
            done.set(contract1);
            auto new_reds = g.adjacency[contract1] ^ g.adjacency[contract2];
            new_reds |= red_edges[contract1];
            new_reds.reset(contract1);
            new_reds.reset(contract2);
            red_edges[contract2] |= new_reds;
            auto new_red_cnt = red_edges[contract2].count();
            if (new_red_cnt > tww)
                tww = new_red_cnt;

            for(auto c_n=red_edges[contract2].find_first(); c_n != dynamic_bitset<>::npos; c_n = red_edges[contract2].find_next(c_n)) {
                red_edges[c_n].set(contract2);
                red_edges[c_n].reset(contract1);
                auto c_red_cnt = red_edges[c_n].count();
                if (c_red_cnt > tww)
                    tww = c_red_cnt;
            }
        }

        return tww;
    }

    void orderingSearch(const ConflictGraph& g, Coloring& start, const string& export_path="", long long iterations=10000000) {
        unordered_map<node_t, node_t> nodePosition(g.getNumNodes());
        vector<node_t> ordering(g.getNumNodes());
        vector<color_t> coloring = start.coloring;
        color_t c_colors = start.numColors;
        vector<dynamic_bitset<>> taboos(g.getNumNodes(), dynamic_bitset<>(c_colors + 1));
        vector<node_t> blockingPos(c_colors + 1);
        dynamic_bitset<> taken(c_colors + 1);
        dynamic_bitset<> done(g.getNumNodes());

        vector<LimitedList> tenures(g.getNumNodes(), LimitedList(c_colors / 2));

        for(auto i=0; i < g.getNumNodes(); i++) {
            nodePosition[get<1>(start.ordering[i])] = i;
            ordering[i] = get<1>(start.ordering[i]);
        }

        node_t pos = INVALID_NODE;

        for(long long iteration=0; iteration < iterations; iteration++) {
            if (pos == INVALID_NODE) {
                // Find position of badly colored vertex
                for (pos=0; pos < g.getNumNodes(); pos++) {
                    if (coloring[ordering[pos]] == c_colors - 1)
                        break;
                }
            }
            // If non could be found, successfully eliminated color...
            if (pos >= g.getNumNodes()) {
                c_colors = 0;
                for (auto cc: coloring) {
                    if (cc > c_colors - 1) {
                        c_colors = cc + 1;
                    }
                }
                for(auto cl:tenures) {
                    if (cl.length >= c_colors - 3) {
                        cl.length = c_colors - 3;
                        cl.reset();
                    }
                }
                for(auto cl: taboos)
                    cl.reset();

                cout << "Eliminated color, now " << c_colors << " colors" << endl;
                for (pos=0; pos < g.getNumNodes(); pos++) {
                    if (coloring[ordering[pos]] == c_colors - 1)
                        break;
                }
            }

            assert(pos < g.getNumNodes());
            node_t n = ordering[pos];

            for(auto& ce: blockingPos) {
                ce = INVALID_NODE;
            }

            // Check where we could move the node to
            for(auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                auto n2_color = coloring[n2];

                if (blockingPos[n2_color] == INVALID_NODE || blockingPos[n2_color] > nodePosition[n2]) {
                    blockingPos[n2_color] = nodePosition[n2];
                }
            }

            // Find largest number that we can assign to the current color without breaking taboos. Avoid num_colors - 2
            // as it would immediately create conflicts
            color_t max_cc = INVALID_COLOR;
            if (taboos[n].count() >= c_colors - 1) {
                taboos[n].reset();
                cout << "Reset " << n << endl;
            }

            for(auto cc = c_colors - 2; cc > 0; cc--) {
                if (max_cc == INVALID_COLOR) {
                    if (!taboos[n].test(cc - 1)) {
                        max_cc = cc - 1;
                        break;
                    }
                }
            }

            // All taboo
            if (max_cc == INVALID_COLOR) {
                // If also taboo, default to c_colors -3, else use color we wanted to avoid.
                if (taboos[n].test(c_colors - 2))
                    max_cc = c_colors - 3;
                else
                    max_cc = c_colors - 2;
            }

            if (blockingPos[max_cc] == INVALID_NODE) {
                coloring[n] = max_cc;
                pos = INVALID_NODE;
            } else {
                auto target_pos = blockingPos[max_cc];
                cout << "Pos: " << pos << " to " << target_pos << "\t" << n << " to " << max_cc << " (" << c_colors << ")" << endl;
                // Rearrange
                for (auto c_pos = pos; c_pos > target_pos; c_pos--) {
                    auto c_target = ordering[c_pos - 1];
                    nodePosition[c_target] = c_pos;
                    swap(ordering[c_pos], ordering[c_pos - 1]);
                }
                ordering[target_pos] = n;
                nodePosition[n] = target_pos;

                // Set taboos
                if (! taboos[n].test(max_cc)) {
                    taboos[n].set(max_cc);

//                    auto n_taboo_old = tenures[n].add(max_cc);
//                    if (n_taboo_old != INVALID_NODE)
//                        taboos[n].reset(n_taboo_old);
                }

                for (auto n2 = g.adjacency[n].find_first();
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    if (nodePosition[n2] > target_pos) {
                        if (! taboos[n2].test(coloring[n2])) {
                            taboos[n2].set(coloring[n2]);
//                            auto n2_taboo_old = tenures[n2].add(coloring[n2]);
//                            if (n2_taboo_old != INVALID_NODE)
//                                taboos[n2].reset(n2_taboo_old);
                        }
                    }
                }

                // Propagate
                done.reset();
                for (node_t i = 0; i < target_pos; i++) {
                    done.set(ordering[i]);
                }

                pos = INVALID_NODE;
                for (node_t i = target_pos; i < g.getNumNodes(); i++) {
                    auto cn = ordering[i];
                    auto modified = g.adjacency[cn] & done;
                    taken.reset();
                    for (auto n2 = modified.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified.find_next(n2)) {
                        taken.set(coloring[n2]);
                    }

                    taken.flip();
                    auto cc = taken.find_first();
                    if (cc >= c_colors - 1) {
                        pos = i;
                        break;
                    }
                    coloring[cn] = static_cast<int>(cc);
                    done.set(cn);
                }
            }
        }
    }

//    void orderingSearch(ConflictGraph& g, vector<node_t>& clique, color_t ub) {
//        vector<dynamic_bitset<>> restricted(g.getNumNodes(), dynamic_bitset<>(ub));
//        dynamic_bitset<> done(g.getNumNodes());
//        BucketQueue q(g.getNumNodes(), false);
//        vector<tuple<int, node_t>> ordering;
//        ordering.reserve(g.getNumNodes());
//
//        color_t max_color = 0;
//        vector<color_t> coloring(g.getNumNodes(), INVALID_COLOR);
//
//        vector<tuple<node_t, node_t>> by_degree;
//
//        by_degree.reserve(g.getNumNodes());
//        for(int i=0; i < g.getNumNodes(); i++) {
//            q.add(0, i);
//            by_degree.emplace_back(g.adjacency[i].count(), i);
//        }
//        sort(by_degree.rbegin(), by_degree.rend());
//
//        unordered_map<node_t, node_t> r_node_map;
//        vector<node_t> node_map;
//        node_map.reserve(g.getNumNodes());
//
//        for(int i=0; i < by_degree.size(); i++) {
//            node_map.push_back(get<1>(by_degree[i]));
//            r_node_map[get<1>(by_degree[i])] = i;
//            restricted.emplace_back(dynamic_bitset<>());
//        }
//
//        while(! q.empty()) {
//            auto entry = q.next();
//            auto n = node_map[get<1>(entry)];
//            ordering.emplace_back(ordering.size(), n);
//            restricted[n].flip();
//            auto cc = restricted[n].find_first();
//            if (cc == dynamic_bitset<>::npos) {
//                cc = restricted[n].size();
//            }
//
//            coloring[n] = cc;
//
//            auto modified_nb = g.adjacency[n] - done;
//            for(auto n2=modified_nb.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb.find_next(n2)) {
//                if (restricted[n2].size() <= cc)
//                    restricted[n2].resize(cc+1);
//                if (!restricted[n2].test(cc)) {
//                    restricted[n2].set(cc);
//                    auto cnt = restricted[n2].count();
//                    q.change(cnt-1, cnt, r_node_map[n2]);
//                }
//            }
//            max_color = max(max_color, static_cast<color_t>(cc));
//            done.set(n);
//        }
//        assert(g.verify(coloring));
//        return Coloring(coloring, max_color+1, ordering);
//    }

    bool tabuSearchLookahead(const ConflictGraph &g, Coloring &start, color_t ub, const string &export_path = "",
                             unsigned int iterations = 100000, unsigned int retention = 10,
                             unsigned int resetIterations = 2500, color_t failed_limit = INVALID_COLOR,
                             unsigned int branching_width = 3, node_t branching_depth = 5, node_t seed=0) {

        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

        // TODO: What in case of early failure?
        auto c_retention = retention;
        int eliminatedColors = 0;
        unordered_set<int> usedColors(start.numColors);
        auto originalColors = start.numColors;
        // Temporary coloring as to not mess up ours
        int selected_color = -1;

        while (usedColors.size() < start.numColors && usedColors.size() < failed_limit) {
            vector<dynamic_bitset<>> partitions(start.numColors, dynamic_bitset<>(g.getNumNodes()));
            vector<dynamic_bitset<>> taboos;
            vector<tuple<unsigned int, node_t, color_t>> tabuQueue;
            vector<vector<node_t>> neighborhood_counts(g.getNumNodes(), vector<node_t>(start.numColors, 0));

            taboos.reserve(g.getNumNodes() * start.numColors);
            node_t c_taboo_idx = 0;
            unsigned int iteration = 0;
            vector<color_t> current_coloring(start.coloring);
            dynamic_bitset<> flexible(g.getNumNodes());
            unordered_map<node_t, color_t> flexibleRev;

            auto changeColor = [&](node_t node, color_t oldColor, color_t newColor) {
                current_coloring[node] = newColor;
                partitions[oldColor].reset(node);
                partitions[newColor].set(node);
                taboos[node].set(oldColor);
                tabuQueue.emplace_back(iteration + c_retention, node, oldColor);
                for (auto n2 = g.adjacency[node].find_first();
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {
                    neighborhood_counts[n2][newColor] += 1;
                    neighborhood_counts[n2][oldColor] -= 1;
                    if (neighborhood_counts[n2][oldColor] == 0 && oldColor != selected_color && oldColor != current_coloring[n2]) {
                        flexible.set(n2);
                        flexibleRev[n2] = oldColor;
                    }
                    if (neighborhood_counts[n2][newColor] == 1 && flexible.test(node) && flexibleRev[node] == newColor) {
                        flexible.reset(n2);
                        for(color_t k=0; k < start.numColors; k++) {
                            if (k != selected_color && k != current_coloring[n2] && neighborhood_counts[n2][k] == 0) {
                                flexibleRev[n2] = k;
                                flexible.set(n2);
                                break;
                            }
                        }
                    }
                }

                if (flexible.test(node)) {
                    flexible.reset(node);
                    for(color_t k=0; k < start.numColors; k++) {
                        if (k != selected_color && k != current_coloring[node] && neighborhood_counts[node][k] == 0) {
                            flexibleRev[node] = k;
                            flexible.set(node);
                            break;
                        }
                    }
                }
            };

            std::function<node_t (dynamic_bitset<>&, dynamic_bitset<>&, node_t, vector<tuple<color_t, dynamic_bitset<>>>&, node_t, color_t, node_t, bool)>
                    lookAhead = [&](dynamic_bitset<>& currentComponent, dynamic_bitset<>& seen, node_t branching,
                                    vector<tuple<color_t, dynamic_bitset<>>> &solutions,
                                    node_t depth, color_t color, node_t min_count, bool taboo) {
                vector<tuple<node_t, color_t, dynamic_bitset<>>> sub_nb;
                sub_nb.reserve(branching + 1);
                dynamic_bitset<> c_adjacency(g.getNumNodes());
                dynamic_bitset<> taboo_colors(taboos.back().size());

                for (auto n = currentComponent.find_first(); n != dynamic_bitset<>::npos; n = currentComponent.find_next(n)) {
                    if (!flexible.test(n)) {
                        c_adjacency |= g.adjacency[n];
                        if (taboo)
                            taboo_colors |= taboos[n];
                    }
                }

                for (auto k = 0; k < start.numColors; k++) {
                    if (k != color && !(seen & partitions[k]).any() && (!taboo || !taboo_colors.test(k))) {
                        auto c_part = (c_adjacency & partitions[k]);
                        auto n_cnt = c_part.count();

                        if (n_cnt == 0)
                            sub_nb.clear();
                        sub_nb.emplace_back(n_cnt, k, c_part);
                        if (sub_nb.size() > branching) {
                            sort(sub_nb.begin(), sub_nb.end());
                            sub_nb.pop_back();
                        }
                        if (n_cnt == 0)
                            break;
                    }
                }

                for (auto &c_nb : sub_nb) {
                    if (depth == 0 || get<0>(c_nb) == 0) {
                        if (get<0>(c_nb) < min_count) {
                            solutions.clear();
                            solutions.emplace_back(get<1>(c_nb), get<2>(c_nb));
                            min_count = get<0>(c_nb);
                        }
                    } else {
                        auto c_seen = seen | get<2>(c_nb);
                        auto result = lookAhead(get<2>(c_nb), c_seen, branching, solutions, depth - 1,
                                                color, min_count, false);
                        if (result < min_count) {
                            min_count = result;
                            solutions.emplace_back(get<1>(c_nb), get<2>(c_nb));
                        }
                    }
                }

                return min_count;
            };

            for (int n = 0; n < g.getNumNodes(); n++) {
                partitions[start.coloring[n]].set(n);
                taboos.emplace_back(start.numColors);

                for (auto n2 = g.adjacency[n].find_first();
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    neighborhood_counts[n2][start.coloring[n]] += 1;
                }
            }

            while (iteration < iterations) {
                dynamic_bitset<>::size_type min_count;

                for(node_t n=0; n < g.getNumNodes(); n++) {
                    for(color_t k=0; k < start.numColors; k++) {
                        if (k != start.coloring[n] && neighborhood_counts[n][k] == 0) {
                            flexible.set(n);
                            flexibleRev[n] = k;
                            break;
                        }
                    }
                }

                // Pick color with fewest elements
                vector<pair<node_t, color_t>> color_counts;
                color_counts.reserve(partitions.size());
                for (int k = 0; k < partitions.size(); k++) {
                    if (partitions[k].empty() || usedColors.find(k) != usedColors.end())
                        continue;

                    auto count = (partitions[k] - flexible).count();
                    color_counts.emplace_back(count, k);
                }
                sort(color_counts.begin(), color_counts.end());
                selected_color = color_counts[seed].second;
                min_count = color_counts[seed].first;

                flexible.reset();
                for(node_t n=0; n < g.getNumNodes(); n++) {
                    for(color_t k=0; k < start.numColors; k++) {
                        if (k != selected_color && k != start.coloring[n] && neighborhood_counts[n][k] == 0) {
                            flexible.set(n);
                            flexibleRev[n] = k;
                            break;
                        }
                    }
                }

                auto &current_partition = partitions[selected_color];
                auto startCount = current_partition.count();
                bool swapped = false; // Used to limit the any calls on the partition
                c_retention = startCount * 6 / 10;

                // Try to eliminate color
                while (iteration < iterations && (swapped || partitions[selected_color].any())) {
                    swapped = false;
                    if (iteration % 100 == 0)
                        c_retention = current_partition.count() * 6 / 10;

                    // Remove tabus after retention
                    while (c_taboo_idx < tabuQueue.size() && get<0>(tabuQueue[c_taboo_idx]) < iteration) {
                        taboos[get<1>(tabuQueue[c_taboo_idx])][get<2>(tabuQueue[c_taboo_idx])] = false;
                        c_taboo_idx++;
                    }

                    int c_min = -1;
                    int c_min_node = -1;
                    int alternative_color = -1;

                    cout << "Color " << selected_color << ", Count " << current_partition.count() << endl;

                    // Find node with the smallest number of neighbors colored in an alternative color
                    for (auto n = current_partition.find_first();
                         n != boost::dynamic_bitset<>::npos && c_min != 0; n = current_partition.find_next(n)) {
                        for (auto k = 0; k < start.numColors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts[n][k];

                            // Non found, just change color
                            if (count == 0) {
                                changeColor(n, selected_color, k);
                                c_min = 0;
                                break;
                            }

                            if (taboos[n][k])
                                continue;

                            if (c_min_node == -1 || count < c_min) {
                                c_min_node = static_cast<int>(n);
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    // No options...
                    if (c_min == -1) {
                        usedColors.insert(selected_color);
                        cout << "Early fail to eliminate color " << selected_color << endl;
                        break;
                    }

                    if (c_min >= 1) {
                        swapped = true;
                        dynamic_bitset<> component(g.getNumNodes());
                        node_t cnt = 0;
                        component.set(c_min_node);
                        vector<tuple<color_t, dynamic_bitset<>>> sol;
                        sol.reserve(branching_depth);
                        auto result = lookAhead(component, component, branching_width, sol, branching_depth, selected_color, INVALID_NODE, true);
                        cout << "Propagated to " << result << " nodes" << endl;
                        while (!sol.empty()) {
                            auto &ck = sol.back();
                            for (auto n = component.find_first();
                                 n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                                auto oldColor = current_coloring[n];
                                if (flexible.test(n)) {
                                    changeColor(n, oldColor, selected_color);
                                } else {
                                    changeColor(n, oldColor, get<0>(ck));
                                }
                            }
                            component = partitions[get<0>(ck)] & get<1>(ck);
                            sol.pop_back();
                        }
                        for (auto n = component.find_first();
                             n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                            auto oldColor = current_coloring[n];
                            changeColor(n, oldColor, selected_color);
                        }
                    }

                    iteration++;
                    if (iteration >= iterations) {
                        auto newCount = current_partition.count();
                        if (newCount < startCount) {
                            startCount = newCount;
                            iteration -= resetIterations;
                        }
                    }
                }

                // Check if we eliminated all nodes, or if we ran out of iterations
                if (!current_partition.any()) {
                    auto c_max_color = partitions.size() - 1;
                    if (selected_color != c_max_color) {
                        partitions[selected_color] = partitions[c_max_color];

                        for (int n = 0; n < g.getNumNodes(); n++) {
                            if (current_coloring[n] == c_max_color) {
                                current_coloring[n] = selected_color;
                            }
                            neighborhood_counts[n][selected_color] = neighborhood_counts[n][c_max_color];
                            taboos[n].reset(selected_color);
                        }
                    }
                    assert(g.verify(current_coloring));

                    partitions.pop_back();
                    start.coloring = current_coloring;
                    start.numColors -= 1;
                    // TODO: Adapt ordering? For the return would be sufficient...
                    if (!export_path.empty() && start.numColors < ub) {
                        start.store(export_path, g);
                    }
                    std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                    cout << seed << "::"<< std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << "::Eliminated " << selected_color << ", Remaining " << partitions.size() << endl;
                    eliminatedColors++;
                } else {
                    cout << "Failed to eliminate color " << selected_color << endl;
                    usedColors.insert(selected_color);
                }
            }
        }
        cout << "Eliminated " << eliminatedColors << " Colors from originally " << originalColors << endl;
        return eliminatedColors > 0;
    }

    bool tabuSearch(const ConflictGraph& g, Coloring& start, color_t ub, std::mutex& sync, unsigned int& cycle, const string& export_path="", node_t seed = 0,
                    unsigned int iterations=100000, unsigned int retention=10, unsigned int resetIterations=10000, color_t failed_limit=INVALID_COLOR) {
        // Check how many different colors:
        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        unordered_set<color_t> seen_colors;
        for(node_t n=0; n < g.getNumNodes(); n++) {
            seen_colors.insert(start.coloring[n]);
        }

        cout << ub << endl;
        cout << seen_colors.size() << endl;
        if (ub > seen_colors.size()) {
            unordered_map<color_t, color_t> color_map;
            color_t max_color = seen_colors.size() - 1;
            color_t current_gap = 0;

            for(node_t n=0; n < g.getNumNodes(); n++) {
                if (start.coloring[n] > max_color) {
                    auto ncolor = color_map.find(start.coloring[n]);
                    if (ncolor == color_map.end()) {
                        for(; current_gap <= max_color; current_gap++) {
                            if (seen_colors.find(current_gap) == seen_colors.end()) {
                                ncolor = color_map.emplace(start.coloring[n], current_gap).first;
                                break;
                            }
                        }
                    }
                    start.coloring[n] = ncolor->second;
                }
                seen_colors.insert(start.coloring[n]);
            }
            ub = max_color + 1;
            start.store(export_path, g);
            assert(g.verify(start.coloring));
        }


        auto c_retention = retention;
        int eliminatedColors = 0;
        sync.lock();
        unordered_set<int> usedColors(start.numColors);
        auto originalColors = start.numColors;
        auto my_cycle = cycle;
        sync.unlock();

        while(usedColors.size() < start.numColors && usedColors.size() < failed_limit) {
            sync.lock();
            vector<color_t> current_coloring(start.coloring);
            color_t current_num_colors = start.numColors;
            my_cycle = cycle;
            sync.unlock();

            vector<dynamic_bitset<>> partitions;
            vector<dynamic_bitset<>> taboos;
            vector<tuple<unsigned int, node_t, color_t>> tabuQueue;
            vector<vector<node_t>> neighborhood_counts(g.getNumNodes(), vector<node_t>(current_num_colors, 0));

            taboos.reserve(g.getNumNodes() * current_num_colors);
            node_t c_taboo_idx = 0;
            unsigned int iteration = 0;

            auto changeColor = [&](node_t node, color_t oldColor, color_t newColor) {
                current_coloring[node] = newColor;
                partitions[oldColor].reset(node);
                partitions[newColor].set(node);
                taboos[node].set(oldColor);
                tabuQueue.emplace_back(iteration + c_retention, node, oldColor);
                for (auto n2=g.adjacency[node].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {
                    neighborhood_counts[n2][newColor] += 1;
                    neighborhood_counts[n2][oldColor] -= 1;
                }
            };

            partitions.reserve(current_num_colors);
            for (int k = 0; k < current_num_colors; k++) {
                partitions.emplace_back(g.getNumNodes());
            }
            for (int n = 0; n < g.getNumNodes(); n++) {
                partitions[current_coloring[n]].set(n);
                taboos.emplace_back(current_num_colors);

                for (auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    neighborhood_counts[n2][current_coloring[n]] += 1;
                }
            }

            while (iteration < iterations) {
                if (my_cycle < cycle)
                    break;

                // Temporary coloring as to not mess up ours
                int selected_color = -1;

                // Pick color with fewest elements
                vector<pair<node_t, color_t>> color_counts;
                color_counts.reserve(current_num_colors);

                for (int k = 0; k < partitions.size(); k++) {
                    if (partitions[k].empty() || usedColors.find(k) != usedColors.end())
                        continue;

                    auto count = (partitions[k] - g.reduced).count();
                    color_counts.emplace_back(count, k);
                }
                sort(color_counts.rbegin(), color_counts.rend());
                selected_color = color_counts[seed].second;
                auto &current_partition = partitions[selected_color];
                auto startCount = current_partition.count();
                bool swapped = false; // Used to limit the any calls on the partition
                c_retention = startCount * 6 / 10;

                // Try to eliminate color
                while (iteration < iterations && (swapped || partitions[selected_color].any())) {
                    swapped = false;
                    if (iteration % 1000 == 0) {
                        cout << "Count " << current_partition.count() << endl;
                        c_retention = max(static_cast<unsigned int>(current_partition.count() * 6 / 10), retention);
                    }

                    // Remove tabus after retention
                    while (c_taboo_idx < tabuQueue.size() && get<0>(tabuQueue[c_taboo_idx]) < iteration) {
                        taboos[get<1>(tabuQueue[c_taboo_idx])].reset(get<2>(tabuQueue[c_taboo_idx]));
                        c_taboo_idx++;
                    }

                    int c_min = -1;
                    int c_min_node = -1;
                    int alternative_color = -1;

                    // Find node with the smallest number of neighbors colored in an alternative color
                    for (auto n = current_partition.find_first();
                         n != boost::dynamic_bitset<>::npos && c_min != 0; n = current_partition.find_next(n)) {
                        for (auto k = 0; k < current_num_colors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts[n][k];

                            // Non found, just change color
                            if (count == 0) {
                                changeColor(n, selected_color, k);
                                c_min = 0;
                                break;
                            }

                            if (taboos[n].test(k))
                                continue;

                            if (c_min_node == -1 || count < c_min || (count == c_min && rand() % 2 == 0)) {
                                c_min_node = static_cast<int>(n);
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    // No options...
                    if (c_min == -1) {
                        usedColors.insert(selected_color);
                        cout << "Early fail to eliminate color " << selected_color << endl;
                        break;
                    }

                    // Change color of neighbors and propagate the change as long as there is only one
                    while (c_min == 1) {
                        // Switch colors
                        int next_n = static_cast<int>((g.adjacency[c_min_node] &
                                                       partitions[alternative_color]).find_first());

                        changeColor(c_min_node, selected_color, alternative_color);
                        changeColor(next_n, alternative_color, selected_color);

                        c_min = -1;
                        c_min_node = next_n;
                        alternative_color = -1;

                        for (auto k = 0; k < current_num_colors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty() || taboos[next_n].test(k))
                                continue;

                            auto count = neighborhood_counts[next_n][k];
                            // Non found, just change color
                            if (count == 0) {
                                changeColor(next_n, selected_color, k);
                                c_min = 0;
                                break;
                            }

                            if (c_min == -1 || count <= 1 || (count < c_min && (rand() % 2) == 0)) {
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    if (c_min > 1) {
                        swapped = true;
                        changeColor(c_min_node, selected_color, alternative_color);

                        auto colored_neighbors = partitions[alternative_color] & g.adjacency[c_min_node];

                        for (auto n = colored_neighbors.find_first();
                             n != boost::dynamic_bitset<>::npos; n = colored_neighbors.find_next(n)) {
                            changeColor(n, alternative_color, selected_color);
                        }
                    }

                    iteration++;
                    if (iteration >= iterations) {
                        auto newCount = current_partition.count();
                        if (newCount < startCount) {
                            startCount = newCount;
                            iteration -= resetIterations;
                        }
                    }
                }

                // Check if we eliminated all nodes, or if we ran out of iterations
                if (!current_partition.any()) {
                    sync.lock();
                    if (my_cycle == cycle) {
                        cycle++;
                        my_cycle = cycle;
                        auto c_max_color = partitions.size() - 1;
                        if (selected_color != c_max_color) {
                            partitions[selected_color] = partitions[c_max_color];

                            for (int n = 0; n < g.getNumNodes(); n++) {
                                if (current_coloring[n] == c_max_color) {
                                    current_coloring[n] = selected_color;
                                }
                                neighborhood_counts[n][selected_color] = neighborhood_counts[n][c_max_color];
                                taboos[n].reset(selected_color);
                            }
                        }

                        partitions.pop_back();
                        start.coloring = current_coloring;
                        start.numColors -= 1;
                        // TODO: Adapt ordering? For the return would be sufficient...
                        if (!export_path.empty() && start.numColors < ub) {
                            start.store(export_path, g);
                        }
                        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                        cout << seed << "::"<< std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << "::Eliminated " << selected_color << ", Remaining " << partitions.size() << endl;
                        eliminatedColors++;
                    }
                    sync.unlock();
                    break;
                } else {
                    cout << "Failed to eliminate color " << selected_color << endl;
                    usedColors.insert(selected_color);
                    break;
                }
            }
        }
        cout << "Eliminated " << eliminatedColors << " Colors from originally " << originalColors << endl;
        return eliminatedColors > 0;
    }
}

#endif //CPP_HEURISTICS_H
