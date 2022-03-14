//
// Created on 16.10.21.
//

#ifndef PLANARITY_SAT_SEARCH_H
#define PLANARITY_SAT_SEARCH_H

#include <iostream>
#include <memory>
#include "sat_encode.h"
#include "sat_encode2.h"
#include <mutex>
#include <deque>

namespace planarity {
    void findUsingSat(const ConflictGraph &g, const vector<node_t> &clique, int ub, unsigned int budget = 2000,
                      unsigned int timeout = 150) {
        unsigned int node_count = 0;
        vector<color_t> coloring(g.getNumNodes(), INVALID_COLOR);
        dynamic_bitset<> done(g.getNumNodes());

        for (int i = 0; i < clique.size(); i++) {
            done.set(clique[i]);
            node_count += 1;
            coloring[clique[i]] = i;
        }

        while (node_count < g.getNumNodes()) {
            dynamic_bitset<> component(g.getNumNodes());
            if (g.getNumNodes() - node_count <= budget) {
                component = done;
                component.flip();
            } else {
                for (auto n = done.find_first();
                     n != dynamic_bitset<>::npos && component.count() < budget; n = done.find_next(n)) {
                    auto tmp = (g.adjacency[n] - done);
                    auto remainder = budget - component.count();
                    if (remainder < tmp.count()) {
                        auto remove = tmp.count() - remainder;
                        for (auto n2 = tmp.find_first();
                             n2 != dynamic_bitset<>::npos && remove > 0; n2 = tmp.find_next(n2)) {
                            tmp[n2] = false;
                            remove--;
                        }
                    }
                    component |= tmp;
                }
                while (component.count() < budget && component.count() <= g.getNumNodes() - node_count) {
                    for (auto n = component.find_first();
                         n != dynamic_bitset<>::npos && component.count() < budget; n = component.find_next(n)) {
                        auto tmp = (g.adjacency[n] - done - component);
                        auto remainder = budget - component.count();
                        if (remainder < tmp.count()) {
                            auto remove = tmp.count() - remainder;
                            for (auto n2 = tmp.find_first();
                                 n2 != dynamic_bitset<>::npos && remove > 0; n2 = tmp.find_next(n2)) {
                                tmp[n2] = false;
                                remove--;
                            }
                        }
                        component |= tmp;
                    }
                }
            }
            done |= component;
            node_count = done.count();

            SubGraph g2(g, component, coloring);
            auto new_coloring = SatEncode::encode_partial(g2, ub, timeout, false, true);
            if (new_coloring.first.coloring.empty()) {
                cout << "Failed coloring" << endl;
                return;
            }
            g2.map_coloring(new_coloring.first.coloring, coloring);

            cout << "Completed " << node_count << " Nodes" << endl;
        }

        assert(g.verify(coloring));
    }

    /**
     * Establishes a lower bound by trying to find an optimal ordering piece by piece.
     */
    color_t orderingLb(const ConflictGraph &g, const vector<node_t> &clique, color_t ub, vector<color_t> &coloring,
                       const unsigned int timeout = 60, const unsigned int full_timeout = 3600,
                       const string &filename = "") {
        bool pre_exist = !coloring.empty();
        if (!pre_exist)
            coloring.resize(g.getNumNodes(), INVALID_COLOR);
        bool is_first_iteration = false;

        vector<dynamic_bitset<>> restricted;
        dynamic_bitset<> done(g.getNumNodes());
        restricted.reserve(g.getNumNodes());
        vector<node_t> nodeMap;
        unordered_map<node_t, node_t> rNodeMap;
        rNodeMap.reserve(g.getNumNodes());
        nodeMap.reserve(g.getNumNodes());
        BucketQueue q(g.getNumNodes(), false);
        vector<node_t> sub_clique;
        sub_clique.reserve(clique.size());
        vector<color_t> restrictions_store;
        restrictions_store.reserve(g.getNumNodes());

        auto sub_g = ConflictGraph(0);
        color_t max_color = clique.size() - 1;

        auto addNode = [&](node_t c_node) {
            node_t mapped_idx = nodeMap.size();
            nodeMap.push_back(c_node);
            rNodeMap.emplace(c_node, mapped_idx);
            assert(nodeMap[rNodeMap[c_node]] == c_node);
            sub_g.addNode(mapped_idx, g.getNumNodes());
            auto modified_nb = g.adjacency[c_node] & done;

            for (auto n2 = modified_nb.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb.find_next(n2)) {
                sub_g.addEdge(rNodeMap[c_node], rNodeMap[n2]);
            }

            done[c_node] = true;
            return mapped_idx;
        };

        auto setColor = [&](node_t c_node, color_t c_color, bool update_queue = true) {
            coloring[c_node] = c_color;
            auto modified_nb = g.adjacency[c_node] - done;
            for (auto n2 = modified_nb.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb.find_next(n2)) {
                if (!restricted[n2].test(c_color)) {
                    restricted[n2][c_color] = true;
                    if (update_queue) {
                        auto cnt = restricted[n2].count();
                        q.change(cnt - 1, cnt, n2);
                    }
                }
            }
        };

        for (unsigned int i : clique) {
            addNode(i);
            done[i] = true;
        }

        if (pre_exist) {
            for (node_t i = 0; i < g.getNumNodes(); i++) {
                if (coloring[i] != INVALID_COLOR) {
                    max_color = max(max_color, coloring[i]);
                    if (!done[i]) {
                        addNode(i);
                        done[i] = true;
                    }
                }
            }
        }

        for (int i = 0; i < g.getNumNodes(); i++) {
            restricted.emplace_back(max(ub, static_cast<color_t>(max_color + 1)));
            if (!done[i])
                q.add(0, i);
        }

        for (node_t i = 0; i < clique.size(); i++) {
            auto n = clique[i];
            sub_clique.emplace_back(i);
            setColor(n, i);
        }
        if (pre_exist) {
            for (node_t i = 0; i < g.getNumNodes(); i++) {
                if (coloring[i] != INVALID_COLOR) {
                    setColor(i, coloring[i]);
                }
            }
            is_first_iteration = true;
        }

        // TODO: We could keep a SAT solver instance the whole time...
        while (!q.empty()) {
            color_t cc = INVALID_COLOR;
            bool exceeded = true;
            node_t n = INVALID_NODE;

            if (is_first_iteration) {
                is_first_iteration = false;
            } else {
                auto entry = q.next();
                n = get<1>(entry);
                restricted[n].flip();
                cc = static_cast<color_t>(restricted[n].find_first());
                exceeded = false;

                if (cc >= ub) {
                    exceeded = true;
                    cc = ub - 1;
                }
                addNode(n);
            }

            if (cc <= max_color && !exceeded) {
                setColor(n, cc);
            } else {
                auto new_color = SatEncode::encode_full(sub_g, sub_clique, max_color + 1,
                                                        exceeded ? full_timeout : timeout, "", true);
                if (new_color.coloring.empty()) {
                    if (!exceeded && cc != INVALID_COLOR) {
                        cout << "Colors increased to " << cc + 1 << endl;
                        max_color = cc;
                        setColor(n, cc);

                        if (!filename.empty()) {
                            Coloring::store(filename, g, coloring, false);
                        }
                    } else if (cc != INVALID_COLOR) {
                        cout << "Exceeded upper bound" << endl;
                        coloring[n] = INVALID_COLOR;
                        return ub;
                    }
                } else {
                    // Set new colors and update queue, we could restrict to actual neighbors, but with the dense graphs
                    // that usually does not eliminate many nodes.
                    for (auto i = 0; i < restricted.size(); i++) {
                        if (!done[i]) {
                            restrictions_store[i] = restricted[i].count();
                            restricted[i].reset();
                        }
                    }

                    max_color = 0;
                    for (auto i = 0; i < new_color.coloring.size(); i++) {
                        setColor(nodeMap[i], new_color.coloring[i], false);
                        max_color = max(max_color, new_color.coloring[i]);
                    }
                    for (auto i = 0; i < restricted.size(); i++) {
                        if (!done[i])
                            q.change(restrictions_store[i], restricted[i].count(), i);
                    }
                    if (!filename.empty()) {
                        Coloring::store(filename, g, coloring, false);
                    }
                }
            }

        }
        assert(g.verify(coloring));
        cout << "Required " << max_color + 1 << " Colors" << endl;
        return max_color + 1;
    }

    void satImproveColoring(ConflictGraph &g, Coloring &c, node_t budget = 2000, unsigned int timeout = 600) {
        vector<dynamic_bitset<>> partitions(c.numColors, dynamic_bitset<>(g.getNumNodes()));

        unordered_set<node_t> usedColors;

        for (node_t n = 0; n < g.getNumNodes(); n++)
            partitions[c.coloring[n]].set(n);

        auto change_color = [&](node_t node, color_t oldc, color_t newc) {
            c.coloring[node] = newc;
            partitions[oldc].reset(node);
            partitions[newc].set(node);
        };

        while (usedColors.size() < c.numColors) {
            auto &c_partition = partitions.back();
            while (c_partition.any()) {
                // Find node with the smallest number of neighbors colored in an alternative color
                node_t c_min = INVALID_NODE;
                node_t c_min_n = INVALID_NODE;

                for (auto n = c_partition.find_first();
                     n != boost::dynamic_bitset<>::npos && c_min != 0; n = c_partition.find_next(n)) {
                    for (auto k = 0; k < c.numColors; k++) {
                        // Already eliminated that color, or taboo
                        if (k == c.numColors - 1 || partitions[k].empty())
                            continue;

                        auto count = (g.adjacency[n] & partitions[k]).count();
                        // Non found, just change color
                        if (count == 0) {
                            change_color(n, c.numColors - 1, k);
                            c_min = 0;
                            break;
                        }

                        if (count < c_min || (count == c_min && rand() % 2 == 0)) {
                            c_min_n = static_cast<node_t>(n);
                            c_min = static_cast<node_t>(count);
                        }
                    }
                }

                dynamic_bitset<> component(g.getNumNodes());
                stack<vector<node_t>> q;
                q.emplace(1, c_min_n);

                while (!q.empty() && component.count() < budget) {
                    auto ns = q.top();
                    q.pop();

                    if (component.count() + ns.size() > budget)
                        continue;

                    for (auto n: ns) {
                        if (component.test(n))
                            continue;

                        component.set(n);

                        auto modifiedNb = g.adjacency[n] - component;
                        vector<vector<node_t>> colors(c.numColors);
                        for (auto n2 = modifiedNb.find_first();
                             n2 != dynamic_bitset<>::npos; n2 = modifiedNb.find_next(n2)) {
                            colors[c.coloring[n2]].push_back(n2);
                        }

                        sort(colors.rbegin(), colors.rend(),
                             [](vector<node_t> &v1, vector<node_t> &v2) { return v1.size() < v2.size(); });
                        for (auto &cv: colors) {
                            q.push(std::move(cv));
                        }
                    }
                }

                // Solve...
                auto sub_g = SubGraph(g, component, c.coloring);
                auto new_coloring = SatEncode::encode_partial(sub_g, c.numColors - 1, timeout, true, false,
                                                              INVALID_COLOR, 0,
                                                              false);
                if (!new_coloring.first.coloring.empty()) {
                    sub_g.map_coloring(new_coloring.first.coloring, c.coloring);
                    assert(g.verify(c.coloring));
                    cout << "Success" << endl;
                } else {
                    cout << "Failure" << endl;
                }
                c_partition.reset(c_min_n);
            }
        }
    }

//    color_t satBuildOrdering(const ConflictGraph &g, const vector<node_t> &clique, color_t ub, node_t budget = 2000,
//                             const unsigned int timeout = 30, const unsigned int min_space = 500,
//                             const bool always_run = true, const string &filename = "", const unsigned int posJumps=250) {
//        // TODO: Prioritize by degree
//        vector<color_t> coloring(g.getNumNodes(), INVALID_COLOR);
//        vector<dynamic_bitset<>> restricted;
//        dynamic_bitset<> done(g.getNumNodes());
//        restricted.reserve(g.getNumNodes());
//        vector<node_t> nodeMap;
//        unordered_map<node_t, node_t> rNodeMap;
//        rNodeMap.reserve(g.getNumNodes());
//        nodeMap.reserve(g.getNumNodes());
//        BucketQueue q(g.getNumNodes(), false);
//        vector<color_t> restrictions_store(g.getNumNodes());
//
//        color_t max_color = clique.size() - 1;
//
//        auto addNode = [&](node_t c_node) {
//            node_t mapped_idx = nodeMap.size();
//            nodeMap.push_back(c_node);
//            done[c_node] = true;
//            return mapped_idx;
//        };
//
//        auto getColor = [&](node_t c_node) {
//            restricted[c_node].flip();
//            auto cc = restricted[c_node].find_first();
//            if (cc == dynamic_bitset<>::npos) {
//                cc = restricted[c_node].size();
//            }
//            return cc;
//        };
//
//        auto restrictColor = [&](node_t c_node, color_t c_color) {
//            if (restricted[c_node].size() <= c_color + 1) {
//                if (restricted[c_node].size() == restricted[c_node].capacity())
//                    restricted[c_node].reserve(restricted[c_node].size() + 256);
//
//                restricted[c_node].resize(c_color + 1);
//            }
//
//            if (!restricted[c_node].test(c_color)) {
//                restricted[c_node][c_color] = true;
//                return true;
//            }
//            return false;
//        };
//
//        auto setColor = [&](node_t c_node, color_t c_color, bool update_queue = true) {
//            coloring[c_node] = c_color;
//            auto modified_nb = g.adjacency[c_node] - done;
//            for (auto n2 = modified_nb.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb.find_next(n2)) {
//                if (restricted[n2].size() <= c_color + 1) {
//                    if (restricted[n2].size() == restricted[n2].capacity())
//                        restricted[n2].reserve(restricted[n2].size() + 256);
//
//                    restricted[n2].resize(c_color + 1);
//                }
//
//                if (restrictColor(n2, c_color) && update_queue && ! g.reduced.test(n2)) {
//                    auto cnt = restricted[n2].count();
//                    q.change(cnt - 1, cnt, n2);
//                }
//            }
//        };
//
//        for (auto i : clique) {
//            addNode(i);
//        }
//
//        for (int i = 0; i < g.getNumNodes(); i++) {
//            restricted.emplace_back(0);
//            if (!done[i])
//                q.add(0, i);
//        }
//
//        for (node_t i = 0; i < clique.size(); i++) {
//            auto n = clique[i];
//            setColor(n, i);
//        }
//
//        node_t nodes_seen = 0;
//        bool exceeded = false;
//        vector<node_t> c_nodes;
//        c_nodes.reserve(min_space);
//
//        while (!q.empty()) {
//            if (! c_nodes.empty()) {
//                for(auto i=0; i < c_nodes.size(); i++) {
//                    auto x = c_nodes[i];
//                    addNode(x);
//                    auto cc = getColor(x);
//                    setColor(x, cc);
//
//                    for (auto j=i+1; j < c_nodes.size(); j++) {
//                        if (g.adjacency[x].test(c_nodes[j]))
//                            restrictColor(c_nodes[j], cc);
//                    }
//                }
//                c_nodes.clear();
//                assert(g.verify(coloring, false));
//            } else {
//                auto entry = q.next();
//                auto n = get<1>(entry);
//                auto cc = getColor(n);
//
//                if (cc > max_color) {
//                    exceeded = true;
//                    max_color = cc;
//                }
//
//                addNode(n);
//                setColor(n, cc);
//                nodes_seen++;
//            }
//            // TODO: Immediately run, if color reaches ub + 1 (i.e. 2 too high)
//            if (((((exceeded || always_run) && nodes_seen >= min_space)) && nodeMap.size() >= budget + clique.size()) ||
//                nodeMap.size() == g.getNumNodes()) {
////            if (((exceeded || (always_run && nodes_seen >= min_space)) && nodeMap.size() >= budget + clique.size()) ||
////                    nodeMap.size() == g.getNumNodes()) {
//                bool found_improvement = false;
//                auto c_idx = nodeMap.size() - 1;
//
//                while (! found_improvement) {
//                    Coloring new_color(vector<color_t>(), 0, vector<tuple<int, node_t>>());
//                    unique_ptr<SubGraph> sg = nullptr;
//
//                    if (nodeMap.size() == budget + clique.size()) {
//                        sg = std::make_unique<SubGraph>(g, done, coloring);
//                        vector<node_t> mappedClique;
//                        mappedClique.reserve(clique.size());
//
//                        for (auto n2 : clique) {
//                            mappedClique.push_back(sg->r_node_map[n2]);
//                        }
//
//                        new_color = SatEncode::encode_full(sg->sub_g, mappedClique, ub, timeout, "", true, false);
//                    } else {
//                        dynamic_bitset<> new_component(g.getNumNodes());
//                        for (auto i: nodeMap) {
//                            if (coloring[i] >= ub)
//                                new_component.set(i);
//                        }
//                        node_t cnt = 0;
//                        new_component.set(nodeMap.back());
//
//                        bool found = true;
//                        while (cnt < budget && found) {
//                            found = false;
//                            for (long i = c_idx; i >= 0 && cnt < budget; i--) {
//                                auto n2 = nodeMap[i];
//                                if (!new_component.test(n2)) {
//                                    if ((g.adjacency[n2] & new_component).any()) {
//                                        found = true;
//                                        new_component.set(n2);
//                                        cnt++;
//                                        break;
//                                    }
//                                }
//                            }
//                        }
//                        sg = std::make_unique<SubGraph>(g, new_component, coloring);
//                        new_color = SatEncode::encode_partial(*sg, ub, timeout, true, false).first;
//                        c_idx -= posJumps;
//                    }
//
//                    if (!new_color.coloring.empty()) {
//                        found_improvement = true;
//                        nodes_seen = 0;
//                        exceeded = false;
//
//                        // Use -1 so that sorting sorts the highest number of colors with the lowest index first.
//                        for (auto i = 0; i < restricted.size(); i++) {
//                            if (!done[i]) {
//                                restrictions_store[i] = restricted[i].count();
//                                restricted[i].reset();
//                            }
//                        }
//
//                        sg->map_coloring(new_color.coloring, coloring);
//
//                        max_color = 0;
//                        for (unsigned int i : nodeMap) {
//                            setColor(i, coloring[i], false);
//                            max_color = max(max_color, coloring[i]);
//                        }
//
//                        for (auto i = 0; i < restricted.size(); i++) {
//                            if (!done[i] && !g.reduced.test(i))
//                                q.change(restrictions_store[i], restricted[i].count(), i);
//                        }
//                    } else if (c_idx <= budget + clique.size()) {
//                        found_improvement = true;
//                        auto start = nodeMap.size();
//                        // TODO: Maybe move the nodes just so the neighbors don't prohibit a change?
//
//                        while(nodeMap.size() > start - posJumps) {
//                            auto c_n = nodeMap.back();
//                            nodeMap.pop_back();
//                            done.reset(c_n);
//                            restricted[c_n].reset();
//
//                            if (coloring[c_n] >= ub) {
//                                c_nodes.push_back(c_n);
//                            } else {
//                                q.add(0, c_n);
//                            }
//                            coloring[c_n] = INVALID_COLOR;
//                        }
//                        for (auto i = 0; i < restricted.size(); i++) {
//                            if (!done[i]) {
//                                restrictions_store[i] = restricted[i].count();
//                                restricted[i].reset();
//                            }
//                        }
//                        for (unsigned int i : nodeMap) {
//                            setColor(i, coloring[i], false);
//                        }
//                        for(auto c_n : c_nodes)
//                            done.set(c_n);
//
//                        for (auto i = 0; i < restricted.size(); i++) {
//                            if (!done[i] && !g.reduced.test(i))
//                                q.change(restrictions_store[i], restricted[i].count(), i);
//                        }
//
//                        cout << "Moved back" << endl;
//                    }
//                }
//
//                cout << nodeMap.size() << " Nodes, " << max_color + 1 << " Colors" << endl;
//
//                assert(g.verify(coloring, false));
//            }
//        }
//
//        assert(g.verify(coloring));
//        cout << "Required " << max_color + 1 << " Colors" << endl;
//
//        vector<tuple<int, node_t>> ordering;
//        ordering.reserve(g.getNumNodes());
//        for (auto i = 0; i < nodeMap.size(); i++)
//            ordering.emplace_back(i, nodeMap[i]);
//        Coloring newc(coloring, max_color + 1, ordering);
//        if (!filename.empty() && newc.numColors < ub) {
//            newc.store(filename, g);
//        }
//        tabuSearch(g, newc, min(newc.numColors, ub), filename);
//        return max_color + 1;
//    }

    void satOrderingSearch(const ConflictGraph& g, Coloring& start,
        node_t budget = 2000, const unsigned int timeout = 60, const string &filename = "") {
        unordered_map<node_t, node_t> nodePosition(g.getNumNodes());
        vector<tuple<color_t, node_t>> ordering(g.getNumNodes());
        vector<color_t> coloring = start.coloring;
        color_t c_colors = start.numColors;
        vector<dynamic_bitset<>> taboos(g.getNumNodes(), dynamic_bitset<>(c_colors + 1));
        vector<node_t> blockingPos(c_colors + 1);
        dynamic_bitset<> taken(c_colors + 1);
        dynamic_bitset<> done(g.getNumNodes());

        vector<LimitedList> tenures(g.getNumNodes(), LimitedList(c_colors / 2));

        for(auto i=0; i < g.getNumNodes(); i++) {
            nodePosition[get<1>(start.ordering[i])] = i;
            get<1>(ordering[i]) = get<1>(start.ordering[i]);
            get<0>(ordering[i]) = coloring[get<1>(start.ordering[i])];
        }

        node_t pos = INVALID_NODE;

        for(long long iteration=0; true; iteration++) {
            if (pos == INVALID_NODE) {
                // Find position of badly colored vertex
                for (pos = 0; pos < g.getNumNodes(); pos++) {
                    if (coloring[get<1>(ordering[pos])] == c_colors - 1)
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
                for (auto cl:tenures) {
                    if (cl.length >= c_colors - 3) {
                        cl.length = c_colors - 3;
                        cl.reset();
                    }
                }
                for (auto cl: taboos)
                    cl.reset();

                cout << "Eliminated color, now " << c_colors << " colors" << endl;
                for (pos = 0; pos < g.getNumNodes(); pos++) {
                    if (coloring[get<1>(ordering[pos])] == c_colors - 1)
                        break;
                }
                assert(g.verify(coloring));
                iteration = 1;
            }

            assert(pos < g.getNumNodes());
            node_t n = get<1>(ordering[pos]);
            bool sat_improved = false;
            node_t target_pos = INVALID_NODE;

            if (iteration > 0 && iteration % 1 == 0) {
                // Build component
                dynamic_bitset<> component(g.getNumNodes());
                component.set(n);
                node_t numNodes = 1;
                bool found = true;
                bool hit_start = false;

                while (numNodes < budget && found) {
                    found = false;
                    for (auto i = pos; i > 0; i--) {
                        auto n2 = get<1>(ordering[i - 1]);
                        if (!component.test(n2)) {
                            if ((g.adjacency[n2] & component).any()) {
                                found = true;
                                component.set(n2);
                                numNodes++;
                                break;
                            }
                        }
                    }
                }
                cout << component.count() << " " << pos << endl;

                auto sg = SubGraph(g, component, coloring, &nodePosition, pos);
                auto new_color = SatEncode::encode_partial(sg, c_colors - 2, timeout, true, false);
                // Coloring new_color(vector<color_t>(), 0, vector<tuple<int, node_t>>());

                if (!new_color.first.coloring.empty()) {
                    sat_improved = true;
                    sg.map_coloring(new_color.first.coloring, coloring);
                    node_t min_idx = INVALID_NODE;
                    node_t max_idx = 0;

                    for (auto cn = 0; cn < new_color.first.coloring.size(); cn++) {
                        auto cidx = nodePosition[sg.node_map[cn]];
                        get<0>(ordering[cidx]) = new_color.first.coloring[cn];
                        min_idx = min(min_idx, cidx);
                        max_idx = max(max_idx, cidx);
                    }

                    sort(ordering.begin() + min_idx, ordering.begin() + max_idx);
                    for (auto cidx = min_idx; cidx < max_idx + 1; cidx++) {
                        nodePosition[get<1>(ordering[cidx])] = cidx;
                    }
                    target_pos = min_idx;
                    pos = INVALID_NODE;
                }
            }
            if (!sat_improved) {
                for (auto &ce: blockingPos) {
                    ce = INVALID_NODE;
                }

                // Check where we could move the node to
                for (auto n2 = g.adjacency[n].find_first();
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
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

                for (auto cc = c_colors - 2; cc > 0; cc--) {
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
                    target_pos = blockingPos[max_cc];
                    cout << "Pos: " << pos << " to " << target_pos << "\t" << n << " to " << max_cc << " (" << c_colors
                         << ")" << endl;
                    // Rearrange
                    for (auto c_pos = pos; c_pos > target_pos; c_pos--) {
                        auto &c_target = ordering[c_pos - 1];
                        nodePosition[get<1>(c_target)] = c_pos;
                        swap(ordering[c_pos], ordering[c_pos - 1]);
                    }
                    get<1>(ordering[target_pos]) = n;
                    nodePosition[n] = target_pos;

                    // Set taboos
                    if (!taboos[n].test(max_cc)) {
                        taboos[n].set(max_cc);

//                    auto n_taboo_old = tenures[n].add(max_cc);
//                    if (n_taboo_old != INVALID_NODE)
//                        taboos[n].reset(n_taboo_old);
                    }

                    for (auto n2 = g.adjacency[n].find_first();
                         n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                        if (nodePosition[n2] > target_pos) {
                            if (!taboos[n2].test(coloring[n2])) {
                                taboos[n2].set(coloring[n2]);
//                            auto n2_taboo_old = tenures[n2].add(coloring[n2]);
//                            if (n2_taboo_old != INVALID_NODE)
//                                taboos[n2].reset(n2_taboo_old);
                            }
                        }
                    }
                }
            }

            if (target_pos != INVALID_NODE) {
                // Propagate
                done.reset();
                for (node_t i = 0; i < target_pos; i++) {
                    done.set(get<1>(ordering[i]));
                }

                pos = INVALID_NODE;
                for (node_t i = target_pos; i < g.getNumNodes(); i++) {
                    auto cn = get<1>(ordering[i]);
                    auto modified = g.adjacency[cn] & done;
                    taken.reset();
                    for (auto n2 = modified.find_first();
                         n2 != dynamic_bitset<>::npos; n2 = modified.find_next(n2)) {
                        taken[coloring[n2]] = true;
                    }

                    taken.flip();
                    auto cc = taken.find_first();
                    if (cc >= c_colors - 1) {
                        pos = i;
                        break;
                    }
                    coloring[cn] = static_cast<int>(cc);
                    get<0>(ordering[i]) = coloring[cn];
                    done.set(cn);
                }
            }
        }
    }

    void satImproveOrdering(const ConflictGraph &g, Coloring &coloring, const vector<node_t> &clique,
                            node_t budget = 2000, const unsigned int timeout = 60, const string &filename = "", const unsigned int posJumps=250) {
        color_t cbound = coloring.numColors - 1;
        vector<tuple<node_t, node_t>> nodePos;
        nodePos.reserve(g.getNumNodes());

        for(auto i=0; i < coloring.ordering.size(); i++){
            auto n = get<1>(coloring.ordering[i]);
            nodePos.emplace_back(i, n);
        }
        bool changed = true;
        auto c_coloring = coloring.coloring;
        node_t prev_node = INVALID_NODE;
        node_t seen = 0;

        while(changed) {
            changed = true;

            // Find first node exceeding bound
            node_t cidx = 0;
            for (; cidx < nodePos.size(); cidx++) {
                if (c_coloring[get<1>(nodePos[cidx])] > cbound - 1) {
                    break;
                }
            }
            if (cidx == nodePos.size())
                break;

            node_t n = get<1>(nodePos[cidx]);

            // Reset colors
            for(auto i=cidx+1; i < c_coloring.size(); i++)
                c_coloring[get<1>(nodePos[i])] = INVALID_COLOR;

            // Build component
            dynamic_bitset<> component(g.getNumNodes());
            component.set(n);
            node_t numNodes = 1;
            bool found = true;
            bool hit_start = false;
            auto startIdx = min(cidx+budget/2, static_cast<node_t>(nodePos.size()));

            seen = prev_node == n ? seen + 1 : 0;
            startIdx -= seen * posJumps;

            while(numNodes < budget && found) {
                found = false;
                for (auto i=startIdx; i > 0; i--) {
                    auto n2 = get<1>(nodePos[i-1]);
                    if (! component.test(n2)) {
                        if ((g.adjacency[n2] & component).any()) {
                            found = true;
                            component.set(n2);
                            numNodes++;
                            break;
                        }
                    }
                }
                if (! found) {
                    startIdx += posJumps;
                    hit_start = true;
                }
            }

            auto sg = SubGraph(g, component, c_coloring);
            auto new_color = SatEncode::encode_partial(sg, c_coloring[n], timeout, true, false);
            if (new_color.first.coloring.empty()) {
                cout << "Failed to improve " << endl;
                if (hit_start) {
                    seen = 0;
                    // Find pos of last node with a lower color
                    node_t max_pos = 0;
                    color_t node_color = c_coloring[n];
                    for(auto i=0; i < cidx; i++) {
                        if (c_coloring[get<1>(nodePos[i])] < n && g.adjacency[n].test(get<1>(nodePos[i])))
                            max_pos = i;
                    }

                    // Sort back...
                    for(auto i=cidx; i > 0 && i > max_pos; i--) {
                        auto na = nodePos[i];
                        auto nb = nodePos[i-1];
                        c_coloring[get<1>(nodePos[i])] = INVALID_COLOR;
                        c_coloring[get<1>(nodePos[i-1])] = INVALID_COLOR;
                        swap(nodePos[i], nodePos[i-1]);
                    }
                    cout << "Swapped back from " << cidx << " to " << max_pos << endl;
                }
            } else {
                sg.map_coloring(new_color.first.coloring, c_coloring);
                assert(g.verify(c_coloring, false));
            }

            // Propagate
            dynamic_bitset<> done(g.getNumNodes());
            dynamic_bitset<> taken(cbound + 1);

            color_t n_max_color = 0;
            for(auto& entry : nodePos) {
                auto cn = get<1>(entry);
                if (c_coloring[cn] != INVALID_COLOR) {
                    n_max_color = max(n_max_color, c_coloring[cn]);
                    done.set(cn);
                } else {
                    auto modified = g.adjacency[cn] & done;
                    for (auto n2 = modified.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified.find_next(n2)) {
                        taken[c_coloring[n2]] = true;
                    }

                    taken.flip();
                    auto cc = taken.find_first();
                    if (cc == dynamic_bitset<>::npos) {
                        if (taken.size() == taken.capacity()) {
                            taken.reserve(taken.capacity() + 64);
                        }
                        cc = taken.size();
                        taken.push_back(false);
                    }

                    c_coloring[cn] = static_cast<int>(cc);
                    n_max_color = max(n_max_color, c_coloring[cn]);
                    done.set(cn);
                    taken.reset();
                }
                get<0>(entry) = c_coloring[cn];
            }
            changed = true;
            sort(nodePos.begin(), nodePos.end());

            if (n_max_color + 1 <= cbound) {
                cout << "Improved to " << n_max_color + 1 << " colors"<<endl;
                cbound = n_max_color;
            }
            if (n_max_color > cbound) {
                cout << "Increased to " << n_max_color + 1 << " colors" << endl;
            }
            assert(g.verify(c_coloring, true));
        }
    }

    bool tabuSearchSat(const ConflictGraph &g, Coloring &start, color_t ub, std::mutex &sync, unsigned int &cycle,
                       const string &export_path = "", node_t seed = 0, unsigned int iterations = 100000,
                       unsigned int retention = 10, unsigned int resetIterations = 2500,
                       color_t failed_limit = INVALID_COLOR, unsigned int timeout = 60,
                       unsigned int later_limit_color = 2,
                       unsigned int first_limit_nodes = 1000, unsigned int later_limit_nodes = 2000,
                       unsigned int first_increment = 50, unsigned int later_increment = 100, bool useTaboos = false,
                       bool useFlexibleSelection = false, bool use_cadical=false) {

        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();

        // TODO: What in case of early failure?
        auto c_retention = retention;
        int eliminatedColors = 0;
        unordered_set<int> usedColors(start.numColors);
        auto originalColors = start.numColors;
        bool failed = false;
        node_t successes = 0;
        node_t max_success_nodes = 0;
        auto my_cycle = cycle;

        while(usedColors.size() < start.numColors && usedColors.size() < failed_limit) {
            // Wait for any write to finish
            sync.lock();
            vector<color_t> current_coloring(start.coloring);
            auto my_num_colors = start.numColors;
            sync.unlock();

            vector<dynamic_bitset<>> partitions(my_num_colors, dynamic_bitset<>(g.getNumNodes()));
            vector<dynamic_bitset<>> taboos;
            vector<tuple<unsigned int, node_t, color_t>> tabuQueue;

            vector<vector<node_t>> neighborhood_counts_real(g.getNumNodes(), vector<node_t>(my_num_colors, 0));
            // Temporary coloring as to not mess up ours
            color_t selected_color = INVALID_COLOR;

            taboos.reserve(g.getNumNodes() * my_num_colors);
            node_t c_taboo_idx = 0;
            unsigned int iteration = 0;
            my_cycle = cycle;

            dynamic_bitset<> flexible(g.getNumNodes());

            auto changeColor = [&](node_t node, color_t oldColor, color_t newColor) {
                current_coloring[node] = newColor;
                partitions[oldColor].reset(node);
                partitions[newColor].set(node);
                taboos[node].set(oldColor);
                tabuQueue.emplace_back(iteration + c_retention, node, oldColor);
                bool is_flex = flexible.test(node);

                // If node is flexible, it wasn't counted
                for (auto n2=g.adjacency[node].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {
                    neighborhood_counts_real[n2][newColor] += 1;
                    neighborhood_counts_real[n2][oldColor] -= 1;

                    if (neighborhood_counts_real[n2][oldColor] == 0 && oldColor != selected_color && oldColor != current_coloring[n2]) {
                        flexible.set(n2);
                    }
                    // Removed possibility for flexibility
                    if (neighborhood_counts_real[n2][newColor] == 1 && flexible.test(n2)) {
                        flexible.reset(n2);
                        for (color_t k = 0; k < my_num_colors; k++) {
                            if (k != selected_color && k != current_coloring[n2] &&
                                neighborhood_counts_real[n2][k] == 0) {
                                flexible.set(n2);
                                break;
                            }
                        }
                    }
                }
            }; // End changeColor

            for (int n = 0; n < g.getNumNodes(); n++) {
                partitions[current_coloring[n]].set(n);
                taboos.emplace_back(my_num_colors);
                for (auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    neighborhood_counts_real[n2][current_coloring[n]] += 1;
                }
            }

            while (iteration < iterations) {
                if (my_cycle < cycle)
                    break;

                vector<dynamic_bitset<>> flexible_counts(g.getNumNodes(), dynamic_bitset<>(g.getNumNodes()));

                for(node_t n=0; n < g.getNumNodes(); n++) {
                    for(color_t k=0; k < start.numColors; k++) {
                        if (k != current_coloring[n] && neighborhood_counts_real[n][k] == 0) {
                            flexible.set(n);
                            for (color_t k2 = 0; k2 < start.numColors; k2++) {
                                if (k2 != k)
                                    flexible_counts[k2].set(n);
                            }
                        }
                    }
                }
                cout << seed << ": " << flexible.count() << " flexible vertices" << endl;

                dynamic_bitset<>::size_type min_count;

                // Pick color with fewest elements
                vector<tuple<node_t, int, color_t>> color_counts;
                color_counts.reserve(partitions.size());

                for (int k = 0; k < partitions.size(); k++) {
                    if (partitions[k].empty() || usedColors.find(k) != usedColors.end())
                        continue;

                    color_counts.emplace_back((partitions[k] - flexible_counts[k]).count(), rand(), k);
                }
                sort(color_counts.begin(), color_counts.end());
                selected_color = get<2>(color_counts[seed]);
                auto &current_partition = partitions[selected_color];

                flexible = flexible_counts[selected_color];

                // Trace 1-paths
                dynamic_bitset<> removable(g.getNumNodes());
                dynamic_bitset<> queue(g.getNumNodes());
                for(auto n=current_partition.find_first(); n != dynamic_bitset<>::npos; n = current_partition.find_next(n)) {
                    if (flexible.test(n))
                        continue;

                    removable.reset();
                    removable.set(n);
                    queue.reset();
                    queue.set(n);
                    unordered_map<node_t, node_t> reverse;
                    node_t found_node = INVALID_NODE;
                    color_t goal_color = INVALID_COLOR;
                    while(queue.any() && found_node == INVALID_NODE) {
                        auto n2 = queue.find_first();
                        queue.reset(n2);
                        for(color_t k=0; k < my_num_colors; k++) {
                            if (neighborhood_counts_real[n2][k] == 0) {
                                assert((g.adjacency[n2] & partitions[k]).count() == 0);
                                found_node = n2;
                                goal_color = k;
                                break;
                            } else if (neighborhood_counts_real[n2][k] == 1) {
                                auto ccross = (g.adjacency[n2] & partitions[k]);
                                auto ccross_cnt = ccross.count();
                                assert(ccross_cnt == 1);
                                auto cnb = ccross.find_first();
                                if (current_coloring[cnb] != selected_color && !removable.test(cnb)) {
                                    removable.set(cnb);
                                    queue.set(cnb);
                                    reverse[cnb] = n2;
                                }
                            }
                        }
                    }

                    if (found_node != INVALID_NODE) {
                        color_t nc = goal_color;
                        while (true) {
                            auto oc = current_coloring[found_node];
                            changeColor(found_node, oc, nc);

                            nc = oc;
                            if (found_node == n)
                                break;
                            found_node = reverse[found_node];
                        }
                    }
                }
//
//                for (node_t n=0; n < g.getNumNodes(); n ++ ) {
//                    if (current_coloring[n] == selected_color)
//                        current_coloring[n] = INVALID_COLOR;
//                }
//                assert(g.verify(current_coloring, false));

                auto startCount = current_partition.count();
                bool swapped = false; // Used to limit the any calls on the partition
                //c_retention = startCount * 6 / 10;

                // Try to eliminate color
                while (iteration < iterations && (swapped || partitions[selected_color].any())) {
                    if (my_cycle < cycle)
                        break;

                    swapped = false;
//                    if (iteration % 100 == 0)
//                        c_retention = current_partition.count() * 6 / 10;

                    // Remove tabus after retention
                    while (c_taboo_idx < tabuQueue.size() && get<0>(tabuQueue[c_taboo_idx]) < iteration) {
                        taboos[get<1>(tabuQueue[c_taboo_idx])][get<2>(tabuQueue[c_taboo_idx])] = false;
                        c_taboo_idx++;
                    }

                    int c_min = -1;
                    int c_min_node = -1;
                    int alternative_color = -1;

                    cout << seed << ": Color " << selected_color << ", Count " << current_partition.count() << endl;

                    // Find node with the smallest number of neighbors colored in an alternative color
                    for (auto n = current_partition.find_first();
                         n != boost::dynamic_bitset<>::npos && c_min != 0; n = current_partition.find_next(n)) {
                        for (auto k = 0; k < my_num_colors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts_real[n][k];

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
                        //cout << seed << ": Early fail to eliminate color " << selected_color << endl;
                        break;
                    }

                    if (c_min >= 1) {
                        swapped = true;
                        dynamic_bitset<> component(g.getNumNodes());
                        node_t cnt = 0;
                        bool split_used = false;
                        bool recursive_step = false;
                        bool solved = false;
                        component.set(c_min_node);

                        if (c_min < first_limit_nodes || later_limit_color > 1) {
                            vector<dynamic_bitset<>> nb_comp;
                            nb_comp.reserve(my_num_colors);

                            vector<tuple<node_t, int, color_t>> nbs;
                            nbs.reserve(my_num_colors);
                            for (auto k = 0; k < my_num_colors; k++) {
                                if (k != selected_color && !taboos[c_min_node].test(k)) {
                                    if (useFlexibleSelection)
                                        nbs.emplace_back(((g.adjacency[c_min_node] & partitions[k]) - flexible).count(), rand(), k);
                                    else
                                        nbs.emplace_back(((g.adjacency[c_min_node] & partitions[k]) - g.reduced).count(), rand(), k);
//                                    if (nbs.size() > first_limit_color) {
//                                        sort(nbs.begin(), nbs.end());
//                                        nbs.pop_back();
//                                    }
                                }
                            }
                            sort(nbs.begin(), nbs.end());

                            //for (int i = 0; i < first_limit_color && i < nbs.size(); i++) {
                            for (int i = 0; i < nbs.size(); i++) {
                                if (neighborhood_counts_real[c_min_node][get<2>(nbs[i])] + cnt < first_limit_nodes) {
                                    auto ncp = g.adjacency[c_min_node] & partitions[get<2>(nbs[i])];
                                    nb_comp.push_back(ncp);
                                    component |= ncp;
                                    cnt += neighborhood_counts_real[c_min_node][get<2>(nbs[i])];
                                    if (i >= 1)
                                        split_used = true;
                                } else {
                                    break;
                                }
                            }
                            if (!nbs.empty())
                                c_min = (partitions[get<2>(nbs[0])] & g.adjacency[c_min_node]).count();

                            if (cnt > 1 || (cnt == 1 && later_limit_color > 1)) {
                                for(auto i=0; i < nb_comp.size(); i++) {
                                    vector<tuple<node_t, int, color_t>> sub_nb;
                                    sub_nb.reserve(my_num_colors);

                                    dynamic_bitset<> c_adjacency(g.getNumNodes());
                                    for (auto n=nb_comp[i].find_first(); n != dynamic_bitset<>::npos; n=nb_comp[i].find_next(n)) {
                                        c_adjacency |= g.adjacency[n];
                                    }

                                    for (auto k = 0; k < my_num_colors; k++) {
                                        if (k != selected_color) {
                                            auto n_cnt = useFlexibleSelection ? (((c_adjacency & partitions[k]) - flexible) - component).count()
                                                    :(((c_adjacency & partitions[k]) - g.reduced) - component).count();

                                            if (n_cnt > 0) {
                                                sub_nb.emplace_back(n_cnt, rand(),k);
                                                // TODO: For dynamically choosing the branching, this has to be adapted as well!
                                                if (sub_nb.size() > later_limit_color) {
                                                    sort(sub_nb.begin(), sub_nb.end());
                                                    sub_nb.pop_back();
                                                }
                                            }
                                        }
                                    }
                                    sort(sub_nb.begin(), sub_nb.end());

                                    for (int j = 0; j < later_limit_color && j < sub_nb.size(); j++) {
                                        if (get<0>(sub_nb[j]) + cnt < later_limit_nodes) {
                                            recursive_step = true;
                                            auto ncp = (c_adjacency & partitions[get<2>(sub_nb[j])]) - component;
                                            nb_comp.push_back(ncp);
                                            component |= ncp;
                                            cnt += ncp.count();
                                            if (i >= 2)
                                                split_used = true;
                                        } else {
                                            break;
                                        }
                                    }
                                }
                            }
                            if (cnt > 0 && split_used && recursive_step) {
                                auto sg = SubGraph(g, component, current_coloring, nullptr, INVALID_NODE, taboos[0].size() - 1);

                                // Make sure current node gets a different color and that all nodes can take this color.
                                bool found_c_node = false;
                                node_t mapped_min_node = sg.r_node_map[c_min_node];
                                dynamic_bitset<> found(sg.sub_g.getNumNodes());
                                for(auto& cEx : sg.exceptions) {
                                    found.set(cEx.node);
                                    if (cEx.node == mapped_min_node) {
                                        found_c_node = true;
                                        cEx.colors.set(selected_color);
                                    } else {
                                        cEx.colors.reset(selected_color);
                                        if (useTaboos) {
                                            auto revn = sg.node_map[cEx.node];
                                            taboos[revn].reset(current_coloring[revn]);
                                            cEx.colors |= taboos[revn];
                                        }
                                    }
                                }
                                if (! found_c_node) {
                                    sg.exceptions.emplace_back(mapped_min_node, dynamic_bitset<>(g.getNumNodes()));
                                    sg.exceptions.back().colors.set(selected_color);
                                }

                                if (useTaboos) {
                                    found.set(mapped_min_node);
                                    found.flip();
                                    for (auto c_sn = found.find_first();
                                         c_sn != dynamic_bitset<>::npos; c_sn = found.find_next(c_sn)) {
                                        auto revn = sg.node_map[c_sn];
                                        taboos[revn].reset(current_coloring[revn]);
                                        sg.exceptions.emplace_back(c_sn, dynamic_bitset<>(g.getNumNodes()));
                                        sg.exceptions.back().colors |= taboos[revn];
                                    }
                                }

                                // Find a new coloring
                                auto new_color = use_cadical ? SatEncodeCadical::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min) :
                                                 SatEncode::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min);
                                node_t new_selected_count = 0;
                                if (! new_color.first.coloring.empty()) {
                                    //cout << seed << ": Solved" << endl;
                                    solved = true;
                                    for(auto i=0; i < new_color.first.coloring.size(); i++) {
                                        auto oldColor = current_coloring[sg.node_map[i]];
                                        if(mapped_min_node == i) {
                                            assert(oldColor != new_color.first.coloring[i]);
                                        }

                                        if (oldColor != new_color.first.coloring[i]) {
                                            changeColor(sg.node_map[i], oldColor, new_color.first.coloring[i]);
                                            if (new_color.first.coloring[i] == selected_color)
                                                new_selected_count++;
                                        }
                                    }

                                    if (new_selected_count <= c_min) {
                                        if (sg.sub_g.adjacency.size() > max_success_nodes)
                                            max_success_nodes = sg.sub_g.adjacency.size();

                                        successes += 1;
                                        failed = false;

                                        if (successes > 5 && max_success_nodes > later_limit_nodes - later_increment && later_limit_nodes < 3000) {
                                            first_limit_nodes += first_increment;
                                            later_limit_nodes += later_increment;
                                            successes = 0;
                                            cout << seed << ": Switched to " << first_limit_nodes << " " << later_limit_nodes
                                                 << endl;
                                        }
                                    }
                                }
                                if (new_selected_count > 1 || new_color.first.coloring.empty()) {
                                    successes = 0;
                                    if (failed) {
                                        if (first_limit_nodes > 2*first_increment) {
                                            first_limit_nodes -= first_increment;
                                            later_limit_nodes -= later_increment;
                                            cout << seed << ": Switched to " << first_limit_nodes << " " << later_limit_nodes
                                                 << endl;
                                        }
                                        failed = false;
                                    } else {
                                        failed = true;
                                    }
                                }
                            }
                        }

                        if (! solved) {
                            changeColor(c_min_node, selected_color, alternative_color);

                            auto colored_neighbors = partitions[alternative_color] & g.adjacency[c_min_node];

                            for (auto n = colored_neighbors.find_first();
                                 n != boost::dynamic_bitset<>::npos; n = colored_neighbors.find_next(n)) {
                                changeColor(n, alternative_color, selected_color);
                            }
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
                                neighborhood_counts_real[n][selected_color] = neighborhood_counts_real[n][c_max_color];
                                taboos[n].reset(selected_color);
                            }
                        }
                        assert(g.verify(current_coloring));

                        partitions.pop_back();
                        start.coloring = current_coloring;
                        start.numColors -= 1;
                        my_num_colors = start.numColors;
                        // TODO: Adapt ordering? For the return would be sufficient...
                        if (!export_path.empty() && start.numColors < ub) {
                            start.store(export_path, g);
                        }
                        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                        cout << seed << "::"<< std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << "::Eliminated " << selected_color << ", Remaining " << partitions.size() << endl;
                        eliminatedColors++;
                    }
                    sync.unlock();
                } else if (iteration >= iterations) {
                    cout << seed << ": Failed to eliminate color " << selected_color << endl;
                    usedColors.insert(selected_color);
                }
            }
        }
        cout << "Eliminated " << eliminatedColors << " Colors from originally " << originalColors << endl;
        return eliminatedColors > 0;
    }

    void contractionSat(const ConflictGraph& g, Coloring& start, node_t budget = 2000) {
        while (true) {
            auto ng = ConflictGraph(g.getNumNodes());
            copy(g.adjacency.begin(), g.adjacency.end(), ng.adjacency.begin());
            dynamic_bitset<> done(g.getNumNodes());
            node_t cnt = 0;

            vector<dynamic_bitset<>> partitions(start.numColors, dynamic_bitset<>(g.getNumNodes()));
            for (node_t n = 0; n < g.getNumNodes(); n++)
                partitions[start.coloring[n]].set(n);

            // Contract nodes
            while (cnt < g.getNumNodes() - budget) {
                // Find random node
                auto n = rand() % g.getNumNodes();
                while (done[n]) {
                    auto n2 = done.find_next(n);
                    if (n2 == dynamic_bitset<>::npos) {
                        n = 0;
                    } else {
                        n++;
                        if (n2 > n) {
                            break;
                        }
                    }
                }

                if (partitions[start.coloring[n]].count() == 1) {
                    done.set(n);
                } else {
                    auto n2 = rand() % g.getNumNodes();
                    while (start.coloring[n2] != start.coloring[n] || n == n2) {
                        n2++;
                        if (n2 >= g.getNumNodes())
                            n2 = 0;
                    }
                    done.set(n2);
                    ng.adjacency[n] |= ng.adjacency[n2];
                    ng.adjacency[n2].reset();
                }
            }
        }
    }

    bool tabuSearchSat2(const ConflictGraph &g, Coloring &start, color_t ub, std::mutex &sync, unsigned int &cycle, dynamic_bitset<>& seed_sync,
                        const string &export_path = "", node_t seed = 0, unsigned int iterations = 100000,
                        unsigned int retention = 10, unsigned int resetIterations = 2500,
                        color_t failed_limit = INVALID_COLOR, unsigned int timeout = 60,
                        unsigned int later_limit_color = 2,
                        unsigned int first_limit_nodes = 1000, unsigned int later_limit_nodes = 2000,
                        unsigned int first_increment = 50, unsigned int later_increment = 100, bool useTaboos = false,
                        bool useFlexibleSelection = false, bool use_allowed = false, unsigned int pre_iterations=100000, bool use_cadical= false,
                        node_t tp_branch_limit=0, bool sync_seed = false) {

        std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();
        // TODO: What in case of early failure?
        auto c_retention = retention;
        int eliminatedColors = 0;
        auto originalColors = start.numColors;
        node_t failures = 0;
        node_t successes = 0;
        node_t max_success_cnt = 0;
        auto my_cycle = cycle;

        while(seed_sync.find_first() < start.numColors) {
            // Wait for any write to finish
            sync.lock();
            vector<color_t> current_coloring(start.coloring);
            auto my_num_colors = start.numColors;
            sync.unlock();

            vector<dynamic_bitset<>> partitions(my_num_colors, dynamic_bitset<>(g.getNumNodes()));
            vector<dynamic_bitset<>> taboos;
            vector<tuple<unsigned int, node_t, color_t>> tabuQueue;

            vector<vector<node_t>> neighborhood_counts(g.getNumNodes(), vector<node_t>(start.numColors, 0));
            vector<vector<node_t>> neighborhood_counts_real(g.getNumNodes(), vector<node_t>(my_num_colors, 0));
            // Temporary coloring as to not mess up ours
            color_t selected_color = INVALID_COLOR;

            taboos.reserve(g.getNumNodes() * my_num_colors);
            node_t c_taboo_idx = 0;
            unsigned int iteration = 0;
            my_cycle = cycle;

            dynamic_bitset<> flexible(g.getNumNodes());

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

            for (int n = 0; n < g.getNumNodes(); n++) {
                partitions[current_coloring[n]].set(n);
                taboos.emplace_back(my_num_colors);
                for (auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    neighborhood_counts_real[n2][current_coloring[n]] += 1;
                }
            }

            while (iteration < iterations + pre_iterations) {
                if (my_cycle < cycle)
                    break;

                vector<dynamic_bitset<>> flexible_counts(g.getNumNodes(), dynamic_bitset<>(g.getNumNodes()));

                for (int n = 0; n < g.getNumNodes(); n++) {
                    for (color_t k = 0; k < my_num_colors; k++)
                        neighborhood_counts[n][k] = neighborhood_counts_real[n][k];
                }

                flexible.reset();
                for (node_t n = 0; n < g.getNumNodes(); n++) {
                    for (color_t k = 0; k < my_num_colors; k++) {
                        if (k != current_coloring[n] && neighborhood_counts_real[n][k] == 0) {
                            flexible.set(n);
                            for (color_t k2 = 0; k2 < my_num_colors; k2++) {
                                if (k2 != k)
                                    flexible_counts[k2].set(n);
                            }
                        }
                    }
                }
                cout << seed << ": " << flexible.count() << " flexible vertices" << endl;

                dynamic_bitset<>::size_type min_count;

                // Pick color with fewest elements
                vector<tuple<node_t, int, color_t>> color_counts;
                color_counts.reserve(partitions.size());

                for (int k = 0; k < partitions.size(); k++) {
                    if (partitions[k].empty() || !seed_sync.test(k))
                        continue;

                    color_counts.emplace_back((partitions[k] - g.reduced).count(), rand(), k);
                }
                sort(color_counts.begin(), color_counts.end());
                if (!sync_seed) {
                    selected_color = get<2>(color_counts[seed]);
                    seed_sync.reset(selected_color);
                } else {
                    selected_color = INVALID_COLOR;
                    sync.lock();
                    for(auto& cc : color_counts) {
                        if (seed_sync.test(get<2>(cc))) {
                            selected_color = get<2>(cc);
                            seed_sync.reset(selected_color);
                            break;
                        }
                    }
                    sync.unlock();
                    if (selected_color == INVALID_COLOR)
                        break;
                }

                auto &current_partition = partitions[selected_color];

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

                unordered_map<node_t, pair<node_t, color_t>> path;
                node_t tp_depth_limit = 3;
                dynamic_bitset<> dfs_found(g.getNumNodes());
                deque<node_t> last_nodes_used_queue(retention);
                dynamic_bitset<> last_nodes_used(g.getNumNodes());
                dynamic_bitset<> last_nodes(g.getNumNodes());

                std::function<dynamic_bitset<> (node_t, node_t)> traceTwoPath = [&] (node_t node, node_t depth) {
                    vector<pair<node_t, node_t>> dfs_queue;
                    dfs_queue.emplace_back(node, node);
                    dfs_found.set(node);
                    node_t last_node = node;
                    //vector<tuple<node_t, node_t, node_t>> tp_queue;

                    while(!dfs_queue.empty()) {
                        auto n2 = dfs_queue.back();
                        dfs_queue.pop_back();

                        while(last_node != n2.second) {
                            // cout << "Retrace from "<< last_node << " to " << n2.second << endl;
                            if (depth < tp_depth_limit) {
                                for (color_t k = 0; k < my_num_colors; k++) {
                                    if (k == current_coloring[last_node] || k == selected_color)
                                        continue;

                                    if (depth < tp_depth_limit && neighborhood_counts_real[last_node][k] > 1 && neighborhood_counts_real[last_node][k] <= tp_branch_limit) {
                                        auto cnbs = (g.adjacency[last_node] & partitions[k]);
                                        bool failed = false;
                                        vector<node_t> nb_list;
                                        nb_list.reserve(tp_branch_limit);
                                        for(auto cnb = cnbs.find_first(); cnb != dynamic_bitset<>::npos; cnb = cnbs.find_next(cnb)) {
                                            if (dfs_found.test(cnb)) {
                                                failed = true;
                                                break;
                                            }
                                            nb_list.push_back(cnb);
                                        }

                                        if (!failed) {
                                            changeColor(last_node, selected_color, k);
                                            vector<dynamic_bitset<>> results;
                                            results.reserve(tp_branch_limit);
                                            for(auto cnb: nb_list) {
                                                changeColor(cnb, k, selected_color);
                                                path[cnb] = {last_node, k};
                                                dfs_found.set(cnb);
                                            }

                                            for(auto cnb: nb_list) {
                                                auto c_result = traceTwoPath(cnb, depth+1);
                                                if (c_result.empty())
                                                    break;
                                                results.push_back(c_result);
                                            }

                                            if (results.size() < nb_list.size()) {
                                                for(auto c_idx=0; c_idx < results.size(); c_idx++) {
                                                    for (auto csube = results[c_idx].find_first();
                                                         csube != dynamic_bitset<>::npos; csube = results[c_idx].find_next(
                                                            csube)) {
                                                        node_t csube_last = csube;
                                                        while (csube_last != nb_list[c_idx]) {
                                                            dfs_found.reset(csube_last);
                                                            assert(path.find(csube_last) != path.end());
                                                            auto csube_prev = path[csube_last];

                                                            if (current_coloring[csube_last] == csube_prev.second)
                                                                break;
                                                            changeColor(csube_last, current_coloring[csube_last],
                                                                        csube_prev.second);
                                                            csube_last = csube_prev.first;
                                                        }
                                                    }
                                                }

                                                for(auto cnb: nb_list) {
                                                    changeColor(cnb, current_coloring[cnb], k);
                                                    dfs_found.reset(cnb);
                                                }
                                                changeColor(last_node, k, selected_color);
                                            } else {
                                                for(auto& c_results: results)
                                                    results.back() |= c_results;

                                                return results.back();
                                            }
                                        }
                                    }
                                }
                            }

                            auto prevNode = path[last_node];
                            changeColor(last_node, current_coloring[last_node], prevNode.second);
                            changeColor(prevNode.first, current_coloring[prevNode.first], selected_color);
                            if (depth == 0)
                                dfs_found.reset(last_node);
                            last_node = prevNode.first;
                        }
//                        if (current_coloring[last_node] != selected_color)
//                            changeColor(last_node, current_coloring[last_node], selected_color);

                        last_node = n2.first;
                        if (depth == 0 || n2.first != n2.second)
                            path[n2.first] = {n2.second, current_coloring[n2.first]};
                        dfs_found.set(n2.first);

                        changeColor(n2.second, selected_color, current_coloring[n2.first]);
                        changeColor(n2.first, current_coloring[n2.first], selected_color);

                        for(color_t k=0; k < my_num_colors; k++) {
                            if (k == current_coloring[n2.first] || k == selected_color)
                                continue;

                            if (neighborhood_counts_real[n2.first][k] == 0) {
                                assert((g.adjacency[n2.first] & partitions[k]).count() == 0);
                                changeColor(n2.first, selected_color, k);
                                dynamic_bitset<> endpoints(g.getNumNodes());
                                endpoints.set(n2.first);
                                return endpoints;
                            } else if (neighborhood_counts_real[n2.first][k] == 1) {
                                assert((g.adjacency[n2.first] & partitions[k]).count() == 1);
                                auto nb = (g.adjacency[n2.first] & partitions[k]).find_first();

                                if (!dfs_found.test(nb)) {
                                    dfs_queue.emplace_back(nb, n2.first);
                                }
                            }
                        }
                    }

                    while (last_node != node) {
                        auto prevNode = path[last_node];
                        changeColor(last_node, current_coloring[last_node], prevNode.second);
                        dfs_found.reset(last_node);
                        last_node = prevNode.first;
                    }
                    if (current_coloring[node] != selected_color)
                        changeColor(node, current_coloring[node], selected_color);

                    return dynamic_bitset<>(0);
                }; // End trace two path


                auto runTwoPath = [&] () {
                    bool changed = true;
                    unordered_map<node_t, vector<node_t>> path_trace;
                    vector<node_t> path_queue;
                    for (int ix=0; ix < 2; ix++) {
                        changed = false;

                        for (auto n = current_partition.find_first(); n != dynamic_bitset<>::npos; n = current_partition.find_next(n)) {
                            if (!flexible.test(n)) {
                                if (ix > 0) {
                                    path.clear();
                                    dfs_found.reset();
                                    auto tpResult = traceTwoPath(n, 0);
                                    if (!tpResult.empty()) {
                                        //cout << seed << ": Recolored node (" << tpResult.count() << ")" << endl;
                                        changed = true;
                                    } else {
                                        //cout << seed << ": Failed to recolor node" << endl;
                                    }
                                    assert(g.verify(current_coloring));
                                }
                            } else { // Simple convert flexible...
                                //cout << seed << ": Converted flexible node " << n << endl;
                                for (color_t k = 0; k < my_num_colors; k++) {
                                    if (k != selected_color && k != current_coloring[n] && neighborhood_counts_real[n][k] == 0) {
                                        changeColor(n, selected_color, k);
                                        changed = true;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                };

//                if (! use_path_trace)
//                    runTwoPath();

//                for(node_t n=0; n < g.getNumNodes(); n++) {
//                    int sum1 = 0;
//                    int sum2 = 0;
//                    for (color_t k = 0; k < start.numColors; k++) {
//                        sum1 += neighborhood_counts_real[n][k];
//                        sum2 += neighborhood_counts[n][k];
//                    }
//                    assert(sum1 == (sum2 + (g.adjacency[n] & flexible).count()));
//                }
//
//                for (node_t n=0; n < g.getNumNodes(); n ++ ) {
//                    if (current_coloring[n] == selected_color)
//                        current_coloring[n] = INVALID_COLOR;
//                }
//                assert(g.verify(current_coloring, false));

                auto startCount = current_partition.count();
                bool swapped = false; // Used to limit the any calls on the partition
                //c_retention = startCount * 6 / 10;

                // Try to eliminate color
                while (iteration < iterations + pre_iterations && partitions[selected_color].any()) {
                    if (my_cycle < cycle) {
                        seed_sync.set(selected_color);
                        break;
                    }

                    swapped = false;
                    if (iteration % 100 == 0)
                        c_retention = iteration > pre_iterations ? retention : max(static_cast<int>(current_partition.count() * 6 / 10), 2);

                    // Remove tabus after retention
                    while (c_taboo_idx < tabuQueue.size() && get<0>(tabuQueue[c_taboo_idx]) < iteration) {
                        taboos[get<1>(tabuQueue[c_taboo_idx])][get<2>(tabuQueue[c_taboo_idx])] = false;
                        c_taboo_idx++;
                    }

                    int c_min = -1;
                    int c_min_node = -1;
                    int alternative_color = -1;

                    if (iteration % 1000 == 0 || iteration >= pre_iterations)
                        cout << seed << ": Color " << selected_color << ", Count " << current_partition.count() << endl;

                    // Find node with the smallest number of neighbors colored in an alternative color
                    for (auto n = current_partition.find_first();
                         n != boost::dynamic_bitset<>::npos && c_min != 0; n = current_partition.find_next(n)) {
                        for (auto k = 0; k < my_num_colors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts_real[n][k];

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
                        //usedColors.insert(selected_color);
                        c_min = 0;
//                        cout << seed << ": Early fail to eliminate color " << selected_color << endl;
//                        break;
                    }

                    while (iteration < pre_iterations && c_min == 1) {
                        // Switch colors
                        int next_n = static_cast<int>((g.adjacency[c_min_node] &
                                                       partitions[alternative_color]).find_first());

                        changeColor(c_min_node, selected_color, alternative_color);
                        changeColor(next_n, alternative_color, selected_color);

                        c_min = -1;
                        c_min_node = next_n;
                        alternative_color = -1;

                        for (auto k = 0; k < my_num_colors; k++) {
                            // Already eliminated that color, or taboo
                            if (k == selected_color || partitions[k].empty())
                                continue;

                            auto count = neighborhood_counts_real[next_n][k];
                            // Non found, just change color
                            if (count == 0) {
                                changeColor(next_n, selected_color, k);
                                c_min = 0;
                                break;
                            }

                            if (taboos[next_n].test(k))
                                continue;

                            if (c_min == -1
                            || (count < c_min)
                            || (count == c_min && neighborhood_counts[next_n][k] < neighborhood_counts[next_n][alternative_color])
                            ) {
                                c_min = static_cast<int>(count);
                                alternative_color = k;
                            }
                        }
                    }

                    if (iteration >= pre_iterations && c_min > 0 && c_min  <= tp_branch_limit) {
                        path.clear();
                        dfs_found.reset();
                        auto tpResult = traceTwoPath(c_min_node, 0);
                        if (!tpResult.empty()) {
                            c_min = 0;
                        }
                    }

                    bool solved = false;

                    if (iteration >= pre_iterations && c_min >= 1) {
                        swapped = true;
                        dynamic_bitset<> component(g.getNumNodes());
                        node_t cnt = 0;
                        component.set(c_min_node);

                        vector<dynamic_bitset<>> allowed_colors;
                        if (use_allowed) {
                            auto cbs = dynamic_bitset<>(g.getNumNodes());
                            cbs.set(c_min_node);
                            allowed_colors.resize(my_num_colors, cbs);
                            allowed_colors[selected_color].flip();
                        }

                        if (c_min < first_limit_nodes || later_limit_color > 1) {
                            vector<dynamic_bitset<>> nb_comp;
                            nb_comp.reserve(my_num_colors);

                            vector<tuple<node_t, node_t, int, color_t>> nbs;
                            nbs.reserve(my_num_colors);
                            for (auto k = 0; k < my_num_colors; k++) {
                                if (k != selected_color && !taboos[c_min_node].test(k)) {
                                    if (useFlexibleSelection)
                                        nbs.emplace_back(neighborhood_counts[c_min_node][k], neighborhood_counts_real[c_min_node][k], rand(), k);
                                    else
                                        nbs.emplace_back(neighborhood_counts_real[c_min_node][k], neighborhood_counts[c_min_node][k], rand(), k);
                                }
                            }
                            sort(nbs.begin(), nbs.end());

                            //cout << seed << ": Minimum element: " << get<0>(nbs[0]) << "/" << neighborhood_counts_real[c_min_node][get<3>(nbs[0])] << endl;

                            //for (int i = 0; i < first_limit_color && i < nbs.size(); i++) {
                            for (int i = 0; i < nbs.size(); i++) {
                                if (i == 0 || neighborhood_counts_real[c_min_node][get<3>(nbs[i])] + cnt < first_limit_nodes) {
                                    auto ncp = g.adjacency[c_min_node] & partitions[get<3>(nbs[i])];
                                    if (!(ncp & last_nodes_used).any()) {
                                        nb_comp.push_back(ncp);
                                        component |= ncp;
                                        last_nodes |= ncp;
                                        cnt += neighborhood_counts_real[c_min_node][get<3>(nbs[i])];
                                    }
                                } else if (! useFlexibleSelection){
                                    //cout << seed << ": Added " << i << " Elements, Max: " << get<0>(nbs[i]) << "/" << neighborhood_counts_real[c_min_node][get<3>(nbs[i])] << endl;
                                    break;
                                }
                            }

                            if (cnt > 1 || (cnt == 1 && later_limit_color > 1)) {
                                vector<tuple<node_t, node_t, int, color_t>> current_nbs;
                                current_nbs.reserve(later_limit_color + 1);

                                for(auto i=0; i < nb_comp.size(); i++) {
                                    vector<dynamic_bitset<>> sub_nb(later_limit_color, dynamic_bitset<>(g.getNumNodes()));

                                    bool is_empty = false;

                                    for (auto n=nb_comp[i].find_first(); n != dynamic_bitset<>::npos; n=nb_comp[i].find_next(n)) {
                                        current_nbs.clear();
                                        for (auto k = 0; k < my_num_colors; k++) {
                                            if (k != selected_color && k != current_coloring[n] && !taboos[n].test(k)) {
                                                if (neighborhood_counts_real[n][k] == 0) {
                                                    is_empty = true;
                                                    break;
                                                }

                                                if ((current_nbs.size() < later_limit_color || get<0>(current_nbs.back()) > neighborhood_counts_real[n][k]) &&
                                                        !((g.adjacency[n] & partitions[k]) & component).any()
                                                ) {
                                                    if (useFlexibleSelection)
                                                        current_nbs.emplace_back(neighborhood_counts[n][k],neighborhood_counts_real[n][k], k == alternative_color ? 0 : rand(), k);
                                                    else
                                                        current_nbs.emplace_back(neighborhood_counts_real[n][k], neighborhood_counts[n][k], k == alternative_color ? 0 : rand(), k);

                                                    if (current_nbs.size() > later_limit_color) {
                                                        sort(current_nbs.begin(), current_nbs.end());
                                                        current_nbs.pop_back();
                                                    }
                                                }
                                            }
                                        }
                                        if (! is_empty) {
                                            sort(current_nbs.begin(), current_nbs.end());
                                            for (int j = 0; j < later_limit_color && j < current_nbs.size(); j++) {
                                                auto nc = (g.adjacency[n] & partitions[get<3>(current_nbs[j])]);
                                                if (use_allowed)
                                                    allowed_colors[get<3>(current_nbs[j])].set(n);
                                                sub_nb[j] |= nc;
                                            }
                                        }
                                    }

                                    for (int j = 0; j < later_limit_color && j < sub_nb.size(); j++) {
                                        auto scnt = (sub_nb[j] - component).count();
                                        if ((sub_nb[j] & last_nodes_used).any())
                                            continue;

                                        if (scnt > 0 && scnt + cnt < later_limit_nodes) {
                                            nb_comp.push_back(sub_nb[j]);
                                            last_nodes |= sub_nb[j];
                                            component |= sub_nb[j];
                                            cnt += scnt;

                                            if (j==0) {
                                                for (auto n=nb_comp[i].find_first(); n != dynamic_bitset<>::npos; n=nb_comp[i].find_next(n)) {
                                                    last_nodes.reset(n);
                                                }
                                            }
                                        } else {
                                            break;
                                        }
                                    }
                                }
                            }
                            if (cnt > 0) {
                                auto sg = SubGraph(g, component, current_coloring, nullptr, INVALID_NODE, taboos[0].size() - 1);

                                // Make sure current node gets a different color and that all nodes can take this color.
                                bool found_c_node = false;
                                node_t mapped_min_node = sg.r_node_map[c_min_node];
                                dynamic_bitset<> found(sg.sub_g.getNumNodes());
                                for(auto& cEx : sg.exceptions) {
                                    found.set(cEx.node);
                                    if (cEx.node == mapped_min_node) {
                                        found_c_node = true;
                                        cEx.colors.set(selected_color);
                                    } else {
                                        auto orig_n = sg.node_map[cEx.node];

                                        if (use_allowed) {
                                            if (!flexible.test(orig_n) && last_nodes.test(orig_n))
                                                cEx.colors.reset(selected_color);
                                            else
                                                cEx.colors.set(selected_color);
                                        } else
                                            cEx.colors.reset(selected_color);

                                        if (use_allowed) {
                                            for (color_t k = 0; k < my_num_colors; k++) {
                                                if (k != current_coloring[orig_n] && k != selected_color &&
                                                    neighborhood_counts_real[orig_n][k] > 0 &&
                                                    !allowed_colors[k].test(orig_n))
                                                    cEx.colors.set(k);
                                            }
                                        } else if (useTaboos) {
                                            auto revn = sg.node_map[cEx.node];
                                            taboos[revn].reset(current_coloring[revn]);
                                            cEx.colors |= taboos[revn];
                                        }
                                    }
                                }

                                if (! found_c_node) {
                                    sg.exceptions.emplace_back(mapped_min_node, dynamic_bitset<>(g.getNumNodes()));
                                    sg.exceptions.back().colors.set(selected_color);
                                }

                                if (useTaboos || use_allowed) {
                                    found.set(mapped_min_node);
                                    found.flip();
                                    for (auto c_sn = found.find_first();
                                         c_sn != dynamic_bitset<>::npos; c_sn = found.find_next(c_sn)) {
                                        sg.exceptions.emplace_back(c_sn, dynamic_bitset<>(g.getNumNodes()));
                                        auto &cEx = sg.exceptions.back();
                                        auto orig_n = sg.node_map[cEx.node];
                                        if (use_allowed) {
                                            if (!flexible.test(orig_n) && last_nodes.test(orig_n))
                                                cEx.colors.reset(selected_color);
                                            else
                                                cEx.colors.set(selected_color);
                                        } else
                                            cEx.colors.reset(selected_color);

                                        if (use_allowed) {
                                            for (color_t k = 0; k < my_num_colors; k++) {
                                                if (k != current_coloring[orig_n] && k != selected_color &&
                                                    neighborhood_counts_real[orig_n][k] > 0 &&
                                                    !allowed_colors[k].test(orig_n))
                                                    cEx.colors.set(k);
                                            }
                                        } else if (useTaboos) {
                                            auto revn = sg.node_map[cEx.node];
                                            taboos[revn].reset(current_coloring[revn]);
                                            cEx.colors |= taboos[revn];
                                        }
                                    }
                                }

                                // Find a new coloring
                                //auto new_color = SatEncode::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min);
                                //cout << seed << ": " << c_min << endl;
//                                dynamic_bitset<> suggested = dynamic_bitset<>(sg.sub_g.getNumNodes());
//                                auto nnb = g.adjacency[c_min_node] & partitions[alternative_color];
//                                for(auto cn=nnb.find_first(); cn != dynamic_bitset<>::npos; cn = nnb.find_next(cn))
//                                    suggested.set(sg.r_node_map[cn]);

                                auto new_color = use_cadical ? SatEncodeCadical::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min) :
                                        SatEncode::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min,
                                        true);
//                                auto new_color = c_min > 1 ?
//                                    SatEncodeCadical::encode_partial(sg, my_num_colors, timeout, true, false, selected_color, c_min)
//                                    : SatEncodeCadical::encode_partial(sg, my_num_colors-1, timeout, true, false, INVALID_COLOR, 0, false);
                                node_t new_selected_count = 0;
                                if (! new_color.first.coloring.empty()) {
                                    //cout << seed << ": Solved" << endl;
                                    solved = true;
                                    for(auto i=0; i < new_color.first.coloring.size(); i++) {
                                        auto oldColor = current_coloring[sg.node_map[i]];
                                        if(mapped_min_node == i) {
                                            assert(oldColor != new_color.first.coloring[i]);
                                        }

                                        if (oldColor != new_color.first.coloring[i]) {
                                            changeColor(sg.node_map[i], oldColor, new_color.first.coloring[i]);
                                            if (new_color.first.coloring[i] == selected_color)
                                                new_selected_count++;
                                        }
                                    }
                                    successes += 1;
                                    max_success_cnt = max_success_cnt < sg.sub_g.adjacency.size() ? sg.sub_g.adjacency.size() : max_success_cnt;
                                    if (!new_color.first.coloring.empty() || new_color.second) {
                                        failures = 0;
                                        if (successes > 5) {
                                            if (max_success_cnt > later_limit_nodes - later_increment  && later_limit_nodes < 3000) {
                                                first_limit_nodes += first_increment;
                                                later_limit_nodes += later_increment;
                                                cout << seed << ": Switched to " << first_limit_nodes << " " << later_limit_nodes
                                                     << endl;
                                            }
                                            successes = 0;
                                        }
                                    }
                                }
                                if (new_color.first.coloring.empty() && !new_color.second) {
                                    // cout << seed << ": Timeout" << endl;
                                    successes = 0;
                                    if (failures > 1) {
                                        if (later_limit_nodes > 100) {
                                            first_limit_nodes -= first_increment;
                                            later_limit_nodes -= later_increment;
                                            cout << seed << ": Switched to " << first_limit_nodes << " " << later_limit_nodes
                                                 << endl;
                                        }
                                        failures = 0;
                                    } else {
                                        failures++;
                                    }
                                } else if (new_color.first.coloring.empty() && new_color.second) {
                                    // cout << seed << ": UNSAT" << endl;
                                }
                            }
                        }

                        if (last_nodes_used_queue.size() == last_nodes_used_queue.max_size()) {
                            last_nodes_used.reset(last_nodes_used_queue.back());
                            last_nodes_used_queue.pop_back();
                        }
                        last_nodes_used.set(c_min_node);
                        last_nodes_used_queue.push_front(c_min_node);
                    }
                    if (! solved && c_min > 0) {
                        if (useFlexibleSelection) {
                            for (color_t k = 0; k < my_num_colors; k++) {
                                if (k == selected_color || taboos[c_min_node].test(k))
                                    continue;

                                if (neighborhood_counts[c_min_node][k] < c_min ||
                                    (neighborhood_counts[c_min_node][k] == c_min && neighborhood_counts_real[c_min_node][k] < neighborhood_counts_real[c_min_node][alternative_color])) {
                                    c_min = neighborhood_counts[c_min_node][k];
                                    alternative_color = k;
                                }
                            }
                        }

                        changeColor(c_min_node, selected_color, alternative_color);

                        auto colored_neighbors = partitions[alternative_color] & g.adjacency[c_min_node];

                        for (auto n = colored_neighbors.find_first();
                             n != boost::dynamic_bitset<>::npos; n = colored_neighbors.find_next(n)) {
                            changeColor(n, alternative_color, selected_color);
                        }
                    }

                    iteration++;
                    if (iteration == pre_iterations && pre_iterations > 0) {
                        auto newCount = current_partition.count();
                        if (newCount < startCount) {
                            startCount = newCount;
                            iteration -= 100 * resetIterations;
                        }
                    } else if (iteration >= iterations + pre_iterations) {
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
                        iteration = 0;

                        auto c_max_color = partitions.size() - 1;
                        if (selected_color != c_max_color) {
                            partitions[selected_color] = partitions[c_max_color];

                            for (int n = 0; n < g.getNumNodes(); n++) {
                                if (current_coloring[n] == c_max_color) {
                                    current_coloring[n] = selected_color;
                                }
                                neighborhood_counts_real[n][selected_color] = neighborhood_counts_real[n][c_max_color];
                                taboos[n].reset(selected_color);
                            }
                        }
                        assert(g.verify(current_coloring));

                        partitions.pop_back();
                        start.coloring = current_coloring;
                        start.numColors -= 1;
                        my_num_colors = start.numColors;
                        // TODO: Adapt ordering? For the return would be sufficient...
                        if (!export_path.empty() && start.numColors < ub) {
                            start.store(export_path, g);
                        }
                        std::chrono::steady_clock::time_point end = std::chrono::steady_clock::now();
                        cout << seed << "::"<< std::chrono::duration_cast<std::chrono::seconds>(end - begin).count() << "::Eliminated " << selected_color << ", Remaining " << partitions.size() << endl;
                        eliminatedColors++;
                    }
                    seed_sync.set(selected_color);
                    sync.unlock();
                } else if (iteration >= iterations + pre_iterations) {
                    cout << seed << ": Failed to eliminate color " << selected_color << endl;
                }
            }
        }
        cout << "Eliminated " << eliminatedColors << " Colors from originally " << originalColors << endl;
        return eliminatedColors > 0;
    }

    bool componentSearch(ConflictGraph& g, Coloring& start, color_t lb, const vector<node_t>& clique) {
        auto find_components = [&] {
            dynamic_bitset<> connected_found(g.getNumNodes());
            connected_found.flip();
            connected_found -= g.reduced;
            for (auto cn: clique)
                connected_found.reset(cn);

            dynamic_bitset<> queue(g.getNumNodes());
            vector<pair<node_t, dynamic_bitset<>>> components;

            while (connected_found.any()) {
                dynamic_bitset<> component(g.getNumNodes());
                auto n = connected_found.find_first();
                queue.set(n);
                component.set(n);

                while (true) {
                    auto cn = queue.find_first();
                    if (cn == dynamic_bitset<>::npos)
                        break;
                    queue.reset(cn);

                    for (auto cnb = g.adjacency[cn].find_first();
                         cnb != dynamic_bitset<>::npos; cnb = g.adjacency[cn].find_next(cnb)) {
                        if (connected_found.test(cnb)) {
                            assert(!g.reduced.test(cnb));
                            queue.set(cnb);
                            component.set(cnb);
                            connected_found.reset(cnb);
                        }
                    }
                }
                components.emplace_back(component.count(), component);
            }

            sort(components.begin(), components.end());
            return components;
        };

        g.reduce(start.numColors-1);

        // Check connectedness
        bool success = true;

        while (success) {
            success = false;

            auto c_components = find_components();
            if (c_components.size() > 1) {
                for(node_t ci=0; ci < clique.size(); ci++) {
                    auto old_color = start.coloring[clique[ci]];
                    for(node_t cn=0; cn < g.getNumNodes(); cn++) {
                        if (start.coloring[cn] == ci)
                            start.coloring[cn] = old_color;
                        else if (start.coloring[cn] == old_color)
                            start.coloring[cn] = ci;
                    }
                }

                assert(g.verify(start.coloring));

                for(auto& c_component: c_components) {
                    cout << c_component.first << endl;
//                    if (c_component.first < 6000) {
//                        for (auto cn: clique) {
//                            c_component.second.set(cn);
//                        }
//                        auto sg = SubGraph(g, c_component.second, start.coloring);
//                        vector<node_t> mappedClique(clique.size());
//                        for (auto i = 0; i < clique.size(); i++)
//                            mappedClique[i] = sg.r_node_map[clique[i]];
//                        SatEncodeCadical::encode_full(sg.sub_g, mappedClique, start.numColors - 1);
//                    }
                }
                exit(0);
            } else {
                cout << "Only one component found" << endl;
                exit(1);
                return false;
            }
        }

        // Reset
        g.reduce(lb);
        return true;
    }
}

#endif //PLANARITY_SAT_SEARCH_H
