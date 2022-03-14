//
// Created on 01.02.22.
//
#include <string>
#include <vector>
#include "planarity.h"
#include <boost/dynamic_bitset.hpp>
#include <random>
#include <iostream>
#include <sstream>
#include "conflict_graph.h"
#include "heuristics.h"
#include "clique.h"

#ifndef PLANARITY_GRAPH_GENERATOR_H
#define PLANARITY_GRAPH_GENERATOR_H

using namespace std;
using namespace boost;

namespace planarity {
    void generate_random(node_t nodes, unsigned short probability, string& name, string& base_path) {
        while(true) {
            auto g = ConflictGraph(nodes);
            random_device rd;
            std::mt19937 mt(rd());
            std::uniform_int_distribution<short> dist(1, 100);

            for (node_t n = 0; n < nodes; n++) {
                for (node_t n2 = n + 1; n2 < nodes; n2++) {
                    if (dist(mt) <= probability) {
                        g.addEdge(n, n2);
                    }
                }
            }

            cout << "Generated graph with " << g.numEdges << " Edges, Storing..." << endl;

            auto sol = dsatur(g);
            cout << "Colors UB: " << sol.numColors << endl;
            g.reduce(sol.numColors);
            if (g.reduced.count() * 100 / nodes > 5) {
                cout << "Too reducible" << endl;
                continue;
            }

            dynamic_bitset<> found(nodes);
            dynamic_bitset<> q(nodes);
            q.set(0);
            found.set(0);
            found |= g.reduced;

            while(true) {
                auto cn = q.find_first();
                if (cn == dynamic_bitset<>::npos)
                    break;

                q.reset(cn);

                auto mnb = g.adjacency[cn] - found;
                for(auto cb=mnb.find_first(); cb != dynamic_bitset<>::npos; cb = mnb.find_next(cb)) {
                    q.set(cb);
                    found.set(cb);
                }
            }

            if(!found.all()) {
                cout << "Not connected" << endl;
                continue;
            }

            cout << "Checked" << endl;

            string path =
                    base_path + "graphs/" + name + "_" + std::to_string(nodes) + "_" + std::to_string(probability) +
                    ".edges.bz2";

            FILE *bz2File = fopen(path.c_str(), "wb");
            int bzError;
            const int BLOCK_MULTIPLIER = 7;
            BZFILE *myBZ = BZ2_bzWriteOpen(&bzError, bz2File, BLOCK_MULTIPLIER, 0, 0);
            char buffer[25];
            int len;

            len = sprintf(buffer, "p edge %u %lu\n", nodes, g.numEdges);
            BZ2_bzWrite(&bzError, myBZ, buffer, len);

            for (node_t n = 0; n < nodes; n++) {
                for (auto n2 = g.adjacency[n].find_next(n);
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    len = sprintf(buffer, "e %u %u\n", n + 1, static_cast<node_t>(n2) + 1);
                    BZ2_bzWrite(&bzError, myBZ, buffer, len);
                }
            }
            BZ2_bzWriteClose(&bzError, myBZ, 0, NULL, NULL);
            break;
        }
    }

    void generate_ba(node_t nodes, node_t degree, string& name, string& base_path) {
        while(true) {
            auto g = ConflictGraph(nodes);
            random_device rd;
            std::mt19937 mt(rd());
            rd();rd();rd();rd();rd();rd();rd();rd();
            vector<node_t> node_list;
            node_list.reserve(nodes * degree);
            node_t starting_nodes = 0;

            // Initialize graph
            for(node_t n=1; n < degree + 1; n++) {
                g.addEdge(0, n);
                node_list.push_back(0);
                node_list.push_back(n);
            }
            starting_nodes = degree + 1;

            // Create graph
            for(node_t n=starting_nodes; n < nodes; n++) {
                dynamic_bitset<> adjacency(n);
                node_t cnt = 0;
                std::uniform_int_distribution<size_t> dist(0, node_list.size()-1);

                while(cnt < degree) {
                    auto new_nb = node_list[dist(mt)];
                    if (! adjacency.test(new_nb)) {
                        cnt++;
                        adjacency.set(new_nb);
                        node_list.push_back(new_nb);
                        node_list.push_back(n);
                        g.addEdge(n, new_nb);
                    }
                }
            }

            cout << "Generated graph with " << g.numEdges << " Edges, Storing..." << endl;

            vector<node_t> cq;
            Clique::findCliqueGreedy2(g, cq, 0);
            cout << "Clique: " << cq.size() << endl;
            auto sol = dsatur(g);
            cout << "Colors UB: " << sol.numColors << endl;
            g.reduce(sol.numColors);
            if (g.reduced.count() * 100 / nodes > 5) {
                cout << "Too reducible" << endl;
                continue;
            }

            dynamic_bitset<> found(nodes);
            dynamic_bitset<> q(nodes);
            q.set(0);
            found.set(0);
            found |= g.reduced;

            while(true) {
                auto cn = q.find_first();
                if (cn == dynamic_bitset<>::npos)
                    break;

                q.reset(cn);

                auto mnb = g.adjacency[cn] - found;
                for(auto cb=mnb.find_first(); cb != dynamic_bitset<>::npos; cb = mnb.find_next(cb)) {
                    q.set(cb);
                    found.set(cb);
                }
            }

            if(!found.all()) {
                cout << "Not connected" << endl;
                continue;
            }

            cout << "Checked" << endl;

            string path =
                    base_path + "graphs/" + name + "_" + std::to_string(nodes) + "_" + std::to_string(degree) +
                    ".edges.bz2";

            FILE *bz2File = fopen(path.c_str(), "wb");
            int bzError;
            const int BLOCK_MULTIPLIER = 7;
            BZFILE *myBZ = BZ2_bzWriteOpen(&bzError, bz2File, BLOCK_MULTIPLIER, 0, 0);
            char buffer[25];
            int len;

            len = sprintf(buffer, "p edge %u %lu\n", nodes, g.numEdges);
            BZ2_bzWrite(&bzError, myBZ, buffer, len);

            for (node_t n = 0; n < nodes; n++) {
                for (auto n2 = g.adjacency[n].find_next(n);
                     n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    len = sprintf(buffer, "e %u %u\n", n + 1, static_cast<node_t>(n2) + 1);
                    BZ2_bzWrite(&bzError, myBZ, buffer, len);
                }
            }
            BZ2_bzWriteClose(&bzError, myBZ, 0, NULL, NULL);
            break;
        }
    }

};
#endif //PLANARITY_GRAPH_GENERATOR_H
