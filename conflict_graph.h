//
// Created on 12.10.21.
//

#ifndef CPP_CONFLICT_GRAPH_H
#define CPP_CONFLICT_GRAPH_H

#include <utility>
#include <vector>
#include <boost/dynamic_bitset.hpp>
#include "planarity.h"
#include <unordered_set>
#include <stack>
#include <iostream>
#include <unordered_map>
#include <fstream>
#include <bzlib.h>
#include <cstring>
#include <sstream>

using namespace std;
using namespace boost;

namespace planarity {
    /**
         * Encodes a color a node is not allowed to get.
         */
    struct ColoringException {
        ColoringException(node_t node, dynamic_bitset<> colors) : node(node), colors(std::move(colors)) {}
        node_t node;
        dynamic_bitset<> colors;
    };

    // Forward declaration
    class Coloring;

    class ConflictGraph {
    public:
        /**
         * The adjacency matrix, accessible as direct iteration is much faster.
         */
        std::vector<dynamic_bitset<>> adjacency;
        dynamic_bitset<> reduced;
        color_t reduced_lb = 0;
        unsigned long numEdges = 0;

        /**
         * Creates a graph with the given number of nodes. Further nodes can be added using @see addNode.
         */
        explicit ConflictGraph(node_t nodes) : reduced(nodes) {
            adjacency = vector<dynamic_bitset<>>(nodes, dynamic_bitset<>(nodes));
        }

        /**
         * Adds a node to the graph and extends it, if the node exceeds the known number of nodes.
         * @param n The node to add.
         * @param reserve Reserves space for this many further nodes, in case n exceeds the number of nodes.
         */
        void addNode(node_t n, node_t reserve=0) {
            if (adjacency.size() <= n) {
               for(auto& cline : adjacency) {
                   if (cline.size() <= n) {
                       cline.resize(n+1);
                   }
               }
               while(adjacency.size() <= n) {
                   adjacency.emplace_back(n, false);
                   if (reserve > 0)
                       adjacency.back().reserve(reserve);
               }
            }
        }

        /**
         * Adds an edge between to nodes. Note that both nodes are assumed to be valid nodes!
         * If unsure use @see addNode before.
         */
        void addEdge(const node_t n1, const node_t n2) {
            if (! adjacency[n1].test(n2)) {
                adjacency[n1][n2] = true;
                adjacency[n2][n1] = true;
            }
            numEdges++;
        }

        /**
         * Returns the number of nodes in the graph.
         */
        [[nodiscard]] int getNumNodes() const {
            return adjacency.size();
        }

        /**
         * Returns the neighbors of the node. This is a convenience method that is rather slow. If performance
         * is important, directly iterate over adjacency[n].
         */
        [[nodiscard]] vector<int> getNeighbors(const node_t n) const {
            vector<int> neighbors;
            for(auto pos=adjacency[n].find_first(); pos != adjacency[n].npos; pos = adjacency[n].find_next(pos)) {
                neighbors.push_back(pos);
            }

            return neighbors;
        }

        /**
         * Returns the neighbors of the node, disregarding exception nodes. This is a convenience method that is rather slow. If performance
         * is important, directly iterate over adjacency[n].
         */
        [[nodiscard]] vector<int> getNeighborsExcept(const node_t n, const dynamic_bitset<>& exceptions) const {
            vector<int> neighbors;
            auto modified = adjacency[n] - exceptions;

            for(auto pos=modified.find_first(); pos != boost::dynamic_bitset<unsigned long, std::allocator<unsigned long> >::npos; pos = modified.find_next(pos)) {
                neighbors.push_back(pos);
            }

            return neighbors;
        }

        /**
         * Returns the degree of the vertex.
         */
        [[nodiscard]] int getDegree(const node_t n) const{
            return adjacency[n].count();
        }

        /**
         * Verifies that a coloring is a valid coloring for the graph.
         * @param coloring The coloring to verify.
         * @param verify_unset If true, conflicts occurring with unset (INVALID_COLOR) colors will cause an error.
         * @return True if no coloring conflicts were detected.
         */
        [[nodiscard]] bool verify(const vector<color_t>& coloring, const bool verify_unset=true) const {
            for(auto n=0; n < adjacency.size(); n++) {
                for (auto n2 = adjacency[n].find_next(n); n2 != adjacency[n].npos; n2 = adjacency[n].find_next(n2)) {
                    if (coloring[n] == coloring[n2]) {
                        if (verify_unset || coloring[n] != INVALID_COLOR) {
                            return false;
                        }
                    }
                }
            }

            return true;
        }

        /**
         * Calculates the number of nodes that could be removed given a specified lower bound.
         */
        void reduce(const node_t lb) {
            reduced.reset();
            reduced_lb = lb;
            vector<dynamic_bitset<>> cp = adjacency;
            bool changed = true;
            while (changed) {
                changed = false;
                for (node_t n=0; n < getNumNodes(); n++) {
                    if (! cp[n].empty() && cp[n].count() < lb) {
                        changed = true;
                        reduced.set(n);

                        for (auto n2 = cp[n].find_next(n); n2 != cp[n].npos; n2 = cp[n].find_next(n2)) {
                            cp[n2][n] = false;
                        }
                        cp[n].clear();
                    }
                }
            }
        }

        void store(const string& path) {
            FILE *bz2File = fopen(path.c_str(), "wb");
            int bzError;
            const int BLOCK_MULTIPLIER = 7;
            BZFILE *myBZ = BZ2_bzWriteOpen(&bzError, bz2File, BLOCK_MULTIPLIER, 0, 0);
            char buffer [25];
            int len;

            unsigned long edgeCount = 0;
            //BZ2_bzWrite(&bzError, myBZ, buf, bytesRead);
            string header = "                                                      \n";

            len = sprintf(buffer, "p edge %u %lu\n", getNumNodes(), numEdges);
            BZ2_bzWrite(&bzError, myBZ, buffer, len);

            for(node_t n=getNumNodes()-1; n >= 0 && n != INVALID_NODE; n--) {
                for (auto n2 = adjacency[n].find_next(n);
                     n2 != dynamic_bitset<>::npos; n2 = adjacency[n].find_next(n2)) {
                    len = sprintf (buffer, "e %u %u\n", n + 1, static_cast<node_t>(n2) + 1);
                    BZ2_bzWrite(&bzError, myBZ, buffer, len);
                    edgeCount++;
                }
            }
            BZ2_bzWriteClose(&bzError, myBZ, 0, NULL, NULL);
        }

        static ConflictGraph parse(const string& filename) {
            fstream fl;
            unique_ptr<ConflictGraph> g = nullptr;

            FILE *bz2File = fopen(filename.c_str(), "rb");
            int bzError;
            BZFILE *myBZ = BZ2_bzReadOpen(&bzError, bz2File, 0, 0, NULL, 0);
            char buffer [4096];

            string tok = "";
            node_t nodes[2];
            bool header_read = false;
            bool is_header = false;
            bool is_edge = false;

            while (bzError == BZ_OK) {
                memset (buffer,'\0',strlen(buffer));
                if (!tok.empty())
                    strcpy(buffer, tok.c_str());
                int charsRead = BZ2_bzRead( &bzError, myBZ, buffer + tok.size(), sizeof(buffer) - tok.size() -1);

                if (charsRead > 0) {
                    istringstream iss(buffer);
                    for (long i = 0; getline(iss, tok); i++) {
                        if (!iss.eof() || bzError == BZ_STREAM_END) {
                            is_edge = true;
                            istringstream iss2(tok);
                            string tok2;
                            long j = 0;

                            for (; getline(iss2, tok2, ' '); j++) {
                                if (j == 0 && !header_read && tok2 == "p") {
                                    is_header = true;
                                    header_read = true;
                                    is_edge = false;
                                }
                                if (j == 0 && !is_header && tok2 != "e") {
                                    is_edge = false;
                                    break;
                                }

                                if (is_edge && j > 2) {
                                    cout << "ERROR: encountered an edge with more than 2 edges" << endl;
                                    exit(1);
                                }

                                if ((is_edge && j > 0) || (is_header && j > 1))
                                    nodes[j - (is_header ? 2 : 1)] = stoull(tok2);
                            }
                            if (is_edge && j != 3) {
                                cout << "ERROR: found incomplete edge" << endl;
                                exit(1);
                            }
                            if (is_header && j != 4){
                                cout << "ERROR: invalid header" << endl;
                                exit(1);
                            }
                            if (g == nullptr && is_header) {
                                g = std::make_unique<ConflictGraph>(nodes[0]);
                                is_header = false;
                            }
                            if (is_edge)
                                g->addEdge(nodes[0] - 1, nodes[1] - 1);
                        } else {
                            tok.erase(tok.begin(), std::find_if(tok.begin(), tok.end(),
                                  std::not1(std::ptr_fun<int, int>(std::isspace))));
                        }
                    }
                }
            }


            // Close the file
            BZ2_bzReadClose( &bzError, myBZ);
            fclose(bz2File);

            return *g;
        }
        };

    /**
     * Encodes a subgraph of a graph.
     */
    class SubGraph {
    private:
        node_t _edges;
        /**
         * Common part between the constructors.
         */
        inline void init(const ConflictGraph& g, const dynamic_bitset<>& nodes, const vector<color_t>& coloring, const unordered_map<node_t, node_t>* ordering=nullptr, node_t orderLimit=0, color_t max_color=INVALID_COLOR) {
            int edges = 0;
            if (max_color == INVALID_COLOR) {
                max_color = 0;
                for (auto cc : coloring)
                    max_color = max(max_color, cc);
            }

            for(auto n=nodes.find_first(); n != dynamic_bitset<>::npos; n = nodes.find_next(n)) {
                auto included = nodes & g.adjacency[n];
                auto excluded = g.adjacency[n] - nodes;

                for(auto n2=included.find_first(); n2 != dynamic_bitset<>::npos && n2 < n; n2 = included.find_next(n2)) {
                    sub_g.addEdge(r_node_map[n], r_node_map[n2]);
                    edges++;
                }
                bool found_any = false;
                dynamic_bitset<> colors(max_color + 1);
                for(auto n2=excluded.find_first(); n2 != dynamic_bitset<>::npos; n2 = excluded.find_next(n2)) {
                    if (coloring[n2] != INVALID_COLOR) {
                        if (ordering == nullptr || ordering->at(n2) < orderLimit) {
                            colors.set(coloring[n2]);
                            found_any = true;
                        }
                    }
                }

                if (found_any)
                    exceptions.emplace_back(r_node_map[n], colors);
            }
            cout << edges << " Edges, " << sub_g.adjacency.size() << " Nodes" << endl;
            _edges = edges;
        }
    public:
        node_t getEdges() {
            return _edges;
        }
        /**
         * The subgraph.
         */
        ConflictGraph sub_g;
        /**
         * Colors that are not eligible for certain nodes.
         */
        vector<ColoringException> exceptions;
        /**
         * Mapping from the original graph's node index to the sub-graph's node index.
         */
        unordered_map<node_t, node_t> r_node_map;
        /**
         * A mapping from the sub-graph's node index to the original graph's node index.
         */
        vector<node_t> node_map;

        SubGraph(const ConflictGraph& g, vector<node_t>& nodes, const vector<color_t>& coloring, const unordered_map<node_t, node_t>* nodePosition=nullptr, node_t orderLimit=INVALID_NODE) :
                sub_g(ConflictGraph(nodes.size())), node_map(nodes.size()) {
            dynamic_bitset<> ns(g.getNumNodes());
            r_node_map.reserve(nodes.size());

            sort(nodes.begin(), nodes.end());
            for(auto i=0; i < nodes.size(); i++) {
                ns.set(nodes[i]);
                node_map[i] = nodes[i];
                r_node_map[nodes[i]] = i;
            }
            init(g, ns, coloring, nodePosition, orderLimit);
        }

        SubGraph(const ConflictGraph& g, const dynamic_bitset<>& nodes, const vector<color_t>& coloring, const unordered_map<node_t, node_t>* nodePosition=nullptr, node_t orderLimit=INVALID_NODE, color_t max_color=INVALID_COLOR) :
                sub_g(ConflictGraph(nodes.count())), node_map(nodes.size()){
            node_t numNodes = nodes.count();
            r_node_map.reserve(numNodes);

            node_t cnode = 0;
            for(auto n=nodes.find_first(); n < dynamic_bitset<>::npos; n = nodes.find_next(n)) {
                node_map[cnode] = n;
                r_node_map[n] = cnode;
                cnode++;
            }
            init(g, nodes, coloring, nodePosition, orderLimit, max_color);
        }

        /**
         * Maps a coloring for the sub-graph to a (partial) coloring of the main graph.
         */
        void map_coloring(const vector<color_t>& sub_coloring, vector<color_t>& main_coloring) const {
            for(auto n=0; n < sub_coloring.size(); n++) {
                main_coloring[node_map[n]] = sub_coloring[n];
            }
        }
    };

    void find_color_subgraph(const ConflictGraph& g, Coloring& coloring, const string& filename);
}

#endif //CPP_CONFLICT_GRAPH_H
