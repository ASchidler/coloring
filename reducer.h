//
// Createdhidler on 2/10/22.
//

#ifndef PLANARITY_REDUCER_H
#define PLANARITY_REDUCER_H

#include <boost/dynamic_bitset.hpp>
#include <fstream>
#include <bzlib.h>
#include <iostream>
#include "planarity.h"

using namespace std;

namespace planarity {
    static vector<vector<node_t>> parse_dimacs(const string& filename) {
        fstream fl;
        vector<vector<node_t>> graphs;

        FILE *bz2File = fopen(filename.c_str(), "rb");
        int bzError;
        BZFILE *myBZ = BZ2_bzReadOpen(&bzError, bz2File, 0, 0, NULL, 0);
        char buffer[4096000];

        string tok = "";
        uint64_t line_cnt = 0;
        size_t edges = 0;

        while (bzError == BZ_OK) {
            memset(buffer, '\0', strlen(buffer));
            if (!tok.empty())
                strcpy(buffer, tok.c_str());
            int charsRead = BZ2_bzRead(&bzError, myBZ, buffer + tok.size(), sizeof(buffer) - tok.size() - 1);

            if (charsRead > 0) {
                istringstream iss(buffer);
                for (long i = 0; getline(iss, tok); i++) {
                    if (!iss.eof() || bzError == BZ_STREAM_END) {
                        istringstream iss2(tok);
                        string tok2;
                        long j = 0;

                        for (; getline(iss2, tok2, ' '); j++) {
                            if (j == 0 && line_cnt == 0) {
                                graphs.resize(stoull(tok2));
                            } else if (line_cnt > 0) {
                                if (tok2 != "") {
                                    auto conv = stoull(tok2) - 1;
                                    if (line_cnt - 1 < conv) {
                                        graphs[line_cnt - 1].push_back(conv);
                                        graphs[conv].push_back(line_cnt - 1);
                                        edges++;
                                    }
                                }
                            }
                        }
                        line_cnt++;
                    } else {
                        tok.erase(tok.begin(), std::find_if(tok.begin(), tok.end(),
                                                            std::not1(std::ptr_fun<int, int>(std::isspace))));
                    }
                }
            }
        }

        // Close the file
        BZ2_bzReadClose(&bzError, myBZ);
        fclose(bz2File);

        cout << edges << " Edges" << endl;

        return graphs;
    }

    node_t find_clique(vector<vector<node_t>>& g) {
        vector<pair<dynamic_bitset<>, vector<node_t>>> cliques;
        size_t c_bound = 0;

        vector<pair<node_t, node_t>> degrees;
        degrees.reserve(g.size());
        for(node_t n=0; n < g.size(); n++) {
            degrees.emplace_back(g[n].size(), n);
        }

        sort(degrees.rbegin(), degrees.rend());

        for(auto& entry : degrees) {
            auto n = entry.second;
            bool clique_found = false;
            dynamic_bitset<> nb(g.size());
            for(auto n2:g[n])
                nb.set(n2);

            for (auto c_idx=0; c_idx < cliques.size(); c_idx++) {
                auto& cq = cliques[c_idx];
                if (cq.first.test(n)) {
                    clique_found = true;
                    cq.first &= nb;
                    cq.second.push_back(n);
                    if (! cq.first.any()) {
                        c_bound = max(c_bound, cq.first.count());
                        swap(cliques[c_idx], cliques.back());
                        cliques.pop_back();
                        c_idx--;
                    }
                }
            }

            if (! clique_found) {
                cliques.emplace_back(nb, 1);
                cliques.back().second.push_back(n);
            }
        }

        size_t max_size = 0;
        for(auto& cq: cliques)
            max_size = max(max_size, cq.second.size());

        return max_size;
    }

    vector<vector<node_t>> perform_reduction(vector<vector<node_t>>& g, node_t lb) {
        bool change = true;
        node_t removed = 0;

        while (change) {
            change = false;

            for(node_t n=0; n < g.size(); n++) {
                if (!g[n].empty() && g[n].size() < lb - 1) {
                    for(auto n2: g[n]) {
                        g[n2].erase(std::remove(g[n2].begin(), g[n2].end(), n), g[n2].end());
                        if (g[n2].empty())
                            removed++;
                    }

                    g[n].clear();
                    removed++;

                    change = true;
                }
            }
        }

        cout << "Removed: " << removed << endl;

        vector<vector<node_t>> result(g.size() - removed);
        vector<node_t> mapping(g.size());
        node_t cnt = 0;
        for(node_t n=0; n < g.size(); n++) {
            if (!g[n].empty()) {
                mapping[n] = cnt++;
            } else {
                mapping[n] = INVALID_NODE;
            }
        }

        for(node_t n=0; n < g.size(); n++) {
            if (mapping[n] != INVALID_NODE) {
                for(auto n2: g[n]) {
                    assert(find(g[n2].begin(), g[n2].end(), n) != g[n2].end());
                    assert(mapping[n2] != INVALID_NODE);
                    result[mapping[n]].push_back(mapping[n2]);
                }
            }
        }

        return result;
    }

    void store(vector<vector<node_t>>& g, string& output) {
        FILE *bz2File = fopen(output.c_str(), "wb");
        int bzError;
        const int BLOCK_MULTIPLIER = 7;
        BZFILE *myBZ = BZ2_bzWriteOpen(&bzError, bz2File, BLOCK_MULTIPLIER, 0, 0);
        char buffer [4096];
        int len;

        unsigned long edgeCount = 0;
        for(auto& v: g)
            edgeCount += v.size();
        edgeCount /= 2;

        //BZ2_bzWrite(&bzError, myBZ, buf, bytesRead);
        string header = "                                                      \n";

        len = sprintf(buffer, "p edge %lu %lu\n", g.size(), edgeCount);
        BZ2_bzWrite(&bzError, myBZ, buffer, len);

        for(node_t n=0; n < g.size(); n++) {
            for (auto n2 : g[n]) {
                if (n2 > n) {
                    len = sprintf(buffer, "e %u %u\n", n + 1, static_cast<node_t>(n2) + 1);
                    BZ2_bzWrite(&bzError, myBZ, buffer, len);
                }
            }
        }
        BZ2_bzWriteClose(&bzError, myBZ, 0, NULL, NULL);
    }

    void reduce(std::string& filename, string& output) {
        auto g = parse_dimacs(filename);
        //auto lb = find_clique(g);
        node_t lb = 55;
        cout << "Clique size: " << lb << endl;
        auto g2 = perform_reduction(g, lb);
        cout << "Graph size: " << g2.size() << endl;

        dynamic_bitset<> found(g2.size());
        vector<node_t> q;
        q.push_back(0);
        found.set(0);

        while(! q.empty()) {
            auto n=q.back();
            q.pop_back();

            for (auto n2: g2[n]) {
                if (! found.test(n2)) {
                    found.set(n2);
                    q.push_back(n2);
                }
            }
        }

        cout << "Connected " << found.count() << endl;

        store(g2, output);
    }
}
#endif //PLANARITY_REDUCER_H
