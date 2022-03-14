//
// Created on 12.10.21.
//

#ifndef CPP_SOLUTION_H
#define CPP_SOLUTION_H
#include <utility>
#include <vector>
#include <fstream>
#include "planarity.h"
#include <sstream>

using namespace std;

namespace planarity{
    class Coloring {
    public:
        vector<color_t> coloring;
        color_t numColors;
        vector<tuple<int, node_t>> ordering;

        Coloring(vector<color_t> coloring, color_t numColors, vector<tuple<int, node_t>> ordering) :
                coloring(std::move(coloring)), numColors(numColors), ordering(std::move(ordering)) {
        }

        void store(const string& filename, const ConflictGraph& g) const {
            if (g.verify(coloring)) {
                ofstream myfile(filename);
                if (myfile.is_open()) {
                    myfile << coloring[0];
                    for (int i = 1; i < coloring.size(); i++) {
                        myfile << "," << coloring[i];
                    }
                    myfile << endl;
                    myfile.close();
                }
            } else {
                cout << "Invalid coloring" << endl;
            }
        }

        static void store(const string& filename, const ConflictGraph& g, const vector<color_t>& coloring, bool ignore_unset=false) {
            if (g.verify(coloring, ignore_unset)) {
                ofstream myfile(filename);
                if (myfile.is_open()) {
                    myfile << coloring[0];
                    for (int i = 1; i < coloring.size(); i++) {
                        myfile << "," << coloring[i];
                    }
                    myfile << endl;
                    myfile.close();
                }
            } else {
                cout << "Invalid coloring" << endl;
            }
        }

        static Coloring parse(const string& filename, int numNodes) {
            fstream fl;

            fl.open(filename, ios::in);
            vector<color_t> coloring;
            color_t maxColor = 0;
            coloring.reserve(numNodes);
            vector<tuple<int, node_t>> ordering;
            ordering.reserve(numNodes);

            if (fl.is_open()) {
                string ln;
                while (getline(fl, ln)) {
                    if (ln.length() > 0) {
                        // Trim
                        ln.erase(ln.begin(), std::find_if(ln.begin(), ln.end(),
                                                          std::not1(std::ptr_fun<int, int>(std::isspace))));
                        istringstream iss(ln);
                        string tok;

                        for (long i = 0; getline(iss, tok, ','); i++) {
                            color_t cc = stoul(tok);
                            coloring.push_back(cc);
                            ordering.emplace_back(cc, i);

                            if (cc != INVALID_COLOR)
                                maxColor = max(maxColor, cc);
                        }
                    }
                }
            }

            sort(ordering.begin(), ordering.end());

            return {coloring, ++maxColor, ordering};
        }

        /**
         * Modify coloring, so that each node gets the smallest available color
         */
        void canonize(ConflictGraph& g) {
            vector<dynamic_bitset<>> partitions(numColors, dynamic_bitset<>(g.getNumNodes()));
            for (auto n=0; n < g.getNumNodes(); n++) {
                partitions[coloring[n]].set(n);
            }

            for(auto cc=1; cc < numColors; cc++) {
                for(auto n=partitions[cc].find_first(); n != dynamic_bitset<>::npos; n = partitions[cc].find_next(n)) {
                    for(auto cc2=0; cc2 < cc; cc2++) {
                        if (! (partitions[cc2] & g.adjacency[n]).any()) {
                            coloring[n] = cc2;
                            partitions[cc][n] = false;
                            partitions[cc2][n] = true;
                            break;
                        }
                    }
                }
            }

            assert(g.verify(coloring));
        }
    };
}
#endif //CPP_SOLUTION_H
