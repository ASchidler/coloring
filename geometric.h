//
// Created on 12.10.21.
//

#ifndef CPP_GEOMETRIC_H
#define CPP_GEOMETRIC_H

#pragma once
#include <queue>
#include <vector>
#include <map>
#include <unordered_map>
#include <optional>
#include <limits>
#include <exception>
#include <stdexcept>
#include <tuple>
#include <utility>
#include <algorithm>
#include <cassert>
#include <memory>
#include <random>
#include <string>
#include <iostream>
#include <boost/algorithm/string.hpp>
#include <fstream>
#include <sstream>
#include "conflict_graph.h"
#include "boi.h"

using namespace std;

namespace planarity {
    class GeometricInstance {
    public:
        vector<Line> edges;
    };

    GeometricInstance parse(string &filename) {
        fstream fl;

        fl.open(filename, ios::in);
        auto instance = GeometricInstance();

        long lineResult[4];

        if (fl.is_open()) {
            string ln;
            while (getline(fl, ln)) {
                if (ln.length() > 0) {
                    // Trim
                    ln.erase(ln.begin(), std::find_if(ln.begin(), ln.end(),
                                                      std::not1(std::ptr_fun<int, int>(std::isspace))));
                    istringstream iss(ln);
                    string tok;

                    for (long i = 0; getline(iss, tok, ' '); i++) {
                        tok.erase(tok.begin(), std::find_if(tok.begin(), tok.end(),
                                                            std::not1(std::ptr_fun<int, int>(std::isspace))));

                        lineResult[i] = stol(tok);
                    }
                    instance.edges.emplace_back(lineResult[0], lineResult[1], lineResult[2], lineResult[3]);
                }
            }
        }

        return instance;
    }

    ConflictGraph createConflictGraph(GeometricInstance &instance) {
        auto g = ConflictGraph(instance.edges.size());

//        auto alg = BentleyOttmannAnyIntersection(instance.edges);
//        auto result = alg.find_intersection();
//        while(result.has_value()) {
//            g.addEdge(result.value().segment_index[0], result.value().segment_index[1]);
//            result = alg.find_intersection();
//            //result.value().segment_index
//        }

        for (size_t i = 0; i < instance.edges.size(); i++) {
            auto &e1 = instance.edges[i];
            for (size_t j = i + 1; j < instance.edges.size(); j++) {
                auto &e2 = instance.edges[j];

                if (e1.intersects(e2)) {
                    g.addEdge(i, j);
                }
            }
        }

        return g;
    }
}
#endif //CPP_GEOMETRIC_H
