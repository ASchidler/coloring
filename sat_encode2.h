//
// Createdhidler on 10/15/21.
//

#ifndef CPP_SAT_ENCODE2_H
#define CPP_SAT_ENCODE2_H

#include "conflict_graph.h"
#include "cadical/cadical.hpp"
#include "cadical/signal.hpp"
#include <boost/thread/thread.hpp>

#include <memory>
#include <queue>
#include "heuristics.h"

using namespace std;

namespace planarity {
    class SatEncodeCadical {
    private:
        friend class Clique;
        /**
         * Encodes the graph part.
         */
        inline static void encode_graph(CaDiCaL::Solver &solver, const ConflictGraph &g,
                                        vector<vector<int>> &variables, const unordered_map<node_t, dynamic_bitset<>>& exceptions, const unsigned int ub, bool encode_edges=true) {
            int c_vars = solver.vars();
            for (int n = 0; n < g.getNumNodes(); n++) {
                bool has_nbs = g.adjacency[n].any();
                auto it = exceptions.find(n);

                for (int k = 0; k < ub; k++) {
                    if ((has_nbs || k == 0) && (it == exceptions.end() || !it->second.test(k))) {
                        variables[n][k] = ++c_vars;
                    } else {
                        variables[n][k] = INT_MIN;
                    }
                }
            }
            solver.reserve(c_vars);

            // Each node needs a color
            for (int n = 0; n < g.getNumNodes(); n++) {
                color_t cnt = 0;
                for (int k = 0; k < ub; k++) {
                    if (variables[n][k] != INT_MIN) {
                        cnt++;
                        solver.add(variables[n][k]);
                    }
                }
                if (cnt > 0)
                    solver.add(0);
            }
//            // Each node needs a color
//            for (int n = 0; n < g.getNumNodes(); n++) {
//                for (int k = 0; k < ub; k++) {
//                    if (variables[n][k] != INT_MIN) {
//                        for (int k2 = k + 1; k2 < ub; k2++) {
//                            if (variables[n][k2] != INT_MIN) {
//                                solver.add(-variables[n][k]);
//                                solver.add(-variables[n][k2]);
//                                solver.add(0);
//                            }
//                        }
//                    }
//                }
//            }

            if (encode_edges) {
                // Edges must be colored differently
                for (int n = 0; n < g.getNumNodes(); n++) {
                    for (auto n2 = g.adjacency[n].find_next(n); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                        for (int k = 0; k < ub; k++) {
                            if (variables[n][k] != INT_MIN && variables[n2][k] != INT_MIN) {
                                solver.add(-variables[n][k]);
                                solver.add(-variables[n2][k]);
                                solver.add(0);
                            }
                        }
                    }
                }
            }
        }

        /**
         * Extracts the coloring from a SAT solver model.
         */
        inline static void extract_color(CaDiCaL::Solver &solver, vector<color_t> &coloring,
                                         const vector<vector<int>> &variables) {
            coloring.clear();

            for (const auto &variable: variables) {
                bool found = false;
                for (auto k = 0; k < variable.size(); k++) {
                    if (variable[k] != INT_MIN && solver.val(variable[k]) > 0) {
                        found = true;
                        coloring.push_back(k);
                        break;
                    }
                }
                assert(found);
            }
        }

        static std::shared_ptr<vector<int>>
        createTotalizer(CaDiCaL::Solver &slv, const vector<int> &literals, const unsigned int ub) {
            queue<std::unique_ptr<vector<int>>> currentVars;
            for (const auto &clit: literals) {
                currentVars.push(std::move(std::make_unique<vector<int>>()));
                currentVars.back()->push_back(clit);
            }
            int c_vars = slv.vars();
            while (currentVars.size() > 1) {
                auto l = std::move(currentVars.front());
                currentVars.pop();
                auto r = std::move(currentVars.front());
                currentVars.pop();
                auto minub = min(ub + 1, static_cast<unsigned int>(l->size() + r->size()));

                auto newVars = make_unique<vector<int>>();
                newVars->reserve(minub);

                for (unsigned int i = 0; i < minub; i++) {
                    newVars->push_back(++c_vars);
                }

                auto minub2 = min(minub, static_cast<unsigned int>(r->size()));
                for (unsigned int j = 0; j < minub2; ++j) {
                    slv.add(-r->at(j));
                    slv.add(newVars->at(j));
                    slv.add(0);
                }

                minub2 = min(minub, static_cast<unsigned int>(l->size()));
                for (int i = 0; i < minub2; ++i) {
                    slv.add(-l->at(i));
                    slv.add(newVars->at(i));
                    slv.add(0);
                }

                for (int i = 1; i <= minub2; ++i) {
                    auto minj = min(minub - i, static_cast<unsigned int>(r->size()));
                    for (int j = 1; j <= minj; ++j) {
                        slv.add(-l->at(i - 1));
                        slv.add(-r->at(j - 1));
                        slv.add(newVars->at(i + j - 1));
                        slv.add(0);
                    }
                }

                currentVars.push(std::move(newVars));
            }
            slv.reserve(c_vars);
            return {std::move(currentVars.front())};
        }

    public:
        /**
         * Tries to find a graph coloring of decreasing size for the given graph, using a SAT solver.
         * @param g The graph to color.
         * @param clique A clique in the graph for symmetry breaking, can be empty.
         * @param ub A starting bound on how many colors are required.
         * @param timeout Optional: a timeout for the SAT solver call. Even if the coloring is not (certified) optimal, the SAT call will be terminated after the timeout, 0 means no timeout.
         * @return A graph coloring for the graph. The coloring is empty, if no coloring could be found (invalid upper bound, or timeout exceeded without result).
         */
        static Coloring
        encode_full(const ConflictGraph &g, const vector<node_t> &clique, color_t ub, unsigned int timeout = 0, const string &filename = "", bool optimize=true, bool timeout_for_first=true) {
            vector<vector<int>> variables(g.getNumNodes(), vector<int>(ub));
            vector<color_t> coloring;
            unordered_map<node_t, dynamic_bitset<>> exceptions;
            exceptions.reserve(g.getNumNodes());
            coloring.reserve(g.getNumNodes());

            for (int i = 0; i < clique.size(); i++) {
                auto n = clique[i];
                auto it = exceptions.find(n);
                if (it == exceptions.end())
                    it = get<0>(exceptions.emplace(n, ub));

                for(color_t k=0; k < ub; k++) {
                    if (k != i)
                        it->second.set(k);
                }

                for (auto n2=g.adjacency[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                    auto it2 = exceptions.find(n2);
                    if (it2 == exceptions.end())
                        it2 = get<0>(exceptions.emplace(n2, ub));

                    it2->second.set(i);
                }
            }

            auto slv = CaDiCaL::Solver();

            encode_graph(slv, g, variables, exceptions, ub);

            cout << "Finished encoding" << endl;

            bool solved = true;
            unsigned int counter = 0;
            int result = 0;
            while (solved) {
                if (timeout > 0 and (counter > 0 or timeout_for_first)) {
                    auto th = boost::thread([&]() {
                        boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                        slv.terminate();
                    });
                    result = slv.solve();
                    solved = result == 10;
                    th.interrupt();
                } else {
                    result = slv.solve();
                    solved = result == 10;
                }
                counter++;

                if (solved) {
                    solved = true;
                    extract_color(slv, coloring, variables);

                    assert(g.verify(coloring));
                    if (!filename.empty()) {
                        Coloring::store(filename, g, coloring);
                    }

                    cout << "Found " << ub << " colors" << endl;
                    ub--;

                    if (! optimize)
                        break;

                    // Remove option for color k
                    for (int n = 0; n < g.getNumNodes(); n++) {
                        if (variables[n][ub] != INT_MIN) {
                            slv.add(-variables[n][ub]);
                            slv.add(0);
                        }
                    }
                } else if (result == 20) {
                    cout << "Result is optimal" << endl;
                }
            }
            cout << "Finished solving" << endl;

            return {coloring, ++ub, vector<tuple<int, node_t>>()};
        }

        /**
         * Tries to find a coloring of decreasing size for the graph using a SAT solver. This method assumes that
         * some colorings outside the graph already exist.
         * @param g The graph to color.
         * @param exceptions The colors that are not allowed for some nodes, i.e. existing colors outside g or tabu search.
         * @param num_colors The number of colors currently used, will be used as an upper bound.
         * @param timeout The timeout used for each SAT call. 0 means no timeout.
         * @param timeout_for_first Flag that states if the timeout is used for the first call. Set to true if a result is required.
         * @param limit_cnt Flag that states if the number of colors is minimized.
         * @param limit_color If set to > -1 will try to minimize color assignments to this color.
         * @param limit_color_ub The upper bound for color assignments to the limit_color.
         * @return A graph coloring for the graph. The coloring is empty, if no coloring could be found (invalid upper bound, or timeout exceeded without result).
         */
        static pair<Coloring, bool>
        encode_partial(const SubGraph& g, color_t num_colors,
                       const unsigned int timeout = 0,
                       const bool timeout_for_first = true, const bool limit_cnt = true, const color_t limit_color = INVALID_COLOR,
                       color_t limit_color_ub = 0, const bool optimize=true) {
            vector<vector<int>> variables(g.sub_g.getNumNodes(), vector<int>(num_colors));
            vector<color_t> coloring;
            coloring.reserve(g.sub_g.getNumNodes());
            std::shared_ptr<vector<int>> cardVarsSingleColor = nullptr;
            std::shared_ptr<vector<int>> cardVarsColors = nullptr;
            bool is_unsat = false;

            auto slv = CaDiCaL::Solver();

            unordered_map<node_t, dynamic_bitset<>> exceptions;
            exceptions.reserve(g.exceptions.size());

            // Encode Exceptions
            for (const auto &cEx: g.exceptions) {
                exceptions.emplace(cEx.node, cEx.colors);
            }

            encode_graph(slv, g.sub_g, variables, exceptions, num_colors, true);

            if (limit_cnt) {
                vector<int> literals;
                literals.reserve(num_colors);
                int c_vars = slv.vars();
                for (int k = 0; k < num_colors; k++) {
                    auto c_var = slv.vars() + 1;
                    slv.reserve(++c_vars);
                    for (int n = 0; n < g.sub_g.getNumNodes(); n++) {
                        slv.add(-variables[n][k]);
                        slv.add(c_var);
                        slv.add(0);
                    }
                }
                literals.push_back(c_vars);
                cardVarsColors = createTotalizer(slv, literals, literals.size());
            }

            if (limit_color != INVALID_COLOR) {
                vector<int> literals;
                literals.reserve(g.sub_g.getNumNodes());
                for (int n = 0; n < g.sub_g.getNumNodes(); n++) {
                    if (variables[n][limit_color] != INT_MIN) {
                        literals.push_back(variables[n][limit_color]);
                    }
                }
                limit_color_ub = limit_color_ub < literals.size() ? limit_color_ub : literals.size();

                if (limit_color_ub > 0) {
//                    cardVarsSingleColor = createTotalizer(slv, literals, limit_color_ub + 1);
//                    slv.add(-cardVarsSingleColor->at(limit_color_ub));
//                    slv.add(0);

                    // Create Zinc encoding, as the UBs are usually very small (mostly <= 2)
                    cardVarsSingleColor = make_shared<vector<int>>();
                    vector<vector<int>> cardVarsSingleColorAux(literals.size(), vector<int>(limit_color_ub));

                    int extraVars = 0;
                    slv.reserve(slv.vars() + static_cast<int>(literals.size() * limit_color_ub));
                    for(node_t i=0; i < literals.size(); i++) {
                        for(color_t k=0; k < min(i+1, static_cast<node_t>(limit_color_ub)); k++) {
                            cardVarsSingleColorAux[i][k] = slv.vars() + (++extraVars);

                            if (i > 0) {
                                // Carry over
                                if (k < i) {
                                    assert(cardVarsSingleColorAux[i-1][k] != 0);
                                    assert(cardVarsSingleColorAux[i][k] != 0);
                                    slv.add(-cardVarsSingleColorAux[i - 1][k]);
                                    slv.add(cardVarsSingleColorAux[i][k]);
                                    slv.add(0);
                                }

                                // Increment
                                if (k > 0) {
                                    assert(cardVarsSingleColorAux[i - 1][k - 1] != 0);
                                    slv.add(-literals[i]);
                                    slv.add(-cardVarsSingleColorAux[i - 1][k - 1]);
                                    slv.add(cardVarsSingleColorAux[i][k]);
                                    slv.add(0);
                                }
                            }
                        }

                        // Initialize
                        assert(cardVarsSingleColorAux[i][0] != 0);
                        slv.add(-literals[i]);
                        slv.add(cardVarsSingleColorAux[i][0]);
                        slv.add(0);

                        // Prohibit exceeding the counter
                        if (i >= limit_color_ub) {
                            assert(cardVarsSingleColorAux[i-1][limit_color_ub - 1] != 0);
                            assert(literals[i] != 0);
                            slv.add(-cardVarsSingleColorAux[i-1][limit_color_ub - 1]);
                            slv.add(-literals[i]);
                            slv.add(0);
                        }
                    }

                    for(color_t k=0; k < cardVarsSingleColorAux.back().size(); k++) {
                        cardVarsSingleColor->push_back(cardVarsSingleColorAux.back()[k]);
                    }
                } else
                    cardVarsSingleColor = createTotalizer(slv, literals, literals.size());
            }

            cout << "Finished encoding" << endl;

            bool solved = true;
            unsigned int counter = 0;

            while (solved) {
                if (timeout > 0 and (counter > 0 or timeout_for_first)) {
                    auto th = boost::thread([&]() {
                        boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                        slv.terminate();
                    });
                    auto result = slv.solve();
                    solved = result == 10;
                    th.interrupt();
                    if (result == 20 && counter == 0)
                        is_unsat = true;
                } else {
                    auto result = slv.solve();
                    solved = result == 10;

                    if (result == 20 && counter == 0)
                        is_unsat = true;
                }
                counter++;

                if (solved) {
                    solved = true;
                    extract_color(slv, coloring, variables);

                    cout << "Found " << num_colors << " colors, " << limit_color_ub << " for color " << limit_color
                         << endl;

                    node_t c_cnt = 0;
                    for(auto c_c: coloring) {
                        if (c_c == limit_color)
                            c_cnt++;
                    }
                    cout << "Found " << c_cnt << endl;


                    if (! optimize)
                        break;

                    if (limit_cnt) {
                        num_colors--;
                        slv.add(-cardVarsColors->at(num_colors));
                        slv.add(0);
                    }
//                    if (! limit_cnt && limit_color_ub == 0) {
//                        num_colors--;
//
//                        // Remove option for color k
//                        for (int n = 0; n < g.sub_g.getNumNodes(); n++) {
//                            if (variables[n][num_colors] != var_Undef)
//                                slv.addClause(Glucose30::mkLit(variables[n][num_colors], true));
//                        }
//                    }
                    if (limit_color != INVALID_COLOR && limit_color_ub > 0) {
                        limit_color_ub--;
                        slv.add(-cardVarsSingleColor->at(limit_color_ub));
                        slv.add(0);
                    } else if (limit_color != INVALID_COLOR && limit_color_ub == 0) {
                        break;
                    }
                }
            }
            cout << "Finished solving" << endl;
            return pair<Coloring, bool>(Coloring(coloring, num_colors, vector<tuple<int, node_t>>()), is_unsat);
        }
    };
}

#endif //CPP_SAT_ENCODE2_H
