//
// Createdhidler on 10/15/21.
//

#ifndef CPP_SAT_ENCODE_H
#define CPP_SAT_ENCODE_H

#include "conflict_graph.h"
#include "glucose30/core/Solver.h"
#include "glucose30/core/SolverTypes.h"
#include <boost/thread/thread.hpp>

#include <memory>
#include <queue>
#include "heuristics.h"

using namespace std;

namespace planarity {
    class SatEncode {
    private:
        friend class Clique;
        /**
         * Encodes the graph part.
         */
        inline static void encode_graph(Glucose30::Solver &solver, const ConflictGraph &g,
                                        vector<vector<Glucose30::Var>> &variables, const unordered_map<node_t, dynamic_bitset<>>& exceptions, const unsigned int ub, bool encode_edges=true) {
            for (int n = 0; n < g.getNumNodes(); n++) {
                bool has_nbs = g.adjacency[n].any();
                auto it = exceptions.find(n);

                for (int k = 0; k < ub; k++) {
                    if ((has_nbs || k == 0) && (it == exceptions.end() || !it->second.test(k)))
                        variables[n][k] = solver.newVar();
                    else
                        variables[n][k] = var_Undef;
                }
            }

            Glucose30::vec<Glucose30::Lit> clause;
            clause.growTo(static_cast<int>(ub));

            // Each node needs a color
            for (int n = 0; n < g.getNumNodes(); n++) {
                clause.clear();

                for (int k = 0; k < ub; k++) {
                    if (variables[n][k] != var_Undef) {
                        clause.push(Glucose30::mkLit(variables[n][k]));

//                        for (int k2 = k + 1; k2 < ub; k2++) {
//                            if (variables[n][k2] != var_Undef) {
//                                solver.addClause(Glucose30::mkLit(variables[n][k], true),
//                                                 Glucose30::mkLit(variables[n][k2], true));
//                            }
//                        }
                    }
                }
                assert(clause.size() > 0);
                solver.addClause(clause);
            }

            if (!solver.okay())
                cout << "Before" << endl;

            if (encode_edges) {
                node_t edge_cnt = 0;
                // Edges must be colored differently
                for (int n = 0; n < g.getNumNodes(); n++) {
                    for (auto n2 = g.adjacency[n].find_next(n); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[n].find_next(n2)) {
                        for (int k = 0; k < ub; k++) {
                            if (variables[n][k] != var_Undef && variables[n2][k] != var_Undef) {
                                solver.addClause(Glucose30::mkLit(variables[n][k], true),
                                                 Glucose30::mkLit(variables[n2][k], true));

                                edge_cnt++;
                            }
                        }
                    }
                }
                cout << "Encoded " << edge_cnt << " edges." << endl;
            }
        }

        /**
         * Extracts the coloring from a SAT solver model.
         */
        inline static void extract_color(const Glucose30::Solver &solver, vector<color_t> &coloring,
                                         const vector<vector<Glucose30::Var>> &variables) {
            coloring.clear();

            for (const auto &variable: variables) {
                bool found = false;
                for (auto k = 0; k < variable.size(); k++) {
                    if (variable[k] != var_Undef && solver.model[variable[k]] == g3l_True) {
                        found = true;
                        coloring.push_back(k);
                        break;
                    }
                }
                assert(found);
            }
        }

        static void AmoCommander(Glucose30::Solver& slv, const vector<Glucose30::Var>& variables, const unsigned int m) {
            if (variables.size() <= m) {
                for(auto i=0; i < variables.size(); i++) {
                    for(auto j=i+1; j < variables.size(); j++) {
                        slv.addClause(Glucose30::mkLit(variables[i], true), Glucose30::mkLit(variables[j], true));
                    }
                }
            } else {
                vector<Glucose30::Var> new_variables;
                new_variables.reserve(variables.size()/m + 1);

                for(auto cc=0; cc < m; cc++) {
                    auto nv = slv.newVar();
                    new_variables.push_back(nv);

                    for(auto i=cc * m; i < variables.size() && i < (cc+1)*m; i++) {
                        slv.addClause(Glucose30::mkLit(nv), Glucose30::mkLit(variables[i], true));
                    }
                    for(auto i=cc * m; i < variables.size() && i < (cc+1)*m; i++) {
                        for(auto j=i+1; j < variables.size() && j < (cc+1)*m; j++) {
                            slv.addClause(Glucose30::mkLit(variables[j], true), Glucose30::mkLit(variables[i], true));
                        }
                    }
                }
                AmoCommander(slv, new_variables, m);
            }
        }

        static std::shared_ptr<vector<Glucose30::Lit>>
        createTotalizer(Glucose30::Solver &slv, const vector<Glucose30::Lit> &literals, const unsigned int ub) {
            queue<std::unique_ptr<vector<Glucose30::Lit>>> currentVars;
            for (const auto &clit: literals) {
                currentVars.push(std::move(std::make_unique<vector<Glucose30::Lit>>()));
                currentVars.back()->push_back(clit);
            }

            while (currentVars.size() > 1) {
                auto l = std::move(currentVars.front());
                currentVars.pop();
                auto r = std::move(currentVars.front());
                currentVars.pop();
                auto minub = min(ub + 1, static_cast<unsigned int>(l->size() + r->size()));

                auto newVars = make_unique<vector<Glucose30::Lit>>();
                newVars->reserve(minub);

                for (unsigned int i = 0; i < minub; i++) {
                    newVars->push_back(Glucose30::mkLit(slv.newVar()));
                }

                auto minub2 = min(minub, static_cast<unsigned int>(r->size()));
                for (unsigned int j = 0; j < minub2; ++j) {
                    slv.addClause(Glucose30::mkLit(r->at(j).x / 2, true), newVars->at(j));
                }

                minub2 = min(minub, static_cast<unsigned int>(l->size()));
                for (int i = 0; i < minub2; ++i) {
                    slv.addClause(Glucose30::mkLit(l->at(i).x / 2, true), newVars->at(i));
                }

                for (int i = 1; i <= minub2; ++i) {
                    auto minj = min(minub - i, static_cast<unsigned int>(r->size()));
                    for (int j = 1; j <= minj; ++j) {
                        slv.addClause(
                                Glucose30::mkLit(l->at(i - 1).x / 2, true),
                                Glucose30::mkLit(r->at(j - 1).x / 2, true),
                                newVars->at(i + j - 1)
                        );
                    }
                }

                currentVars.push(std::move(newVars));
            }
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
            vector<vector<Glucose30::Var>> variables(g.getNumNodes(), vector<Glucose30::Var>(ub));
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

            auto slv = Glucose30::Solver();
            //slv.setIncrementalMode();

            encode_graph(slv, g, variables, exceptions, ub);

            cout << "Finished encoding" << endl;

            bool solved = true;
            unsigned int counter = 0;

            while (solved) {
                if (timeout > 0 && (counter > 0 || timeout_for_first)) {
                    // TODO: Fix many threads, use boost threads with interrupt?
                    auto th = boost::thread([&]() {
                        boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                        slv.interrupt();
                    });
                    slv.clearInterrupt();
                    solved = slv.solve();
                    th.interrupt();
                } else {
                    slv.verbosity = 0;
                    solved = slv.solve();
                    slv.printIncrementalStats();
                }
                counter++;

                if (solved) {
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
                        if (variables[n][ub] != var_Undef)
                            slv.addClause(Glucose30::mkLit(variables[n][ub], true));
                    }
                } else if (timeout == 0) {
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
                       color_t limit_color_ub = 0, const bool optimize=true, color_t suggested_color = INVALID_COLOR, const dynamic_bitset<>& suggested_nodes=dynamic_bitset<>()) {
            vector<vector<Glucose30::Var>> variables(g.sub_g.getNumNodes(), vector<Glucose30::Var>(num_colors));
            vector<color_t> coloring;
            coloring.reserve(g.sub_g.getNumNodes());
            std::shared_ptr<vector<Glucose30::Lit>> cardVarsSingleColor = nullptr;
            std::shared_ptr<vector<Glucose30::Lit>> cardVarsColors = nullptr;

            auto slv = Glucose30::Solver();
            slv.setIncrementalMode();

            unordered_map<node_t, dynamic_bitset<>> exceptions;
            exceptions.reserve(g.exceptions.size());

            // Encode Exceptions
            for (const auto &cEx: g.exceptions) {
                exceptions.emplace(cEx.node, cEx.colors);
            }

            encode_graph(slv, g.sub_g, variables, exceptions, num_colors, true);

            Glucose30::vec<Glucose30::Lit> assps;
            if (suggested_color != INVALID_COLOR) {
                for(auto cn = suggested_nodes.find_first(); cn != dynamic_bitset<>::npos; cn = suggested_nodes.find_next(cn)) {
                    assps.push(Glucose30::mkLit(variables[cn][suggested_color]));
                }
            }

//            int options = 0;
//            for(node_t cn=0; cn < g.sub_g.getNumNodes(); cn++) {
//                for(color_t k=0; k < num_colors; k++) {
//                    if (variables[cn][k] != var_Undef)
//                        options++;
//                }
//            }
//            cout << "Options " << options << endl;

            if (limit_cnt) {
                vector<Glucose30::Lit> literals;
                literals.reserve(num_colors);

                for (int k = 0; k < num_colors; k++) {
                    auto c_var = slv.newVar();
                    literals.push_back(Glucose30::mkLit(c_var));
                    for (int n = 0; n < g.sub_g.getNumNodes(); n++) {
                        slv.addClause(Glucose30::mkLit(variables[n][k], true), Glucose30::mkLit(c_var));
                    }
                }
                cardVarsColors = createTotalizer(slv, literals, literals.size());
            }

            if (limit_color != INVALID_COLOR) {
                vector<Glucose30::Lit> literals;
                literals.reserve(g.sub_g.getNumNodes());
                for (int n = 0; n < g.sub_g.getNumNodes(); n++) {
                    if (variables[n][limit_color] != var_Undef) {
                        literals.push_back(Glucose30::mkLit(variables[n][limit_color]));
                    }
                }

                limit_color_ub = limit_color_ub < literals.size() ? limit_color_ub : literals.size() - 1;

                if (limit_color_ub > 0) {
                    cardVarsSingleColor = createTotalizer(slv, literals, limit_color_ub + 1);
                    slv.addClause(Glucose30::mkLit(cardVarsSingleColor->at(limit_color_ub).x / 2, true));
                } else
                    cardVarsSingleColor = createTotalizer(slv, literals, literals.size());
            }

            //cout << "Finished encoding" << endl;

            bool solved = true;
            unsigned int counter = 0;
            bool is_unsat = true;

            while (solved) {
                if (timeout > 0 and (counter > 0 or timeout_for_first)) {
                    auto th = boost::thread([&]() {
                        boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                        slv.interrupt();
                        is_unsat = false;
                    });
                    slv.clearInterrupt();
                    if (counter == 0 && suggested_color != INVALID_COLOR)
                        solved = slv.solve(assps);
                    else
                        solved = slv.solve();
                    th.interrupt();
                } else {
                    if (counter == 0 && suggested_color != INVALID_COLOR)
                        solved = slv.solve(assps);
                    else
                        solved = slv.solve();
                }
                counter++;

                if (solved) {
                    is_unsat = false;
                    extract_color(slv, coloring, variables);
//
//                    cout << "Found " << num_colors << " colors, " << limit_color_ub << " for color " << limit_color
//                         << endl;

                    if (! optimize)
                        break;

                    if (limit_cnt) {
                        num_colors--;
                        slv.addClause(Glucose30::mkLit(cardVarsColors->at(num_colors).x / 2, true));
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
                        slv.addClause(Glucose30::mkLit(cardVarsSingleColor->at(limit_color_ub).x / 2, true));
                    } else if (limit_color != INVALID_COLOR && limit_color_ub == 0) {
                        break;
                    }
                }
            }
            //cout << "Finished solving" << endl;
            return pair<Coloring, bool>(Coloring(coloring, num_colors, vector<tuple<int, node_t>>()), is_unsat);
        }
//
//        static void ind_set_heuristic(const ConflictGraph &g, const vector<node_t>& clique, const string &filename = "", const int timeout = 60) {
//            vector<Glucose30::Var> variables;
//            variables.reserve(g.getNumNodes());
//            dynamic_bitset<> done(g.getNumNodes());
//            vector<Glucose30::Lit> literals;
//            literals.reserve(g.getNumNodes());
//            color_t colors = 0;
//            vector<color_t> coloring(g.getNumNodes());
//
//            while (done.count() < g.getNumNodes()) {
//                colors += 1;
//                Glucose30::Solver solver;
//                solver.setIncrementalMode();
//                variables.clear();
//                literals.clear();
//
//                for (auto i = 0; i < g.getNumNodes(); i++) {
//                    if (!done[i]) {
//                        variables.push_back(solver.newVar());
//                        literals.push_back(Glucose30::mkLit(variables.back()));
//                    } else {
//                        variables.push_back(0);
//                    }
//                }
//
//                for (auto n = 0; n < g.getNumNodes(); n++) {
//                    if (! done[n]) {
//                        auto cNb = g.adjacency[n] - done;
//                        for (auto n2 = cNb.find_first(); n2 != dynamic_bitset<>::npos and n2 < n; n2 = cNb.find_next(n2)) {
//                            solver.addClause(Glucose30::mkLit(variables[n]), Glucose30::mkLit(variables[n2]));
//                        }
//                    }
//                }
//
//                if (colors <= clique.size())
//                    solver.addClause(Glucose30::mkLit(variables[clique[colors-1]], true));
//
//                auto rhs = SatEncode::createTotalizer(solver, literals, literals.size());
//
//                cout << "Encoded Independent set" << endl;
//
//                bool solved = true;
//                dynamic_bitset<> current_is(g.getNumNodes());
//                while (solved) {
//                    if (timeout > 0) {
//                        bool running = true;
//                        auto th = boost::thread([&]() {
//                            boost::this_thread::sleep(boost::posix_time::seconds(timeout));
//                            solver.interrupt();
//                        });
//                        solver.clearInterrupt();
//                        solved = solver.solve();
//                        th.interrupt();
//                    } else {
//                        solved = solver.solve();
//                    }
//
//                    if (solved) {
//                        unsigned int issize = 0;
//                        current_is.reset();
//                        for (int i = 0; i < variables.size(); i++) {
//                            if (! done[i] && solver.model[variables[i]] == g3l_False) {
//                                current_is[i] = true;
//                                issize++;
//                            }
//                        }
//
//                        cout << "Found independent set of size " << issize << endl;
//                        if (issize < literals.size()) {
//                            solver.addClause(Glucose30::mkLit(rhs->at(literals.size() - 1 - issize).x / 2, true));
//                        } else {
//                            solved = false;
//                        }
//                    }
//                }
//                done |= current_is;
//                for (auto n = current_is.find_first(); n != dynamic_bitset<>::npos; n = current_is.find_next(n)) {
//                    coloring[n] = colors - 1;
//                }
//            }
//            cout << colors << " Required" << endl;
//
//            Coloring result(coloring, colors, vector<tuple<int, node_t>>());
//            tabuSearch(g, result, result.numColors);
//        }
    };
}

#endif //CPP_SAT_ENCODE_H
