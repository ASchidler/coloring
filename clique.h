//
// Created on 13.10.21.
//

#ifndef CPP_CLIQUE_H
#define CPP_CLIQUE_H
#include "conflict_graph.h"
#include "glucose30/core/Solver.h"
#include "sat_encode.h"

using namespace std;
namespace planarity {
    class Myciel {
    private:
        void init(const ConflictGraph& g) {
            unordered_map<node_t, dynamic_bitset<>> S;
            S.reserve(clique_set.count() + 100);

            dynamic_bitset<> common_nbs(g.getNumNodes());
            common_nbs.set(0);

            while(common_nbs.any()) {
                for(auto n=component.find_first(); n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                    // Find all nodes that share a common neighborhood with the current node (all nodes that are neighbors of all neighbors of n)
                    auto nnb = (g.adjacency[n] & component);
                    dynamic_bitset<> viable(g.getNumNodes());
                    viable.flip();

                    for (auto n2=nnb.find_first(); n2 != dynamic_bitset<>::npos; n2 = nnb.find_next(n2)) {
                        viable &= g.adjacency[n2];
                    }

                    assert(viable[n]);
                    S[n] = std::move(viable);
                }

                // Now share at least one node in S for each n in the current component.
                common_nbs = component;
                common_nbs.flip();
                for(auto n=component.find_first(); n != dynamic_bitset<>::npos && common_nbs.any(); n = component.find_next(n)) {
                    // Add all nodes adjacent to any of the entries.
                    dynamic_bitset<> cnb(g.getNumNodes());
                    for (auto n2=S[n].find_first(); n2 != dynamic_bitset<>::npos; n2 = S[n].find_next(n2)) {
                        cnb |= g.adjacency[n2];
                    }
                    common_nbs &= cnb;
                }

                if (common_nbs.any()) {
                    bound += 1;

                    // Add w
                    auto new_n = common_nbs.find_first();
                    dynamic_bitset<> new_nodes(g.getNumNodes());
                    new_nodes.set(new_n);

                    // Add one shared node per node in the Myciel component and w
                    for(auto n=component.find_first(); n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                        auto sharedNb = (g.adjacency[new_n] & S[n]);
                        // Check if one necessary node has already been added.
                        if (!((component | new_nodes) & sharedNb ).any()) {
                            auto add_n = sharedNb.find_first();
                            new_nodes.set(add_n);
                        }
                    }

                    component |= new_nodes;
                }
            }

            component -= clique_set;
            assert(verify(g));
        }
        Myciel(dynamic_bitset<>& clique_set, dynamic_bitset<>& component, node_t bound) : clique_set(clique_set), component(component), bound(bound) {

        }
    public:
        dynamic_bitset<> clique_set;
        dynamic_bitset<> component;
        node_t bound = 0;

        Myciel(const ConflictGraph& g, const dynamic_bitset<>& clique) : component(g.getNumNodes()), clique_set(g.getNumNodes()) {
            bound = clique.count();
            clique_set = clique;
            component = clique;

            init(g);
        }

        Myciel(const ConflictGraph& g, const vector<node_t>& clique) : component(g.getNumNodes()), clique_set(g.getNumNodes()) {
            bound = clique.size();

            for(auto n: clique) {
                clique_set.set(n);
                component.set(n);
            }

            init(g);
        }

        [[nodiscard]] bool verify(const ConflictGraph& g) const{
            unordered_map<node_t, dynamic_bitset<>> reserved;
            reserved.reserve(component.count());
            auto added_nodes = component;
            color_t c_bound = 0;

            // Set clique colors
            for(auto i=clique_set.find_first(); i != dynamic_bitset<>::npos; i = clique_set.find_next(i)) {
                auto common = g.adjacency[i] & component;
                for(auto n2=common.find_first(); n2 != dynamic_bitset<>::npos; n2 = common.find_next(n2)) {
                    auto it = reserved.find(n2);
                    if (it == reserved.end())
                        it = get<0>(reserved.emplace(n2, bound));
                    it->second.set(c_bound);
                }

                c_bound++;
            }

            // Add entries for nodes not adjacent to the clique
            for(auto n=added_nodes.find_first(); n != dynamic_bitset<>::npos; n = added_nodes.find_next(n)) {
                auto it = reserved.find(n);
                if (it == reserved.end())
                    reserved.emplace(n, bound);
            }

            // Start coloring
            bool changed = true;
            while (changed) {
                changed = false;
                for(auto offset=1; offset >= 0; offset--) {
                    for (auto n = added_nodes.find_first(); n != dynamic_bitset<>::npos && !changed; n = added_nodes.find_next(n)) {
                        // First the implied colors and then the nodes that cannot be colored within the current bound
                        if (reserved[n].count() + offset == c_bound) {
                            changed = true;
                            // Try to find nodes with an implied color first, if none, try to find those that have no color available
                            reserved[n].flip();
                            auto cc = reserved[n].find_first();

                            if (cc == dynamic_bitset<>::npos)
                                return true;

                            auto common = g.adjacency[n] & added_nodes;
                            for (auto n2 = common.find_first();
                                 n2 != dynamic_bitset<>::npos; n2 = common.find_next(n2)) {
                                reserved[n2].set(cc);
                            }
                            added_nodes.reset(n);

                            if (cc >= c_bound) {
                                c_bound = cc + 1;
                            }
                        }
                    }
                }
            }

            return c_bound == bound;
        }

        void store(const ConflictGraph &g, const string &filename) const {
            if (verify(g)) {
                ofstream myfile(filename);
                if (myfile.is_open()) {
                    myfile << bound << endl;

                    auto n=clique_set.find_first();
                    if (n != dynamic_bitset<>::npos)
                        myfile << n;
                    for(; n != dynamic_bitset<>::npos; n = clique_set.find_next(n)) {
                        myfile << "," << n;
                    }
                    myfile << endl;

                    n=component.find_first();
                    if (n != dynamic_bitset<>::npos)
                        myfile << n;
                    for(; n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                        myfile << "," << n;
                    }
                    myfile << endl;
                    myfile.close();
                }
            } else {
                cout << "Invalid Myciel" << endl;
            }
        }

        /**
         * Loads a clique stored in a file.
         */
        static Myciel import(const string &filename, const ConflictGraph& g) {
            fstream fl;

            fl.open(filename, ios::in);
            vector<node_t> clique;
            int line_no = 0;
            node_t bound = 0;
            dynamic_bitset<> clique_set(g.getNumNodes());
            dynamic_bitset<> component(g.getNumNodes());

            if (fl.is_open()) {
                string ln;
                while (getline(fl, ln)) {
                    // Trim
                    ln.erase(ln.begin(), std::find_if(ln.begin(), ln.end(),
                                                      std::not1(std::ptr_fun<int, int>(std::isspace))));
                    if (ln.length() > 0) {
                        istringstream iss(ln);
                        string tok;

                        for (long i = 0; getline(iss, tok, ','); i++) {
                            if (line_no == 0)
                                bound = stoul(tok);
                            else if (line_no == 1)
                                clique_set.set(stoul(tok));
                            else
                                component.set(stoul(tok));
                        }
                    }
                    line_no++;
                }
            }

            return Myciel(clique_set, component, bound);
        }
    };

    class Clique {
    public:
        static bool isClique(const vector<unsigned int> &clique, const ConflictGraph &g) {
            dynamic_bitset<> currentNbs(g.getNumNodes());
            for (const auto n: clique) {
                currentNbs.set(n);
            }

            for (const auto cNode: clique) {
                if ((g.adjacency[cNode] & currentNbs).count() != clique.size() - 1)
                    return false;
            }

            return true;
        }

        static void storeClique(const vector<unsigned int> &clique, const ConflictGraph &g, const string &filename) {
            if (isClique(clique, g)) {
                ofstream myfile(filename);
                if (myfile.is_open()) {
                    myfile << clique[0];
                    for (int i = 1; i < clique.size(); i++) {
                        myfile << "," << clique[i];
                    }
                    myfile << endl;
                    myfile.close();
                }
            } else {
                cout << "Invalid clique" << endl;
            }
        }

        /**
         * Loads a clique stored in a file.
         */
        static vector<node_t> importClique(const string &filename) {
            fstream fl;

            fl.open(filename, ios::in);
            vector<node_t> clique;

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
                            node_t cc = stoul(tok);
                            clique.push_back(cc);
                        }
                    }
                }
            }

            return clique;
        }

        /**
         * Finds maximal cliques in a greedy fashion. Processes the nodes from largest degree to smallest.
         */
        static void findCliqueGreedy(const ConflictGraph &g, vector<node_t> &start, node_t lb, node_t myciel_lb = 0, bool extend_myciel = false, const string &filename = "", const string &filename_myciel = "", bool useRankOrder=false) {
            BucketQueue q(g.getNumNodes());
            color_t best_myciel = 0;

            vector<node_t> nodes;
            nodes.reserve(g.getNumNodes());
            vector<node_t> degeneracy;
            degeneracy.reserve(g.getNumNodes());
            unordered_map<node_t, node_t> ranks;
            ranks.reserve(g.getNumNodes());

            auto done = dynamic_bitset<>(g.getNumNodes());

            for(int i=0; i < g.getNumNodes(); i++) {
                auto degree = g.getDegree(i);
                q.add(degree, i);
                degeneracy.push_back(degree);
            }
            node_t c_degeneracy = 0;
            while(! q.empty()) {
                auto element = q.next();
                nodes.emplace_back(get<1>(element));
                if (get<0>(element) > c_degeneracy)
                    c_degeneracy = get<0>(element);
                done[get<1>(element)] = true;
                degeneracy[get<1>(element)] = c_degeneracy;

                auto newNb = g.adjacency[get<1>(element)] - done;
                for (auto nb = newNb.find_first(); nb != dynamic_bitset<>::npos; nb = newNb.find_next(nb)) {
                    q.change(degeneracy[nb], degeneracy[nb]-1, nb);
                    degeneracy[nb] -= 1;
                }
            }
            reverse(nodes.begin(), nodes.end());
            for (node_t i=0; i < nodes.size(); i++) {
                ranks.emplace(nodes[i], i);
            }

            int c_best = static_cast<int>(start.size());
            nodes.reserve(g.getNumNodes());

            vector<node_t> cClique;
            dynamic_bitset<> currentNbs(g.getNumNodes());

            for (auto n: nodes) {
                if (degeneracy[n] < start.size())
                    return;

                currentNbs = g.adjacency[n];
                cClique.push_back(n);
                bool replace_first = false;
                bool is_first = true;
                while (currentNbs.any()) {
                    dynamic_bitset<>::size_type c_max_nbs = 0;
                    node_t c_max_rank = 0;
                    node_t c_max_node = INVALID_NODE;

                    for (auto n2 = currentNbs.find_first();
                         n2 != dynamic_bitset<>::npos; n2 = currentNbs.find_next(n2)) {

                        if (useRankOrder) {
                            if (c_max_node == INVALID_NODE || c_max_rank < ranks[n2]) {
                                c_max_node = static_cast<node_t>(n2);
                                c_max_rank = ranks[n2];
                            }
                        } else if ((extend_myciel && degeneracy[n2] >= start.size()) || degeneracy[n2] > start.size()){
                            auto currentCommon = (currentNbs & g.adjacency[n2]).count();
                            if (c_max_node == INVALID_NODE || replace_first || currentCommon > c_max_nbs || (currentCommon == c_max_nbs && c_max_rank < ranks[n2])) {
                                c_max_nbs = currentCommon;
                                c_max_node = static_cast<node_t>(n2);
                                c_max_rank = ranks[n2];
                                // Avoid same opening moves
                                replace_first = (is_first && degeneracy[n2] < degeneracy[n]);
                                is_first = false;
                            }
                        }
                    }
                    if (c_max_node == INVALID_NODE)
                        break;
                    currentNbs &= g.adjacency[c_max_node];
                    if (cClique.size() + currentNbs.count() <= c_best && !extend_myciel)
                        break;

                    cClique.push_back(c_max_node);
                }

                if (extend_myciel && !currentNbs.any() && !cClique.empty()) {
                    auto myc = Myciel(g, cClique);

                    if (myc.bound > best_myciel) {
                        best_myciel = myc.bound;

                        if (best_myciel > myciel_lb && !filename_myciel.empty()) {
                            myciel_lb = best_myciel;
                            myc.store(g, filename_myciel);
                        }
                    }
                }

                if (cClique.size() > c_best) {
                    c_best = static_cast<int>(cClique.size());
                    start.clear();
                    start.insert(start.begin(), cClique.begin(), cClique.end());

                    if (cClique.size() > lb) {
                        if (!filename.empty()) {
                            storeClique(start, g, filename);
                        }
                    }
                }
                cClique.clear();
            }
        }

        static void findCliqueGreedy2(const ConflictGraph &g, vector<node_t>& start, node_t lb, node_t myciel_lb = 0, const bool extend_myciel = false, const string &filename = "", const string& filename_myciel = "", bool reducedNumber = true) {
            BucketQueue q(g.getNumNodes());

            vector<node_t> nodes;
            nodes.reserve(g.getNumNodes());
            vector<node_t> degeneracy(g.getNumNodes());
            unordered_map<node_t, node_t> ranks;
            ranks.reserve(g.getNumNodes());
            vector<tuple<node_t, node_t>> degrees;
            degrees.reserve(g.getNumNodes());

            auto done = dynamic_bitset<>(g.getNumNodes());

            for(node_t i=0; i < g.getNumNodes(); i++) {
                auto degree = g.getDegree(i);
                degrees.emplace_back(degree, i);
            }

            sort(degrees.rbegin(), degrees.rend());
            unordered_map<node_t, node_t> degree_map;
            degree_map.reserve(g.getNumNodes());
            for(node_t i=0; i < g.getNumNodes(); i++) {
                degree_map[get<1>(degrees[i])] = i;
            }

            for(node_t i=0; i < g.getNumNodes(); i++) {
                q.add(get<0>(degrees[i]), i);
                degeneracy[get<1>(degrees[i])] = get<0>(degrees[i]);
            }

            node_t c_degeneracy = 0;
            while(! q.empty()) {
                auto element = q.next();
                auto n = get<1>(degrees[get<1>(element)]);
                nodes.emplace_back(n);
                if (get<0>(element) > c_degeneracy)
                    c_degeneracy = get<0>(element);
                done[n] = true;
                degeneracy[n] = c_degeneracy;

                auto newNb = g.adjacency[n] - done;
                for (auto nb = newNb.find_first(); nb != dynamic_bitset<>::npos; nb = newNb.find_next(nb)) {
                    q.change(degeneracy[nb], degeneracy[nb]-1, degree_map[nb]);
                    degeneracy[nb] -= 1;
                }
            }
            reverse(nodes.begin(), nodes.end());

            vector<dynamic_bitset<>> cliques;
            cliques.reserve(g.getNumNodes());

            for (auto n: nodes) {
                bool found = false;

                for(auto& cc: cliques) {
                    if (cc.is_subset_of(g.adjacency[n])) {
                        cc.set(n);
                        found = reducedNumber;
                    }
                }
                if (! found) {
                    cliques.emplace_back(g.getNumNodes());
                    cliques.back().set(n);
                }
            }

            node_t maxClique = 0;
            node_t maxMyciel = 0;

            for(auto& c: cliques) {
                auto cnt = c.count();
                if (extend_myciel && cnt > maxClique * 4 / 3) {
                    auto m = Myciel(g, c);
                    if (m.bound > maxMyciel) {
                        maxMyciel = m.bound;
                        if (maxMyciel > myciel_lb && !filename_myciel.empty()) {
                            m.store(g, filename_myciel);
                            myciel_lb = maxMyciel;
                        }
                    }
                }
                if (cnt > maxClique) {
                    maxClique = cnt;
                    if (cnt > lb) {
                        lb = cnt;
                        start.clear();
                        start.reserve(cnt);
                        for (auto cn=c.find_first(); cn != dynamic_bitset<>::npos; cn = c.find_next(cn))
                            start.push_back(cn);
                        if (!filename.empty()) {
                            storeClique(start, g, filename);
                        }
                    }
                }
            }
        }

        static void findCliqueSatPartial(const ConflictGraph &g, vector<unsigned int> &start, const string &filename = "",
                                  const int timeout = 10) {
            vector<pair<int, int>> nodes;
            nodes.reserve(g.getNumNodes());

            // Order by highest degree first
            for (int n = 0; n < g.getNumNodes(); n++) {
                nodes.emplace_back(g.adjacency[n].count(), n);
            }
            sort(nodes.rbegin(), nodes.rend());

            // Stores the variables
            vector<Glucose30::Var> vars;
            vector<Glucose30::Lit> lits;
            unordered_map<unsigned int, unsigned int> rNodeMap;
            vector<unsigned int> nodeMap;

            // Find maximum cliques in turn
            for (auto &cEntry: nodes) {
                if (get<0>(cEntry) < start.size())
                    return;

                int n = get<1>(cEntry);

                auto cNb = g.adjacency[n];
                auto neighbors = cNb.count();

                Glucose30::Solver solver;
                solver.setIncrementalMode();
                vars.clear();
                lits.clear();
                nodeMap.clear();
                rNodeMap.clear();

                if (vars.size() < neighbors + 1) {
                    vars.reserve(neighbors + 1);
                    lits.reserve(neighbors + 1);
                    nodeMap.reserve(neighbors + 1);
                    rNodeMap.reserve(neighbors + 1);
                }
                vars.push_back(solver.newVar());
                nodeMap.push_back(n);
                rNodeMap.emplace(n, nodeMap.size() - 1);
                solver.addClause(Glucose30::mkLit(vars.back(), true));

                // Reduce the number of possible vertices to a safe number, by greedily adding vertices to the clique
                // until the shared neighborhood becomes manageable.
                while (neighbors > 15000) {
                    dynamic_bitset<>::size_type c_max = 0;
                    unsigned int c_best = 0;

                    for (auto n2 = cNb.find_first(); n2 != dynamic_bitset<>::npos; n2 = cNb.find_next(n2)) {
                        auto new_count = (cNb & g.adjacency[n2]).count();
                        if (new_count > c_max) {
                            c_max = new_count;
                            c_best = n2;
                        }
                    }

                    assert(c_max > 0);

                    vars.push_back(solver.newVar());
                    nodeMap.push_back(c_best);
                    rNodeMap.emplace(c_best, nodeMap.size() - 1);
                    solver.addClause(Glucose30::mkLit(vars.back(), true));
                    cNb &= g.adjacency[c_best];
                    neighbors = cNb.count();
                }

                for (auto n2 = cNb.find_first(); n2 != dynamic_bitset<>::npos; n2 = cNb.find_next(n2)) {
                    // All non-edges
                    auto newNb = g.adjacency[n] - g.adjacency[n2];
                    // If the shared neighbors are lower than the current lower bound, cannot be part of better clique...
                    if (neighbors - newNb.count() + 2 < start.size()) {
                        continue;
                    }

                    vars.push_back(solver.newVar());
                    nodeMap.push_back(n2);
                    rNodeMap.emplace(n2, nodeMap.size() - 1);
                    lits.push_back(Glucose30::mkLit(vars.back()));

                    for (auto n3 = newNb.find_first();
                         n2 != dynamic_bitset<>::npos && n3 < n2; n3 = newNb.find_next(n3)) {
                        auto it = rNodeMap.find(n3);
                        if (it != rNodeMap.end()) {
                            solver.addClause(Glucose30::mkLit(vars.back()), Glucose30::mkLit(vars[it->second]));
                        }
                    }
                }

                auto rhs = SatEncode::createTotalizer(solver, lits, lits.size());
                if (!start.empty())
                    solver.addClause(Glucose30::mkLit(rhs->at(vars.size() - 1 - start.size()).x / 2, true));

                bool solved = true;
                while (solved) {
                    if (timeout > 0) {
                        bool running = true;
                        solver.clearInterrupt();
                        auto th = boost::thread([&]() {
                            boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                            solver.interrupt();
                        });
                        solved = solver.solve();
                        th.interrupt();
                    } else {
                        solved = solver.solve();
                    }

                    if (solved) {
                        start.clear();
                        for (int i = 0; i < vars.size(); i++) {
                            if (solver.model[vars[i]] == g3l_False)
                                start.push_back(nodeMap[i]);
                        }
                        if (!filename.empty())
                            storeClique(start, g, filename);

                        cout << "Found clique of size " << start.size() << endl;
                        solver.addClause(Glucose30::mkLit(rhs->at(vars.size() - 1 - start.size()).x / 2, true));
                    }
                }

                cout << "Finished node " << n << endl;
            }
        }

        static void findCliqueSat(const ConflictGraph &g, vector<unsigned int> &start, const string &filename = "",
                                         const int timeout = 10) {
            // Stores the variables
            vector<Glucose30::Var> vars;
            vector<Glucose30::Lit> lits;

            vars.reserve(g.getNumNodes());
            lits.reserve(g.getNumNodes());

            Glucose30::Solver solver;
            solver.setIncrementalMode();
            vars.clear();
            lits.clear();

            // Find maximum cliques in turn
            for (node_t n=0; n < g.getNumNodes(); n++) {
                vars.push_back(solver.newVar());
                lits.push_back(Glucose30::mkLit(vars.back()));
            }

            for(node_t n=0; n < g.getNumNodes(); n++) {
                auto inv = ~g.adjacency[n];

                for (auto n2=inv.find_next(n); n2 != dynamic_bitset<>::npos; n2 = inv.find_next(n2)) {
                    solver.addClause(lits[n], lits[n2]);
                }
            }

            auto rhs = SatEncode::createTotalizer(solver, lits, lits.size());
            if (!start.empty())
                solver.addClause(Glucose30::mkLit(rhs->at(vars.size() - 1 - start.size()).x / 2, true));

            bool solved = true;
            while (solved) {
                if (timeout > 0) {
                    bool running = true;
                    auto th = boost::thread([&]() {
                        boost::this_thread::sleep(boost::posix_time::seconds(timeout));
                        solver.interrupt();
                    });
                    solver.clearInterrupt();
                    solved = solver.solve();
                    th.interrupt();
                } else {
                    solved = solver.solve();
                }

                if (solved) {
                    start.clear();
                    for (int i = 0; i < vars.size(); i++) {
                        if (solver.model[vars[i]] == g3l_False)
                            start.push_back(i);
                    }
                    if (!filename.empty())
                        storeClique(start, g, filename);

                    cout << "Found clique of size " << start.size() << endl;
                    solver.addClause(Glucose30::mkLit(rhs->at(vars.size() - 1 - start.size()).x / 2, true));
                }
            }
        }
    };
}
#endif //CPP_CLIQUE_H
