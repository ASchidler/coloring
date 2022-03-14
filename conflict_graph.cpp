//
// Created on 22.10.21.
//

#include "conflict_graph.h"
#include "solution.h"

void planarity::find_color_subgraph(const ConflictGraph& g, Coloring& coloring, const string& filename) {
    vector<dynamic_bitset<>> partitions(coloring.numColors, dynamic_bitset<>(g.getNumNodes()));

    dynamic_bitset<> component(g.getNumNodes());
    dynamic_bitset<> new_nodes(g.getNumNodes());

    auto findNeighbor = [&] (node_t node, color_t color) {
        new_nodes.reset();
        dynamic_bitset<> node_colors(color);

        for (auto n2=g.adjacency[node].find_first(); n2 != dynamic_bitset<>::npos; n2 = g.adjacency[node].find_next(n2)) {
            if (coloring.coloring[n2] < color) {
                if (!node_colors.test(coloring.coloring[n2])) {
                    node_colors[coloring.coloring[n2]] = true;
                    new_nodes.set(n2);
                }
            }
        }

        if (node_colors.all()) {
            component.set(node);
            component |= new_nodes;
            return true;
        } else {
            node_colors.flip();
            auto new_c = node_colors.find_first();
            coloring.coloring[node] = new_c;
            partitions[color][node] = false;
            partitions[new_c][node] = true;
            cout << "Skip " << color << endl;
        }
        return false;
    };

    for (node_t n=0; n < g.getNumNodes(); n++) {
        partitions[coloring.coloring[n]].set(n);
    }

    bool done = false;
    for (node_t n=0; n < g.getNumNodes() && ! done; n++) {
        if (coloring.coloring[n] == coloring.numColors - 1) {
            component.reset();
            color_t cc = coloring.numColors - 1;
            if (findNeighbor(n, cc)) {
                node_t c_n = n;
                while (cc > 0) {
                    cc--;
                    auto modified_nb = g.adjacency[c_n] & partitions[cc];
                    auto modified_nb1 = modified_nb & component;
                    auto modified_nb2 = modified_nb - component;
                    bool found_nb = false;
                    for (auto n2 = modified_nb1.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb1.find_next(n2)) {
                        if (findNeighbor(n2, cc)) {
                            c_n = n2;
                            found_nb = true;
                            break;
                        }
                    }
                    if (! found_nb) {
                        for (auto n2 = modified_nb2.find_first(); n2 != dynamic_bitset<>::npos; n2 = modified_nb2.find_next(n2)) {
                            if (findNeighbor(n2, cc)) {
                                c_n = n2;
                                found_nb = true;

                                break;
                            }
                        }
                        if (! found_nb)
                            break;
                    }
                }

                done = cc == 0;
            }
        }
    }
    if (! done)
        cout << "Failed" << endl;
    assert(g.verify(coloring.coloring));
    cout << component.count() << " Nodes" << endl;

    if (!filename.empty()) {
        ofstream myfile(filename);
        if (myfile.is_open()) {
            auto n = component.find_first();
            myfile << n;
            for (; n != dynamic_bitset<>::npos; n = component.find_next(n)) {
                myfile << "," << n;
            }
            myfile << endl;
            myfile.close();
        }
    }
}
