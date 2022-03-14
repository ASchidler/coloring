#include <iostream>
#include <string>

#include "geometric.h"
#include "heuristics.h"
#include "clique.h"
#include <experimental/filesystem>
#include "sat_encode.h"
#include "sat_encode2.h"
#include "sat_search.h"
#include <thread>
#include <mutex>
#include "reducer.h"
#include "graph_generator.h"

using namespace std;
namespace efilesystem = std::experimental::filesystem;

enum CliqueComputation {
    greedy1,
    greedy2,
    sat
};

int convert_to_int(char* argv[], int argc, int& idx) {
    string name = string(argv[idx]);

    if (argc <= idx + 1) {
        cerr << name << " requires a number";
        exit(1);
    }

    try {
        auto conv_result = stoi(argv[idx + 1]);
        if (conv_result < 0) {
            cerr << name << " cannot be negative" << endl;
            exit(1);
        }
        idx++;
        return conv_result;
    }
    catch (invalid_argument const &e) {
        cerr << "Invalid number entered for " << name << " " << argv[idx + 1] << endl;
        exit(1);
    }
    catch (std::out_of_range const &e) {
        cerr << "Invalid number entered for "<< name << " " << argv[idx + 1] << endl;
        exit(1);
    }
}

int main(int argc, char* argv[]) {
    auto filename = string(argv[argc-1]);
    auto slashpos = filename.rfind('/');
    auto secondslash = filename.rfind('/', slashpos-1);
    string instance_name = filename.substr(slashpos+1);
    instance_name = instance_name.substr(0, instance_name.rfind('.'));
    string file_ending = filename.substr(filename.rfind('.')+1);
    string folder_name = filename.substr(secondslash+1, slashpos-secondslash-1);
    string base_path = filename.substr(0, filename.rfind('/', filename.rfind('/')-1)+1);
    string random_name = "";
    bool generate = false;
    node_t random_nodes = 0;
    unsigned short random_prob = 0;

    string convert_path = "";
    bool use_local_search = false;
    bool use_sat_local_search1 = false;
    bool use_sat_local_search2 = false;
    bool use_flexible_sat_search = true;
    bool use_local_search_result = false;
    bool use_cadical = true;
    bool continue_result = false;
    bool vary_parameters = false;
    node_t total_nodes_per_initial = 4;
    unsigned int pre_iterations = 0;
    unsigned int iteration_limit = 1000;
    node_t branching = 2;
    int threadCount = 1;
    node_t path_trace_limit = 2;

    string marker = "";

    // Configure
    bool use_sat_encoding = false;
    node_t seed = 0;
    uint timeout = 5;

    bool compute_cliques = false;
    CliqueComputation clique_method = greedy2;
    bool compute_myciel = true;

    // Parse arguments
    for (int i = 1; i < argc-1; ++i) {
        string arg = string(argv[i]);
        if (arg == "-e") {
            use_sat_encoding = true;
        } else if (arg == "-f") {
            use_flexible_sat_search = !use_flexible_sat_search;
        } else if (arg == "-s0") {
            use_local_search = !use_local_search;
        } else if (arg == "-s1") {
            use_sat_local_search1 = !use_sat_local_search1;
        } else if (arg == "-s2") {
            use_sat_local_search2 = !use_sat_local_search2;
        } else if (arg == "-q") {
            compute_cliques = !compute_cliques;
        } else if (arg == "-l") {
            use_local_search_result = !use_local_search_result;
        } else if (arg == "-n") {
            continue_result = !continue_result;
        } else if (arg == "-a") {
            use_cadical = !use_cadical;
        } else if (arg == "-v") {
            vary_parameters = !vary_parameters;
        } else if (arg == "-w") {
            path_trace_limit = convert_to_int(argv, argc, i);
        } else if (arg == "-s") {
            seed = convert_to_int(argv, argc, i);
        } else if (arg == "-t") {
            timeout = convert_to_int(argv, argc, i);
        } else if (arg == "-r") {
            total_nodes_per_initial = convert_to_int(argv, argc, i);
        } else if (arg == "-d") {
            threadCount = convert_to_int(argv, argc, i);
        } else if (arg == "-b") {
            branching = convert_to_int(argv, argc, i);
        } else if (arg == "-p") {
            pre_iterations = convert_to_int(argv, argc, i);
        } else if (arg == "-i") {
            iteration_limit = convert_to_int(argv, argc, i);
        } else if (arg == "-c") {
            if (argc <= i + 1) {
                cerr << "-c requires a path";
                return 1;
            }
            convert_path = string(argv[i + 1]);
            if (string(convert_path.substr(convert_path.rfind('.') + 1)) != "bz2") {
                cerr << "-c path should end with .bz2";
                return 1;
            }
            i++;
        } else if (arg == "-m") {
            marker = string(argv[i + 1]);
            i++;
        } else if (arg == "-g") {
            if (argc <= i + 1) {
                cerr << "-g requires parameters name:nodes:probability";
                return 1;
            }

            generate = true;
            istringstream iss(argv[i + 1]);
            string tok;

            for (long j = 0; getline(iss, tok, ':'); j++) {
                if (j == 0)
                    random_name = tok;
                else if (j == 1)
                    random_nodes = stoul(tok);
                else if (j == 2)
                    random_prob = stoul(tok);
            }
            i++;
        }
    }

    if (generate) {
        planarity::generate_random(random_nodes, random_prob, random_name, base_path);
        //planarity::generate_ba(random_nodes, random_nodes * random_prob / 100, random_name, base_path);
        exit(0);
    }

    for(auto ca=0; ca < argc; ca++) {
        if (ca > 0)
            cout << " ";
        cout << argv[ca];
    }
    cout << endl;
    cout << instance_name << endl;

    string result_modifier = "";

    stringstream args;

    args << ".p" << pre_iterations << ".b" << branching << ".r" << total_nodes_per_initial << ".d" << threadCount << ".t" << timeout << ".w" << path_trace_limit << (path_trace_limit > 0 ? "x" : "") << ".i"<<iteration_limit;

    if (use_local_search_result)
        args << ".l";
    if (use_flexible_sat_search)
        args << ".f";
    if (use_cadical)
        args << ".a";
    if (vary_parameters)
        args << ".v";
    if (! marker.empty())
        args << "." << marker;
    auto arg = args.str();

    string clique_path = base_path + "benchmark-results/" + instance_name + ".clique";
    string color_path = base_path + "benchmark-results/" + instance_name + ".ds.color";
    string sls1_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + arg + ".s1.color";
    string sls2_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + arg + ".s2.color";
    string ls_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + (marker.empty() ? marker : "."+marker) + ".ls.color";
    string enc_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + ".en.color";

    string stats_path = base_path + "benchmark-results/" + instance_name + ".stats";
    string myciel_path = base_path + "benchmark-results/" + instance_name + ".myciel";

    bool color_exists = efilesystem::exists(color_path);
    if (color_exists) {
        cout << "Color exists" << endl;
    }

    if (continue_result) {
        if (use_local_search) {
            color_path = ls_color_path;
            ls_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + ".n.ls.color";
        } else if (use_sat_encoding) {
            color_path = enc_color_path;
            enc_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + ".n.en.color";
        } else if (use_sat_local_search1) {
            color_path = sls1_color_path;
            sls1_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + arg + ".n.s1.color";
        } else if (use_sat_local_search2) {
            color_path = sls2_color_path;
            sls2_color_path = base_path + "benchmark-results/" + result_modifier + instance_name + arg + ".n.s2.color";
        }
    }

    planarity::ConflictGraph g = [&]() -> planarity::ConflictGraph {
        if (file_ending == "bz2") {
            return planarity::ConflictGraph::parse(filename);
        } else {
            auto instance = planarity::parse(filename);
            return planarity::createConflictGraph(instance);
        }
    }();

    if (!convert_path.empty()) {
        g.store(convert_path);
        exit(0);
    }

    std::cout << g.getNumNodes() << " nodes, " << g.numEdges << " edges"  << std::endl;
    if (!efilesystem::exists(stats_path)) {
        ofstream myfile(stats_path);
        if (myfile.is_open()) {
            myfile << g.getNumNodes() << " " << g.numEdges << std::endl;
            myfile.close();
        }
    }

    if (use_local_search_result)
        color_path = ls_color_path;

    auto result = color_exists ? planarity::Coloring::parse(color_path, g.getNumNodes()) : planarity::dsatur(g);
    //assert(g.verify(result.coloring));

    if (! color_exists)
        result.store(color_path, g);

    if (!g.verify(result.coloring)) {
        result = planarity::dsatur(g);
        result.store(color_path, g);
    }

    std::cout << result.numColors << " Colors" << std::endl;

    auto clique = efilesystem::exists(clique_path) ? planarity::Clique::importClique(clique_path) : vector<node_t>();
    if (!clique.empty())
        cout << "Clique of size "<< clique.size() << " exists" << endl;

    node_t myciel_lb = 0;
    if (efilesystem::exists(myciel_path)) {
        auto myciel = planarity::Myciel::import(myciel_path, g);
        cout << "Loaded Myciel with bound " << myciel.bound << endl;
        myciel_lb = myciel.bound;
    }

    if (compute_cliques) {
        if (clique_method == greedy1)
            planarity::Clique::findCliqueGreedy(g, clique, clique.size(), myciel_lb, compute_myciel, clique_path, myciel_path, false);
        else if (clique_method == greedy2) {
            planarity::Clique::findCliqueGreedy2(g, clique, clique.size(), myciel_lb, compute_myciel, clique_path,
                                                 myciel_path, true);
            planarity::Clique::findCliqueGreedy(g, clique, clique.size(), myciel_lb, compute_myciel, clique_path, myciel_path, false);
        }
        else if (clique_method == sat) {
            if (g.getNumNodes() < 15000)
                planarity::Clique::findCliqueSat(g, clique, clique_path, 0);
            else
                planarity::Clique::findCliqueSatPartial(g, clique, clique_path, 600);
        }
    }

    if (! efilesystem::exists(myciel_path) && !clique.empty()) {
        auto myciel = planarity::Myciel(g, clique);
        cout << "Computed Myciel with lb " << myciel.bound << endl;
        myciel_lb = myciel.bound;
        myciel.store(g, myciel_path);
    }

    if (use_sat_encoding) {
        if (use_cadical)
            planarity::SatEncodeCadical::encode_full(g, clique, result.numColors-1, 0, color_path);
        else
            planarity::SatEncode::encode_full(g, clique, result.numColors - 1, 0, enc_color_path);
    }

    if (use_local_search) {
        std::mutex tabu_mutex;
        unsigned int c_cycle = 0;
        vector<std::thread> threads;

        auto f = [&](unsigned int tid) {
            planarity::tabuSearch(g, result, result.numColors, tabu_mutex, c_cycle, ls_color_path, seed + tid);
        };

        for (int i = 0; i < threadCount; i++) {
            threads.emplace_back(f, i);
        }

        for (auto &th: threads)
            th.join();
    }

    if (use_sat_local_search1 || use_sat_local_search2) {
        //planarity::tabuSearchLookahead(g, result, result.numColors, ls_color_path, 10000, 10, 4000, INVALID_COLOR, 5u, 5);

        std::mutex tabu_mutex;
        unsigned int c_cycle = 0;
        vector<std::thread> threads;
        threads.reserve(threadCount);
        dynamic_bitset<> seed_sync(result.numColors);
        seed_sync.flip();

        auto f = [&](unsigned int tid) {
            if (use_sat_local_search1)
                planarity::tabuSearchSat(g, result, result.numColors, tabu_mutex, c_cycle, sls1_color_path, seed + tid,
                                         iteration_limit * 3, 10,
                                         1000, INVALID_COLOR,
                                         timeout,
                                         branching,
                                         300 / total_nodes_per_initial,
                                         300,
                                         50 / total_nodes_per_initial,
                                         50, false, use_flexible_sat_search, use_cadical);
            else {
                auto c_pre_iterations = pre_iterations;
                auto c_use_cadical = use_cadical;
                auto c_use_flexible = use_flexible_sat_search;
                auto c_branching = branching;
                auto c_initial_node = 300 / total_nodes_per_initial;
                auto c_iterations = iteration_limit;
                auto c_timeout = timeout;

                if (vary_parameters) {
                    if (tid >= 2) {
                        c_timeout = 5;
                    } else {
                        c_timeout = 10;
                    }

                    if (tid <= 1) {
                        c_iterations = 5000;
                    } else if (tid <= 3) {
                        c_iterations = 1000;
                    } else {
                        c_iterations = 500;
                    }

                    if (tid == 1) {
                        c_pre_iterations = 100000;
                    } else {
                        c_pre_iterations = 0;
                    }

                    c_use_flexible = tid % 2 == 1;
                    c_use_cadical = (tid == 0 || tid == 4);
                    c_branching = (tid <= 1 ? 5 : 2);
                }
                if (vary_parameters) {
                    seed_sync = dynamic_bitset<>(result.numColors);
                    seed_sync.flip();
                }
                planarity::tabuSearchSat2(g, result, result.numColors, tabu_mutex, c_cycle, seed_sync, sls2_color_path,
                                          seed + tid,
                                          c_iterations, 5,
                                          100, INVALID_COLOR,
                                          c_timeout,
                                          c_branching,
                                          c_initial_node,
                                          300,
                                          0,
                                          60, false, c_use_flexible, false, c_pre_iterations, c_use_cadical,
                                          path_trace_limit, !vary_parameters);
            }
        };

        for (int i = 0; i < threadCount; i++) {
            threads.emplace_back(f, i);
        }

        for (auto &th: threads)
            th.join();
    }

    std::cout << result.numColors << " Colors" << std::endl;

    return 0;
}
