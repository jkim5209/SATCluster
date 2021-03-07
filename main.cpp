//
//  main.cpp
//  SATCluster
//
//  Created by Jaeyoon Kim on 2/4/21.
//  Copyright © 2021 Jaeyoon Kim. All rights reserved.
//
//
// Note variables indexed from 1. n is normal, -n in negation
#include "preprocessing.h"
#define NDEBUG

#include <random>
#include <queue>
#include <algorithm>
#include <iostream>
#include <vector>
#include <map>
#include <utility>
#include <fstream>
#include <sstream>
#include <string>
#include <cassert>
#include <unordered_map>
#include <map>
#include <set>
#include <stdlib.h>
#include <math.h>
#include <filesystem>
#include <chrono>

using namespace std;
using namespace std::chrono;

constexpr int MAX_CLUSTER = 20;



set<int> get_dependent_clauses(const set<int>& group, const vtc_T& var_to_clauses) {
    set<int> dependent_clauses;
    for (int var : group) {
        try {
            for (int clause_num: var_to_clauses.at(abs(var))) {
                dependent_clauses.insert(clause_num);
            }
        } catch (...) {
            cout << "caught exception\n";
        }
    }

    return dependent_clauses;
}

set<int> get_dependent_clauses(const map<int,int>& group, const vtc_T& var_to_clauses) {
    set<int> dependent_clauses;
    for (auto p : group) {
        int var = p.first;
        try {
            for (int clause_num: var_to_clauses.at(abs(var))) {
                dependent_clauses.insert(clause_num);
            }
        } catch (...) {
            cout << "caught exception\n";
        }
    }

    return dependent_clauses;
}

struct ImplicationData {
    vector<int> pos;
    vector<bool> vals;
    bool implAss;
};

vector<ImplicationData> get_implications(int var, map<int, int> group, const vtc_T& var_to_clauses, const vector<vector<int>>& clause_list) {
    vector<ImplicationData> impl_list;
    for (int clause_num : var_to_clauses.at(var)) {
        ImplicationData id;
        bool all_in = true;
        for (int clause_var : clause_list[clause_num]) {
            if (abs(clause_var) == var) {
                id.implAss = (clause_var > 0);
                continue;
            } 
            auto it = group.find(abs(clause_var));
            if (it != group.end()) {
                id.pos.push_back(it->second);
                id.vals.push_back(clause_var > 0);
            } else {
                all_in = false;
                break;
            }
        }
        if (all_in) impl_list.push_back(id);
    }

    return impl_list;
}


// Checks if other clauses implies this clause
bool check_clause_necessary(int checking_clause_num, const vtc_T& var_to_clauses, const vector<vector<int>>& clause_list) {
    map<int, bool> ass;
    map<int, bool> implications;
    queue<int> unprocessed_implications;

    for (int var : clause_list[checking_clause_num]) {
        ass[abs(var)] = (var < 0); // assign opposite to make clause false
        unprocessed_implications.push(abs(var));
    }

    while (!unprocessed_implications.empty()) {
        int var_to_process = unprocessed_implications.front();
        assert(var_to_process > 0);
        unprocessed_implications.pop();

        for (int clause_num : var_to_clauses.at(var_to_process)) {
            if (clause_num == checking_clause_num) continue;
            int implication_var = 0;
            bool clause_sat = false;
            for (int clause_var : clause_list[clause_num]) {
                auto it = ass.find(abs(clause_var));
                if (it != ass.end()) {
                    if (it->second == (clause_var > 0)) {
                        clause_sat = true;
                        break;
                    }
                }

                auto impl_it = implications.find(abs(clause_var));
                if (impl_it != implications.end()) {
                    if (impl_it->second == (clause_var > 0)) {
                        clause_sat = true;
                        break;
                    }
                }

                if (it == ass.end() && impl_it == implications.end()) {
                    if (implication_var != 0) {
                        // there are at least two variables that we didn't account for
                        clause_sat = true;
                        break;
                    }
                    implication_var = clause_var;
                }
            }

            if (clause_sat) continue;
            if (implication_var == 0) return false;
            //implications.emplace(abs(implication_var), ImplicationTracker({implication_counter, abs(implication_var), (implication_var > 0)}));
            implications.emplace(abs(implication_var), implication_var > 0);
            unprocessed_implications.push(abs(implication_var));
        }
    }
    return true;
}

struct VarDeps {
    bool hasDefault = false;
    bool hasNeg = false;
};

// Removes implications (only one variable in clause)
// TODO check if all clauses only depends on x_n or not x_n
vector<vector<int>> remove_implications(vector<vector<int>>&& clause_list) {
    set<int> implications;
    for (auto clause : clause_list) {
        if (clause.size() == 1) {
            int var_to_insert = clause.front();
            if (implications.find(-var_to_insert) != implications.end()) {
                throw "UNSAT!";
            }
            implications.insert(var_to_insert);
        }
    }

    map<int, VarDeps> deps;
    for (auto clause : clause_list) {
        for (int var : clause) {
            if (var > 0) { 
                deps[var].hasDefault = true;
            } else {
                deps[-var].hasNeg = true;
            }
        }
    }

    for (auto p : deps) {
        if (p.second.hasDefault && !p.second.hasNeg) {
            implications.insert(p.first);
        }
        else if (!p.second.hasDefault && p.second.hasNeg) {
            implications.insert(-p.first);
        }
    }

    cout << "num implications " << implications.size() << "\n";
    if (implications.size() == 0) {
        return clause_list;
    }

    vector<vector<int>> new_clause_list;
    for (auto clause : clause_list) {
        set<int> new_clause(clause.begin(), clause.end());
        bool clause_sat = false;
        for (int var : clause) {
            if (implications.find(var) != implications.end()) {
                clause_sat = true;
                break;
            }

            if (implications.find(-var) != implications.end()) {
                new_clause.erase(var);
            }
        }

        if (!clause_sat) {
            new_clause_list.emplace_back(new_clause.begin(), new_clause.end());
        }
    }

    return remove_implications(move(new_clause_list));
}

// depth starts at num vars
void helper(int depth, vector<bool>& curr, vector<vector<bool>>& valids, const vector<vector<int>>& int_clauses) {
    for (auto clause : int_clauses) {
        bool clause_sat = false;
        for (int var : clause) {
            if (abs(var) > curr.size()) {
                clause_sat = true;
                break;
            }
            if (var > 0) {
                if (curr[var - 1]) {
                    clause_sat = true;
                    break;
                }
            } else {
                if (!curr[-var - 1]) {
                    clause_sat = true;
                    break;
                }
            }

        }
        if (!clause_sat) {
            return;
        }
    }

    if (depth == 0) {
        valids.push_back(curr);
        return;
    }

    curr.push_back(true);
    helper(depth - 1, curr, valids, int_clauses);
    curr.pop_back();

    curr.push_back(false);
    helper(depth - 1, curr, valids, int_clauses);
    curr.pop_back();
}

void compute_sat(const vector<int>& vars, const vector<vector<int>>& clauses) {
    map<int, int> var_new_mapping;
    for (int i = 0; i < vars.size(); ++i) {
        var_new_mapping[vars[i]] = i + 1;
    }
    vector<vector<int>> remapped_int_clauses;
    vector<vector<int>> remapped_ext_clauses;

    for (auto clause : clauses) {
        vector<int> new_clause;
        bool hasExternal = false;
        for (int var : clause) {
            auto it = var_new_mapping.find(abs(var));
            if (it == var_new_mapping.end()) {
                hasExternal = true;
                continue;
            }

            if (var > 0) {
                new_clause.push_back(it->second);
            } else {
                new_clause.push_back(-it->second);
            }
        }
        if (hasExternal) {
            remapped_ext_clauses.emplace_back(move(new_clause));
        } else {
            remapped_int_clauses.emplace_back(move(new_clause));
        }
    }

    vector<bool> curr;
    vector<vector<bool>> valids;
    helper(vars.size(), curr, valids, remapped_int_clauses);
    cout << "num valids" << valids.size() << endl;
    for (auto valid : valids) {
        assert(valid.size() == vars.size());
    }

    vector<vector<int>> sat_ext_list;
    for (auto valid : valids) {
        vector<int> sat_ext;
        for (int i = 0; i < remapped_ext_clauses.size(); ++i) {
            for (int var : remapped_ext_clauses[i]) {
                if (var > 0) {
                    if (valid[var - 1]) {
                        sat_ext.push_back(i);
                        break;
                    }
                } else {
                    if (!valid[-var - 1]) {
                        sat_ext.push_back(i);
                        break;
                    }
                }
            }
        }

        bool isSubset = false;
        for (auto v : sat_ext_list) {
            if (includes(v.begin(), v.end(), sat_ext.begin(), sat_ext.end())) {
                isSubset = true;

                //cout << "=================\n";

                //for (int var : sat_ext) {
                //    cout << var << " ";
                //}
                //cout << "\n";

                //for (int var : v) {
                //    cout << var << " ";
                //}
                //cout << "\n";
                //cout << "=================\n";
                
                break;
            }
        }

        if (!isSubset) {
            sat_ext_list.emplace_back(move(sat_ext));
        }
    }

    int num_no_subset = 0;
    for (int i = 0; i < sat_ext_list.size(); ++i) {
        bool is_subset = true;
        for (int j = 0; j < sat_ext_list.size(); ++j) {
            if (i == j) continue;
            // check check if i subset of j
            if (includes(sat_ext_list[i].begin(), sat_ext_list[i].end(), sat_ext_list[j].begin(), sat_ext_list[j].end())) {
                if (sat_ext_list[i].size() == sat_ext_list[j].size()) {
                    if (i < j) continue;
                }
                is_subset = false;
                break;
            }
        }
        if (is_subset) {
            num_no_subset += 1;
        }
    }


    cout << "num valids" << valids.size() << " num relavent " << num_no_subset << endl;
}

void save_simplified_dependencies(string filename, vector<vector<int>> clause_list) {
    map<int,int> old_var_to_new;
    int counter = 1;
    for (const auto& clause : clause_list) {
        for (int var : clause) {
            if (old_var_to_new.find(abs(var)) == old_var_to_new.end()) {
                old_var_to_new[abs(var)] = counter;
                counter += 1;
            }
        }
    }

    ofstream of(filename);
    of << clause_list.size() << " " << old_var_to_new.size() << "\n";
    for (const auto& clause : clause_list) {
        for (int var : clause) {
            of << old_var_to_new[abs(var)] << " ";
        }
        of << "\n";
    }
}

vector<set<int>> find_connected_components(const vector<vector<int>>& clause_list) {
    vtc_T var_to_clauses;
    
    for (int i = 0; i < clause_list.size(); ++i) {
        for (auto var : clause_list[i]) {
            var_to_clauses[abs(var)].push_back(i);
        }
    }
    int counter = 0;

    vector<set<int>> components;

    while (!var_to_clauses.empty()) {
        set<int> component;
        queue<int> to_add;
        to_add.push(var_to_clauses.begin()->first);
        while (!to_add.empty()) {
            int var = to_add.front();
            to_add.pop();
            component.insert(var);
            auto it = var_to_clauses.find(var);
            if (it == var_to_clauses.end()) continue;

            for (int clause_idx : it->second) {
                for (int var : clause_list[clause_idx]) {
                    var = abs(var);
                    if (component.find(var) != component.end()) continue;

                    to_add.push(var);
                }
            }
            var_to_clauses.erase(it);
        }

        //cout << "component " << counter++ << " size " << component.size() << "\n";
        components.emplace_back(component);
    }

    return components;
}

int find_start_var(const vtc_T& var_to_clauses, const set<int>& used) {
    int min_num_clauses = var_to_clauses.size();
    int start_var;
    for (auto p : var_to_clauses) {
        if (used.find(p.first) != used.end()) continue;
        int num_new_clause = p.second.size();
        if (num_new_clause < min_num_clauses) {
            min_num_clauses = num_new_clause;
            start_var = p.first;
        }
    }
    return start_var;
}

// vars in group, clauses in group, clauses dependent on group
// When adding, add var to group, for clauses that has var, check if is now covered by group, and how many are added
// for each var keep track of clauses they are in

int main(int argc, const char * argv[]) {
    assert(argc == 3);
    int max_num_ass = atoi(argv[2]);
    int n_vars, n_clauses;
    auto clause_list = read_sat(argv[1], n_vars, n_clauses);
    clause_list = remove_implications(move(clause_list));
    n_clauses = clause_list.size();

    auto components = find_connected_components(clause_list);
    int max_size = 0;
    int max_idx;
    for (int i = 0; i < components.size(); ++i) {
        if (components[i].size() > max_size) {
            max_idx = i;
            max_size = components[i].size();
        }
    }

    set<int> max_component = components[max_idx];
    cout << "using component of size " << max_component.size() << "\n";

    //string filename = filesystem::path(argv[1]).filename();
    //save_simplified_dependencies("partition/" + filename, clause_list);
    //
    for (auto clause : clause_list) {
        int counter = 0;
        for (int var : clause) {
            if (max_component.find(abs(var)) != max_component.end()) {
                ++counter;
            }
        }
        assert(counter == clause.size() || counter == 0);
    }

    // Do clustering just on largest component
    vtc_T var_to_clauses;
    
    for (int i = 0; i < n_clauses; ++i) {
        for (auto var : clause_list[i]) {
            if (max_component.find(abs(var)) != max_component.end()) {
                var_to_clauses[abs(var)].push_back(i);
            }
        }
    }

    double total = 0;
    for (auto& p : var_to_clauses) {
        total += p.second.size();
    }
    cout << "avg var to clauses: " << total / var_to_clauses.size() << endl;

    for (auto var : max_component) {
        assert(var_to_clauses.find(var) != var_to_clauses.end());
    }

    for (auto p : var_to_clauses) {
        assert(max_component.find(p.first) != max_component.end());
    }

    //double num_unnecessary = 0;
    //int counter = 0;
    //for (int i = 0; i < clause_list.size(); ++i) {
    //    if (clause_list[i].size() <= 3) continue;
    //    ++counter;
    //    
    //    if (!check_clause_necessary(i, var_to_clauses, clause_list)) {
    //        ++num_unnecessary;
    //    }
    //    cout << "unnecessary clause size " << clause_list[i].size() << " ratio " << num_unnecessary / counter << "\n";
    //}

    set<int> used;
    while (true) {
        int start_var = find_start_var(var_to_clauses, used);
        auto start = high_resolution_clock::now(); 
        auto group = get_cluster(start_var, var_to_clauses, clause_list, max_num_ass, used);
        auto end = high_resolution_clock::now(); 
        cout << "time" << duration_cast<seconds>(end - start).count() << endl;
        for (auto p : group) {
            //var_to_clauses.erase(var);
            used.insert(p.first);
        }
        cout << "used size " << used.size() << "\n";
    }

    return 0;
}

