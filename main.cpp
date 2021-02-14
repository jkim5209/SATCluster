//
//  main.cpp
//  SATCluster
//
//  Created by Jaeyoon Kim on 2/4/21.
//  Copyright © 2021 Jaeyoon Kim. All rights reserved.
//
//
// Note variables indexed from 1. n is normal, -n in negation
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

using namespace std;

constexpr int MAX_CLUSTER = 20;

vector<vector<int>> read_sat(string filename, int& n_vars, int& n_clauses) {
    ifstream fin(filename);
    if (!fin.is_open()) {
        throw "failed to open file";
    }

    string line;

    do {
        getline(fin, line);
    } while(line[0] == 'c');

    stringstream ss(line);
    char p;
    string cnf;
    ss >> p >> cnf >> n_vars >> n_clauses;
    assert(p == 'p');
    assert(cnf == "cnf");

    cout << n_vars << " " << n_clauses << endl;

    vector<vector<int>> clause_list;

    int var;
    set<int> clause;
    bool should_add = true;
    while (fin >> var) {
        if (var == 0) {
            if (should_add) {
                clause_list.emplace_back(clause.begin(), clause.end());
            }
            clause.clear();
            should_add = true;
        } else {
            if (clause.find(-var) != clause.end()) should_add = false;
            clause.insert(var);
        }
    }

    return clause_list;
}


set<int> get_dependent_clauses(const set<int>& group, const unordered_map<int, vector<int>>& var_to_clauses) {
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

set<int> get_dependent_clauses(const map<int,int>& group, const unordered_map<int, vector<int>>& var_to_clauses) {
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

// num fully in group, num part in group
pair<int, int> num_clauses(const set<int>& group, const set<int>& dependent_clauses, const vector<vector<int>>& clause_list) {

    int num_full_in = 0;
    int num_part_in = 0;

    for (int clause_num : dependent_clauses) {
        bool full_in = true;
        for (int var : clause_list[clause_num]) {
            if (group.find(abs(var)) == group.end()) {
                full_in = false;
                break;
            }
        }

        if (full_in) num_full_in += 1;
        else num_part_in += 1;
    }

    return make_pair(num_full_in, num_part_in);
}

struct AddInfo {
    int var;
    int clause_out;
    int clause_in;
};

AddInfo find_best_to_add(const set<int>& group, const unordered_map<int, vector<int>>& var_to_clauses, const vector<vector<int>>& clause_list) {
    int best_score = clause_list.size();
    int best_num_in = 0;
    int best_var = 0;

    set<int> dependent_clauses = get_dependent_clauses(group, var_to_clauses);
    set<int> dependent_vars;
    for (int clause_num : dependent_clauses) {
        for (int var : clause_list[clause_num]) {
            if (group.find(abs(var)) != group.end()) {
                //cout << var << " already in group\n";
                continue;
            }
            if (var_to_clauses.find(abs(var)) == var_to_clauses.end()) {
                //cout << var << " not in var to clauses\n";
                continue;
            }
            dependent_vars.insert(abs(var));
        }
    }

    cout << "dep clauses " << dependent_clauses.size() << " dep vars " << dependent_vars.size() << "\n";

    // TODO replace dependent vars with everything?
    for (auto var : dependent_vars) {
        //int var = p.first;
        if (group.find(var) != group.end()) continue;

        set<int> test_group = group;
        test_group.insert(var);
        set<int> test_dependent_clauses = get_dependent_clauses(test_group, var_to_clauses);
        auto score = num_clauses(test_group, test_dependent_clauses, clause_list);

        if (score.second < best_score) {
            best_score = score.second;
            best_num_in = score.first;
            best_var = var;
        }
    }

    AddInfo ai;
    ai.var = best_var;
    ai.clause_out = best_score;
    ai.clause_in = best_num_in;

    return ai;
}

struct ScoreObj {
    int num0 = 0;
    int num1 = 0;
    int num2 = 0;

    bool operator<(const ScoreObj& rhs) {
        if (num0 < rhs.num0) {
            return true;
        }
        if (num0 > rhs.num0) {
            return false;
        }

        if (num1 < rhs.num1) {
            return true;
        }
        if (num1 > rhs.num1) {
            return false;
        }

        if (num2 < rhs.num2) {
            return true;
        }
        if (num2 > rhs.num2) {
            return false;
        }

        return false;
    }
};

struct ImplicationData {
    vector<int> pos;
    vector<bool> vals;
    bool implAss;
};

vector<ImplicationData> get_implications(int var, map<int, int> group, const unordered_map<int, vector<int>>& var_to_clauses, const vector<vector<int>>& clause_list) {
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

// checks for possible assignment
// returns (can_be_true, can_be_false)
pair<bool, bool> poss_assign(const vector<bool>& ass, vector<ImplicationData> impls) {
    bool can_be_true = true;
    bool can_be_false = true;
    for (const auto& impl : impls) {
        bool impl_active = true;
        for (size_t i = 0; i < impl.pos.size(); ++i) {
            if (ass.at(impl.pos[i]) == impl.vals[i]) {
                impl_active = false;
                break;
            }
        }

        if (!impl_active) continue;

        if (impl.implAss) {
            can_be_false = false;
        } else {
            can_be_true = false;
        }
    }
    return make_pair(can_be_true, can_be_false);
}

class Assignment {
public:
    Assignment(const map<int, int>& group_, const unordered_map<int, vector<int>>& var_to_clauses_, const vector<vector<int>>& clause_list_) :
        group(group_), var_to_clauses(var_to_clauses_), clause_list(clause_list_) {};

    void add_implications(map<int, int>& implication_counter) const {
        for (auto p : implications) {
            ++implication_counter[abs(p.first)];
        }
    }

    // returns true if valid assignment false otherwise
    bool assign(int var, bool value) {
        assert(var > 0);
        assert(ass.find(var) == ass.end());

        auto it = implications.find(var);
        if (it != implications.end()) {
            if (it->second != value) return false;
            implications.erase(it);
        }
        ass[var] = value;
        queue<int> unprocessed_implications;
        unprocessed_implications.push(var);

        while (!unprocessed_implications.empty()) {
            int var_to_process = unprocessed_implications.front();
            assert(var_to_process > 0);
            unprocessed_implications.pop();

            for (int clause_num : var_to_clauses.at(var_to_process)) {
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
                implications[abs(implication_var)] = (implication_var > 0);
                unprocessed_implications.push(abs(implication_var));
            }
        }
        return true;
    }
private:
    map<int, bool> ass;
public:
    map<int, bool> implications;
    const map<int, int>& group;
    const unordered_map<int, vector<int>>& var_to_clauses;
    const vector<vector<int>>& clause_list;
}; 
void get_cluster2(int init_var, const unordered_map<int, vector<int>>& var_to_clauses, const vector<vector<int>>& clause_list) {
    int counter = 0;
    map<int, int> group;
    vector<int> vars;
    vars.push_back(init_var);
    group[init_var] = counter++;
    vector<Assignment> assignments;
    assignments.emplace_back(Assignment(group, var_to_clauses, clause_list));
    assignments.back().assign(init_var, true);
    assignments.emplace_back(Assignment(group, var_to_clauses, clause_list));
    assignments.back().assign(init_var, false);

    while (true) {
        map<int, int> implication_counter;
        for (const auto& ass : assignments) {
            //cout << "impl size" << ass.implications.size() << endl;
            ass.add_implications(implication_counter);
        }

        int max_counter = 0;
        int max_var = 0;
        for (auto p : implication_counter) {
            if (p.second > max_counter) {
                max_counter = p.second;
                max_var = p.first;
            }
        }
        assert(max_counter != 0);

        vector<Assignment> new_assignments;
        group[max_var] = counter++;
        for (auto& ass : assignments) {
            Assignment temp = ass;
            if (temp.assign(max_var, true)) {
                new_assignments.push_back(temp);
            }
            if (ass.assign(max_var, false)) {
                new_assignments.push_back(move(ass));
            }
        }

        assignments = move(new_assignments);
        cout << counter << " num ass " << assignments.size() << endl;
    }
}

void get_cluster(int init_var, const unordered_map<int, vector<int>>& var_to_clauses, const vector<vector<int>>& clause_list) {
    int counter = 0;
    map<int, int> group;
    vector<int> vars;
    vars.push_back(init_var);
    group[init_var] = counter++;
    vector<vector<bool>> satisfiable;
    satisfiable.emplace_back(vector<bool>({true}));
    satisfiable.emplace_back(vector<bool>({false}));

    while (true) {
        set<int> dependent_clauses = get_dependent_clauses(group, var_to_clauses);
        set<int> dependent_vars;
        for (int clause_num : dependent_clauses) {
            for (int var : clause_list[clause_num]) {
                if (group.find(abs(var)) != group.end()) {
                    continue;
                }
                if (var_to_clauses.find(abs(var)) == var_to_clauses.end()) {
                    continue;
                }
                dependent_vars.insert(abs(var));
            }
        }

        int best_var = 0;
        int min_num_satisfiable = 10000000; // TODO change
        vector<ImplicationData> best_impls;


        for (int var : dependent_vars) {
            auto impl_list = get_implications(var, group, var_to_clauses, clause_list);

            if (impl_list.empty()) continue;

            int num_sat = 0;
            for (const auto& ass : satisfiable) {
                auto p = poss_assign(ass, impl_list);
                if (p.first) ++num_sat;
                if (p.second) ++num_sat;
                if (num_sat >= min_num_satisfiable) break;
            }

            if (num_sat < min_num_satisfiable) {
                best_var = var;
                min_num_satisfiable = num_sat;
                best_impls = std::move(impl_list);
            }
        }

        assert(best_var != 0); // TODO have to check for case where no implications added

        cout << "size: " << group.size() + 1 << " new var: " << best_var << " num sat: " << min_num_satisfiable << " log2: " << log2(min_num_satisfiable) << endl;

        vector<vector<bool>> new_satisfiable;
        for (auto& ass : satisfiable) {
            auto p = poss_assign(ass, best_impls);
            if (p.first && p.second) {
                ass.push_back(true);
                new_satisfiable.push_back(ass);
                ass.back() = false;
                new_satisfiable.emplace_back(move(ass));
            } else if (p.first) {
                ass.push_back(true);
                new_satisfiable.emplace_back(move(ass));
            } else if (p.second) {
                ass.push_back(false);
                new_satisfiable.emplace_back(move(ass));
            }
        }
        satisfiable = move(new_satisfiable);
        group[best_var] = counter++;
    }
}

AddInfo find_best_to_add2(const set<int>& group, const unordered_map<int, vector<int>>& var_to_clauses, const vector<vector<int>>& clause_list) {
    set<int> dependent_clauses = get_dependent_clauses(group, var_to_clauses);
    set<int> dependent_vars;
    for (int clause_num : dependent_clauses) {
        for (int var : clause_list[clause_num]) {
            if (group.find(abs(var)) != group.end()) {
                //cout << var << " already in group\n";
                continue;
            }
            if (var_to_clauses.find(abs(var)) == var_to_clauses.end()) {
                //cout << var << " not in var to clauses\n";
                continue;
            }
            dependent_vars.insert(abs(var));
        }
    }

    ScoreObj best_score;

    int best_var = 0;

    for (int var : dependent_vars) {
        if (group.find(var) != group.end()) continue;

        set<int> test_group = group;
        test_group.insert(var);
        set<int> test_dependent_clauses = dependent_clauses;
        for (const int clause_num : var_to_clauses.at(abs(var))) {
            test_dependent_clauses.insert(clause_num);
        }

        ScoreObj so;

        for (int clause_num : test_dependent_clauses) {
            int num_out = 0;
            for (int clause_var : clause_list[clause_num]) {
                if (test_group.find(abs(clause_var)) == test_group.end()) {
                    ++num_out;
                }
            }

            switch (num_out) {
                case 0:
                    ++so.num0;
                    break;
                case 1:
                    ++so.num1;
                    break;
                case 2:
                    ++so.num2;
                    break;
                default:
                    break;
            }
        }

        if (best_score < so) {
            best_score = so;
            best_var = var;
            //cout << "new best var " << best_var << " " << so.num0 << " " << so.num1 << " " << so.num2 << "\n";
        }
    }

    AddInfo ai;
    ai.var = best_var;
    ai.clause_out = best_score.num1;
    ai.clause_in = best_score.num0;

    return ai;
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
    unordered_map<int, vector<int>> var_to_clauses;
    
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

// vars in group, clauses in group, clauses dependent on group
// When adding, add var to group, for clauses that has var, check if is now covered by group, and how many are added
// for each var keep track of clauses they are in

int main(int argc, const char * argv[]) {
    assert(argc == 3);
    int group_size = atoi(argv[2]);
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
    unordered_map<int, vector<int>> var_to_clauses;
    
    for (int i = 0; i < n_clauses; ++i) {
        for (auto var : clause_list[i]) {
            if (max_component.find(abs(var)) != max_component.end()) {
                var_to_clauses[abs(var)].push_back(i);
            }
        }
    }

    for (auto var : max_component) {
        assert(var_to_clauses.find(var) != var_to_clauses.end());
    }

    for (auto p : var_to_clauses) {
        assert(max_component.find(p.first) != max_component.end());
    }

    int min_num_clauses = var_to_clauses.size();
    int start_var;
    for (auto p : var_to_clauses) {
        int num_new_clause = p.second.size();
        if (num_new_clause < min_num_clauses) {
            min_num_clauses = num_new_clause;
            start_var = p.first;
            cout << "min " << num_new_clause << "\n";
        }
    }

    get_cluster(start_var, var_to_clauses, clause_list);
    return 0;
    set<int> group;
    group.insert(start_var);

    for (int i = 0; i < group_size; ++i) {
        auto ai = find_best_to_add2(group, var_to_clauses, clause_list);
        assert(max_component.find(abs(ai.var)) != max_component.end());
        group.insert(ai.var);
        cout << "report: " << group.size() << " " << ai.clause_out << " " << ai.clause_in << endl;
    }
    const vector<int> vars(group.begin(), group.end());
    set<int> dep_clause_idx = get_dependent_clauses(group, var_to_clauses);
    vector<vector<int>> dependent_clause_list;
    for (int idx : dep_clause_idx) {
        dependent_clause_list.push_back(clause_list[idx]);
    }

    compute_sat(vars, dependent_clause_list);

    return 0;
}

