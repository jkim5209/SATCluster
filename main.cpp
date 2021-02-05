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
#include <iostream>
#include <vector>
#include <map>
#include <utility>
#include <fstream>
#include <sstream>
#include <string>
#include <cassert>
#include <unordered_map>
#include <set>

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
    vector<int> clause;
    while (fin >> var) {
        if (var == 0) {
            clause_list.push_back(clause);
            clause.clear();
        } else {
            clause.push_back(var);
        }
    }

    return clause_list;
}

set<int> get_dependent_clauses(const set<int>& group, const unordered_map<int, vector<int>>& var_to_clauses) {
    set<int> dependent_clauses;
    for (int var : group) {
        for (int clause_num: var_to_clauses.at(abs(var))) {
            dependent_clauses.insert(clause_num);
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
            if (group.find(var) == group.end()) {
                full_in = false;
                break;
            }
        }

        if (full_in) num_full_in += 1;
        else num_part_in += 1;
    }

    return make_pair(num_full_in, num_part_in);
}

// vars in group, clauses in group, clauses dependent on group
// When adding, add var to group, for clauses that has var, check if is now covered by group, and how many are added
// for each var keep track of clauses they are in

int main(int argc, const char * argv[]) {
    assert(argc == 2);
    int n_vars, n_clauses;
    const auto clause_list = read_sat(argv[1], n_vars, n_clauses);
    unordered_map<int, vector<int>> var_to_clauses;
    
    for (int i = 0; i < n_clauses; ++i) {
        for (auto var : clause_list[i]) {
            var_to_clauses[abs(var)].push_back(i);
        }
    }

    // TODO do implications and remove all the trivial variables and clauses

    // remove vars with clause determining it and vars without any clauses
    set<int> var_to_remove;
    for (auto clause : clause_list) {
        if (clause.size() == 1) {
            var_to_remove.insert(abs(clause[0]));
        }
    }

    for (auto p : var_to_clauses) {
        if (p.second.empty()) {
            var_to_remove.insert(p.first);
        }
    }

    //for (int var : var_to_remove) {
    //    var_to_clauses.erase(var);
    //}

    vector<int> valid_vars;
    for (int i = 1; i < n_vars + 1; ++i) {
        if (var_to_remove.find(i) != var_to_remove.end()) {
            valid_vars.push_back(i);
        }
    }


    random_device rd;     // only used once to initialise (seed) engine
    mt19937 rng(rd());    // random-number engine used (Mersenne-Twister in this case)
    uniform_int_distribution<int> uni(0,valid_vars.size()); // guaranteed unbiased

    int start_var = 100;//valid_vars[uni(rng)];
    set<int> group;
    group.insert(start_var);

    for (int i = 0; i < 10; ++i) {
        set<int> dependent_clauses = get_dependent_clauses(group, var_to_clauses);

        auto curr_score = num_clauses(group, dependent_clauses, clause_list);
        cout << group.size() << " " << curr_score.first << " " << curr_score.second << "\n";

        set<int> dependent_vars;
        for (int clause_num : dependent_clauses) {
            for (int var :clause_list[clause_num]) {
                if (group.find(abs(var)) == group.end()) dependent_vars.insert(abs(var));
            }
        }

        if (dependent_vars.size() == 0) {
            cout << "size zero!" << endl;
        }

        int best_score = n_clauses;
        int best_var = 0;

        // TODO replace dependent vars with everything?
        for (int var : dependent_vars) {
            if (group.find(var) != group.end()) continue;
            set<int> test_group = group;
            test_group.insert(var);
            set<int> test_dependent_clauses = get_dependent_clauses(test_group, var_to_clauses);
            auto score = num_clauses(test_group, test_dependent_clauses, clause_list);

            if (score.second < best_score) {
                cout << best_score << " to " << score.second << "\n";
                best_score = score.second;
                best_var = var;
            }
        }

        group.insert(best_var);
        cout << "added " << best_var << endl;

    }
    
    return 0;
}

