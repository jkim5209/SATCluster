#include "preprocessing.h"
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
#include <unordered_map>
#include <map>
#include <set>
#include <stdlib.h>
#include <math.h>
#include <filesystem>
#include <chrono>

#define NDEBUG // TURNS off asserts
#include <cassert>

using namespace std;

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


vtc_T get_vtc(const vector<vector<int>>& clause_list) {
    vtc_T vtc;
    for (int clause_num = 0; clause_num < clause_list.size(); ++clause_num) {
        for (int var : clause_list[clause_num]) {
            vtc[var].get_contains(var > 0).push_back(clause_num);
        }
    }

    return vtc;
}

//class ImplicationRemover {
//private:
//    map<int, bool> ass;
//    map<int, ImplicationTracker> implications;
//    const map<int, int>& group;
//    const vtc_T& var_to_clauses;
//    const vector<vector<int>>& clause_list;
//    map<int, int>& implication_counter;
//
//}

/*
void remove_implications(vector<vector<int>>& clause_list) {
        map<int, bool> implications;
        vtc_T var_to_clauses = get_vtc(clause_list);

        ass[var] = value;
        queue<int> unprocessed_implications;
        for (const auto& clause : clause_list) {
            if (clause.empty()) {
                throw "UNSAT";
            }
            if (clause.size() == 1) {

            }
        }
        if (value) {
            unprocessed_implications.push(var);
        } else {
            unprocessed_implications.push(-var);
        }

        while (!unprocessed_implications.empty()) {
            int var_to_process = unprocessed_implications.front();
            unprocessed_implications.pop();
            
            // only want to look at clauses that can give additional implications
            const vector<int>& clauses_to_look_at = (var_to_process > 0) ?
                    var_to_clauses.at(abs(var_to_process)).contains_neg :
                    var_to_clauses.at(abs(var_to_process)).contains_default;

            //vector<int> clauses_to_look_at = var_to_clauses.at(abs(var_to_process)).contains_neg;
            //for (int a : var_to_clauses.at(abs(var_to_process)).contains_default) {
            //    clauses_to_look_at.push_back(a);
            //}

            for (int clause_num : clauses_to_look_at) {
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
                if (implication_var == 0) return false; // this means all the var was in implication or assignment but wasn't satisfied

                //auto it = implications.find(abs(implication_var));
                //if (it != implications.end()) {
                //    if (it->second != (implication_var > 0)) return false;
                //}
                //implications.emplace(abs(implication_var), ImplicationTracker({implication_counter, abs(implication_var), (implication_var > 0)}));
                implications.emplace(abs(implication_var), ImplicationTracker{implication_counter, abs(implication_var), (implication_var > 0)});
                unprocessed_implications.push(implication_var);
            }
        }
        return true;

}
*/


// check if a is a subset of b
bool isSubset(const vector<int>& a, const vector<int>& b) {
    return includes(b.begin(), b.end(), a.begin(), a.end());
}

// counts number of items in both vec1 vec2 (cardinality of set intersection)
// assumes sorted
int num_intersection(const vector<int>& vec1, const vector<int>& vec2) {
    auto it1 = vec1.begin();
    auto it2 = vec2.begin();
    int num_same = 0;
    while (it1 != vec1.end() && it2 != vec2.end()) {
        if (*it1 < *it2) {
            ++it1;
        } else if (*it1 > *it2) {
            ++it2;
        } else {
            ++num_same;
            ++it1;
            ++it2;
        }
    }
    return num_same;
}

// depth starts at num vars
bool helper(int depth, vector<bool>& curr, const vector<vector<int>>& int_clauses) {
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
            
            return false;
        }
    }

    if (depth == 0) {
        return true;
    }

    if (helper(depth - 1, curr, int_clauses)) {
        return true;
    }

    if (helper(depth - 1, curr, int_clauses)) {
        return true;
    }
    return false;
}

bool compute_sat(const vector<int>& vars, const vector<vector<int>>& clauses) {
    if (clauses.empty()) return true;
    if (vars.empty()) return false;


    map<int, int> var_new_mapping;
    for (int i = 0; i < vars.size(); ++i) {
        var_new_mapping[vars[i]] = i + 1;
    }
    vector<vector<int>> remapped_clauses;

    for (auto clause : clauses) {
        vector<int> new_clause;
        bool hasExternal = false;
        for (int var : clause) {
            auto it = var_new_mapping.find(abs(var));
            if (var > 0) {
                new_clause.push_back(it->second);
            } else {
                new_clause.push_back(-it->second);
            }
        }
        remapped_clauses.emplace_back(move(new_clause));
    }

    vector<bool> curr;
    return helper(vars.size(), curr, remapped_clauses);
}
/*
void compute_skyline(const vector<Assignment>& assignments, const vtc_T& var_to_clauses, 
        const vector<vector<int>>& clause_list) {

    set<int> subsets;

    for (int i = 0; i < assignments.size(); ++i) {
        // TODO don't include internal clauses
        set<int> sat_clauses;
        for (const auto& ass : assignments[i].ass) {
            for (int clause_num : var_to_clauses.at(ass.first).get_contains(ass.second)) {
                sat_clauses.insert(clause_num);
            }
        }

        for (const auto& impl : assignments[i].implications) {
            for (int clause_num : var_to_clauses.at(impl.first).get_contains(impl.second)) {
                sat_clauses.insert(clause_num);
            }
        }

        for (int j = 0; j < assignments.size(); ++j) {
            if (j == i) continue;
            if (subsets.find(j) != subsets.end()) continue;
            set<int> free_vars;
            set<int> implication_intersection;
            set<int> unsat_clauses = sat_clauses;
            for (const auto& p : assignments[i].implications) {
                auto it = assignments[j].implications.find(p.first);
                if (it == assignments[j].implications.end()) {
                    free_vars.insert(p.first);
                } else {
                    implication_intersection.insert(p.first);
                    for (int clause_num : var_to_clauses.at(it->first).get_contains(it->second)) {
                        unsat_clauses.erase(clause_num);
                    }
                }
            }

            for (const auto& p : assignments[j].ass) {
                for (int clause_num : var_to_clauses.at(p.first).get_contains(p.second)) {
                    unsat_clauses.erase(clause_num);
                }
            }

            vector<vector<int>> required_clauses;
            bool found_impossible_clause = false;
            for (int clause_num : unsat_clauses) {
                vector<int> clause;
                for (int var : clause_list[clause_num]) {
                    if (free_vars.find(abs(var)) != free_vars.end()) {
                        clause.push_back(var);
                    }
                }
                if (clause.empty()) {
                    found_impossible_clause = true;
                    break;
                }
                //cout << clause.size() << "/" << clause_list[clause_num].size() << endl;
                required_clauses.emplace_back(move(clause));
            }
            if (found_impossible_clause) {
                //cout << i << " " << j << "found impossible" << endl;
                continue;
            }
            double avg_size = 0;
            int num_one = 0;
            int num_two = 0;
            for (const auto& v : required_clauses) {
                avg_size += v.size();
                if (v.size() == 1) ++num_one;
                else if (v.size() == 2) ++num_two;
            }
            cout << "avg: " << avg_size << " " << num_one << " " << num_two << endl;
            cout << i << " " << j << "intersection " << implication_intersection.size() << "/" << assignments[i].implications.size() << 
                " num free vars: " << free_vars.size() << " required " << required_clauses.size() << "/" <<sat_clauses.size() << endl;
            const vector<vector<int>> reduced_required_clauses = remove_implications(move(required_clauses));
            cout << "reduced size: " << reduced_required_clauses.size() << endl;
            avg_size = 0;
            num_one = 0;
            num_two = 0;
            for (const auto& v : reduced_required_clauses) {
                avg_size += v.size();
                if (v.size() == 1) ++num_one;
                else if (v.size() == 2) ++num_two;
            }
            cout << "avg: " << avg_size << " " << num_one << " " << num_two << endl;


            set<int> required_vars;
            for (const auto& clause : reduced_required_clauses) {
                for (int var : clause) {
                    required_vars.insert(abs(var));
                }
            }
            const vector<int> required_vars_vec(required_vars.begin(), required_vars.end());
            if (compute_sat(required_vars_vec, required_clauses)) {
                // IS sat
                subsets.insert(i);
                cout << "TRUE\n";
                break;
            }
        }
    }

    cout << "extreme subset " << subsets.size() << endl;
}
*/