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
#include <cassert>
#include <unordered_map>
#include <map>
#include <set>
#include <stdlib.h>
#include <math.h>
#include <filesystem>
#include <chrono>

using namespace std;

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

class ImplicationTracker {
public:
    ImplicationTracker(map<int, int>& implication_counter_, int var_, bool value_) : implication_counter(implication_counter_), var(var_), value(value_) {
        ++implication_counter[var];
    }

    ImplicationTracker(const ImplicationTracker& other) : implication_counter(other.implication_counter), var(other.var), value(other.value) {
        ++implication_counter[var];
    }

    ~ImplicationTracker() {
        --implication_counter[var];
        assert(implication_counter[var] >= 0);
    }

    bool operator<(const ImplicationTracker& other) {
        return var < other.var;
    }

    operator bool() const {
        return value;
    }
private:
    map<int, int>& implication_counter;
    int var;
    bool value;
};

class Assignment {
public:
    Assignment(const map<int, int>& group_, const vtc_T& var_to_clauses_, const vector<vector<int>>& clause_list_, map<int, int>& implication_counter_) :
        group(group_), var_to_clauses(var_to_clauses_), clause_list(clause_list_), implication_counter(implication_counter_) {};

    Assignment(Assignment&& other) : group(other.group), var_to_clauses(other.var_to_clauses), clause_list(other.clause_list), implication_counter(other.implication_counter) {
        swap(ass, other.ass);
        swap(implications, other.implications);
    }

    Assignment(const Assignment& other) = default;

    Assignment& operator=(Assignment&& other) noexcept {
        swap(ass, other.ass);
        swap(implications, other.implications);
        return *this;
    }

    // naively check if we can assign value to var.
    // if returns false, always false, but might return false positive.
    // for var and then neg var returned as pair
    pair<bool, bool> naive_check_assign(int var) noexcept {
        auto it = implications.find(var);
        if (it == implications.end()) return make_pair(true, true);

        if (it->second) {
            return make_pair(true, false);
        }

        return make_pair(false, true);
    }

    // returns true if valid assignment false otherwise
    bool assign(int var, bool value) noexcept {
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
                if (implication_var == 0) return false; // this means all the var was in implication or assignment but wasn't satisfied
                //implications.emplace(abs(implication_var), ImplicationTracker({implication_counter, abs(implication_var), (implication_var > 0)}));
                implications.emplace(abs(implication_var), ImplicationTracker{implication_counter, abs(implication_var), (implication_var > 0)});
                unprocessed_implications.push(abs(implication_var));
            }
        }
        return true;
    }

public: // TODO make this private?
    map<int, bool> ass;
    map<int, ImplicationTracker> implications;
    const map<int, int>& group;
    const vtc_T& var_to_clauses;
    const vector<vector<int>>& clause_list;
    map<int, int>& implication_counter;
}; 

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

map<int, int> get_cluster(int init_var, const vtc_T& var_to_clauses, const vector<vector<int>>& clause_list, int max_count, const set<int>& used) {
    cout << "init var " << init_var << endl;
    int counter = 0;
    map<int, int> group;
    vector<int> vars;
    //vars.push_back(init_var);
    group[init_var] = counter++;
    vector<Assignment> assignments;
    assignments.reserve(max_count * 2);
    map<int, int> implication_counter;
    assignments.emplace_back(group, var_to_clauses, clause_list, implication_counter);
    bool inserted = assignments.back().assign(init_var, true);
    assert(inserted);
    assignments.emplace_back(group, var_to_clauses, clause_list, implication_counter);
    inserted = assignments.back().assign(init_var, false);
    assert(inserted);

    while (assignments.size() < max_count) {
        int max_counter = 0;
        int max_var = 0;
        for (auto p : implication_counter) {
            if (p.second > max_counter) {
                max_counter = p.second;
                max_var = p.first;
            }
        }
        //cout << "avg num implications: " << num_implications / assignments.size() << " " << implication_counter.size() << endl;

        assert(max_counter != 0);

        vector<size_t> to_remove;

        group[max_var] = counter++;
        size_t original_size = assignments.size();
        for (size_t i = 0; i < original_size; ++i) {
            auto check = assignments[i].naive_check_assign(max_var);
            if (check.first && check.second) {
                assignments.emplace_back(assignments[i]);
                if (!assignments[i].assign(max_var, true)) {
                    to_remove.push_back(i);
                }

                if (!assignments.back().assign(max_var, false)) {
                    assignments.pop_back();
                }
                continue;
            }

            if (check.first && !check.second) {
                if (!assignments[i].assign(max_var, true)) {
                    to_remove.push_back(i);
                }
            }

            if (!check.first && check.second) {
                if (!assignments[i].assign(max_var, false)) {
                    to_remove.push_back(i);
                }
            }

            if (!check.first && !check.second) {
                // Is this possible...?
                assert(true);
            }
        }

        for (auto it = to_remove.rbegin(); it != to_remove.rend(); ++it) {
            assignments[*it] = move(assignments.back()); // TODO is this an issue if moving itself?
            assignments.pop_back();
        }

        auto it = implication_counter.find(max_var);
        if (it != implication_counter.end()) {
            assert(it->second == 0);
            implication_counter.erase(it);
        }

        //cout << counter << " num ass " << assignments.size() <<  endl;
    }

    cout << "num vars: " << counter << " effective vars: " << log2(assignments.size()) << " raw num " << assignments.size() << "\n";
    //assignments.clear(); // have to make sure implication trackers dtor gets called before implication_counter goes away
    //return group;

    set<int> relavent_clauses;
    for (auto p : group) {
        for (int clause_num : var_to_clauses.at(p.first)) {
            relavent_clauses.insert(clause_num);
        }
    }

    vector<int> external_clauses;
    vector<int> internal_clauses;
    for (int clause_num : relavent_clauses) {
        bool internal = true;
        for (int clause_var : clause_list[clause_num]) {
            if (group.find(abs(clause_var)) == group.end()) {
                internal = false;
                break;
            }
        }
        if (internal) internal_clauses.push_back(clause_num);
        else external_clauses.push_back(clause_num);
    }

    cout << "num internal clauses: " << internal_clauses.size() << " external " << external_clauses.size() << "\n";

    //assignments.clear(); // have to make sure implication trackers dtor gets called before implication_counter goes away
    //return group;

    int smart_subsets = 0;

    // stat checking
    for (const auto& ass : assignments) {
        for (int clause_num : internal_clauses) {
            bool satisfied = false;
            for (int clause_var : clause_list[clause_num]) {
                auto it = ass.ass.find(abs(clause_var));
                if (it == ass.ass.end()) continue;
                if (it->second == (clause_var > 0)) {
                    satisfied = true;
                    break;
                }
            }
            assert(satisfied);
        }
    }

    set<int> smart_covered;

    for (int i = 0; i < assignments.size(); ++i) {
        if (smart_covered.find(i) != smart_covered.end()) continue;
        for (int j = i + 1; j < assignments.size(); ++j) {
            if (smart_covered.find(j) != smart_covered.end()) continue;
            vector<int> intersection;
            auto i_it = assignments[i].implications.begin();
            auto j_it = assignments[j].implications.begin();
            while (i_it != assignments[i].implications.end() && j_it != assignments[j].implications.end()) {
                if (i_it->first < j_it->first) {
                    ++i_it;
                } else if (i_it->first > j_it->first) {
                    ++j_it;
                } else {
                    intersection.push_back(i_it->first);
                    ++i_it;
                    ++j_it;
                }
            }

            map<int, bool> i_var_ass = assignments[i].ass;
            for (auto p : assignments[i].implications) {
                i_var_ass[p.first] = p.second;
            }

            map<int, bool> j_var_ass = assignments[j].ass;
            for (auto p : assignments[j].implications) {
                j_var_ass[p.first] = p.second;
            }

            set<int> relavent_clauses_with_intersection = relavent_clauses;
            for (int var : intersection) {
                for (int clause_num : var_to_clauses.at(var)) {
                    relavent_clauses_with_intersection.insert(clause_num);
                }
            }

            vector<int> i_sat_groups;
            vector<int> j_sat_groups;
            for (int clause_num : external_clauses) {
                bool satisfied = false;
                for (int clause_var : clause_list[clause_num]) {
                    auto it = i_var_ass.find(abs(clause_var));
                    if (it == i_var_ass.end()) continue;
                    if (it->second == (clause_var > 0)) {
                        satisfied = true;
                        break;
                    }
                }

                if (satisfied) {
                    i_sat_groups.push_back(clause_num);
                }
                satisfied = false;

                for (int clause_var : clause_list[clause_num]) {
                    auto it = j_var_ass.find(abs(clause_var));
                    if (it == j_var_ass.end()) continue;
                    if (it->second == (clause_var > 0)) {
                        satisfied = true;
                        break;
                    }
                }

                if (satisfied) {
                    j_sat_groups.push_back(clause_num);
                }

            }
            int n = num_intersection(i_sat_groups, j_sat_groups);
            if (n == i_sat_groups.size()) {
                smart_covered.insert(i);
            } else if (n == j_sat_groups.size()) {
                smart_covered.insert(j);
            }
        }
    }

    cout << "smart subsets " << smart_covered.size() << endl;


    vector<vector<int>> clause_sat_groups;
    int max_sat = 0;
    double tot_sat = 0;
    for (const auto& ass : assignments) {
        vector<int> sat_groups;
        int num_sat = 0;
        for (int clause_num : external_clauses) {
            bool satisfied = false;
            for (int clause_var : clause_list[clause_num]) {
                auto it = ass.ass.find(abs(clause_var));
                if (it == ass.ass.end()) continue;
                if (it->second == (clause_var > 0)) {
                    satisfied = true;
                    break;
                }
            }
            if (satisfied) {
                sat_groups.push_back(clause_num);
                ++num_sat;
            }
        }
        clause_sat_groups.emplace_back(move(sat_groups));
        if (max_sat < num_sat) max_sat = num_sat;
        tot_sat += num_sat;
    }
    cout << "max sat " << max_sat << "avg " << tot_sat / assignments.size() << endl;
    cout << "sat group size" << clause_sat_groups.back().size() << endl;

    vector<vector<int>> exclusive_clause_sat_groups;
    for (const auto& ass : assignments) {
        vector<int> sat_groups;
        int num_sat = 0;
        for (int clause_num : external_clauses) {
            bool satisfied = false;
            for (int clause_var : clause_list[clause_num]) {
                auto it = ass.ass.find(abs(clause_var));
                if (it == ass.ass.end()) continue;
                if (it->second == (clause_var > 0)) {
                    satisfied = true;
                    break;
                }
            }
            if (satisfied) {
                bool satisfied_by_implication = false;
                for (int clause_var : clause_list[clause_num]) {
                    auto it = ass.implications.find(abs(clause_var));
                    if (it == ass.implications.end()) continue;
                    if (it->second == (clause_var > 0)) {
                        satisfied_by_implication = true;
                        break;
                    }
                }

                if (!satisfied_by_implication) {
                    sat_groups.push_back(clause_num);
                }
            }
        }
        exclusive_clause_sat_groups.emplace_back(move(sat_groups));
    }
    double ratio_sum = 0;
    for (int i = 0; i < clause_sat_groups.size(); ++i) {
        ratio_sum += double(exclusive_clause_sat_groups[i].size()) / clause_sat_groups[i].size();
    }
    cout << "avg ratio " << ratio_sum / clause_sat_groups.size() << endl;
    double num_impl = 0;
    for (const auto& ass : assignments) {
        num_impl += ass.implications.size();
    }
    cout << "avg num impl " << num_impl / assignments.size() << endl;

    int num_exclusive_subset = 0;
    for (int i = 0; i < exclusive_clause_sat_groups.size(); ++i) {
        for (int j = 0; j < exclusive_clause_sat_groups.size(); ++j) {
            if (i == j) continue;
            if (isSubset(exclusive_clause_sat_groups[i], clause_sat_groups[j])) {
                ++num_exclusive_subset;
                break;
            }
        }
    }

    cout << "exclusive subset " << num_exclusive_subset << endl;

    // sort with least sat first
    sort(clause_sat_groups.begin(), clause_sat_groups.end(), [](const vector<int>& a, const vector<int>& b) {return a.size() < b.size(); });
    int num_subset = 0;
    vector<vector<int>> clause_sat_groups_no_subset;

    for (size_t i = 0; i < clause_sat_groups.size(); ++i) {
        // TODO prob more efficient if you go backwards
        bool is_subset = false;
        for (size_t j = i + 1; j < clause_sat_groups.size(); ++j) {
            if (isSubset(clause_sat_groups[i], clause_sat_groups[j])) {
                //cout << "found subset!\n";
                ++num_subset;
                is_subset = true;
                break;
            }
        }

        if (!is_subset) clause_sat_groups_no_subset.push_back(clause_sat_groups[i]);
    }

    map<int, int> num_sat_counter;
    for (const auto& sats : clause_sat_groups_no_subset) {
        for (int clause_num : sats) {
            ++num_sat_counter[clause_num];
        }
    }
    int always_covered = 0;
    int never_covered = 0;
    for (int clause_num : external_clauses) {
        auto it = num_sat_counter.find(clause_num);
        if (it == num_sat_counter.end()) {
            ++never_covered;
            continue;
        }

        if (it->second == clause_sat_groups_no_subset.size()) ++always_covered;
    }
    

    cout << "never covered " << never_covered << " always covered " << always_covered << endl;
    cout << "num vars: " << counter << " effective vars: " << log2(assignments.size()) << " raw num " << assignments.size() << " num subset: " << num_subset << endl;;

    assignments.clear(); // have to make sure implication trackers dtor gets called before implication_counter goes away
    return group;
}