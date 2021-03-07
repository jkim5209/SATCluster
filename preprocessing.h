#include <vector>
#include <string>
#include <map>
#include <unordered_map>
#include <set>

using vtc_T = std::unordered_map<int, std::vector<int>>;
std::vector<std::vector<int>> read_sat(std::string filename, int& n_vars, int& n_clauses);

std::map<int, int> get_cluster(int init_var, const vtc_T& var_to_clauses, 
    const std::vector<std::vector<int>>& clause_list, int max_count, const std::set<int>& used);