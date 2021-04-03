#pragma once

#include "preprocessing.h"
#include <vector>
#include <map>

struct Cluster {
    Cluster(std::map<int, int>&& group, const std::vector<std::vector<bool>>&& assigments_);
    const std::map<int, int> var_to_idx;
    std::vector<std::vector<bool>> assignment;
};

Cluster get_cluster(int init_var, const vtc_T& var_to_clauses, 
    const std::vector<std::vector<int>>& clause_list, int max_count, const std::set<int>& used);