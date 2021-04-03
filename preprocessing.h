#pragma once

#include <vector>
#include <string>
#include <map>
#include <unordered_map>
#include <set>

std::vector<std::vector<int>> remove_implications(std::vector<std::vector<int>>&& clause_list);

struct ClausesContainingVar {
    std::vector<int> contains_default;
    std::vector<int> contains_neg;
    inline const std::vector<int>& get_contains(bool b) const noexcept {
        return b ? contains_default : contains_neg;
    }

    inline std::vector<int>& get_contains(bool b) noexcept {
        return b ? contains_default : contains_neg;
    }
};

using vtc_T = std::unordered_map<int, ClausesContainingVar>;
std::vector<std::vector<int>> read_sat(std::string filename, int& n_vars, int& n_clauses);