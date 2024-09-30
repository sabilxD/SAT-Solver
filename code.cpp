#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <set>
#include <unordered_map>
#include <optional>
#include <algorithm>
#include <random>
#include <cassert>

using namespace std;

struct Literal {
    int variable;
    bool negation;

    Literal(int var, bool neg) : variable(var), negation(neg) {}

    Literal neg() const {
        return Literal(variable, !negation);
    }

    string to_string() const {
        return negation ? "¬" + std::to_string(variable) : std::to_string(variable);
    }

    bool operator==(const Literal& other) const {
        return variable == other.variable && negation == other.negation;
    }
};

struct Clause {
    vector<Literal> literals;

    Clause(const vector<Literal>& lits) : literals(lits) {}

    size_t size() const {
        return literals.size();
    }

    string to_string() const {
        stringstream ss;
        for (size_t i = 0; i < literals.size(); ++i) {
            if (i > 0) ss << " ∨ ";
            ss << literals[i].to_string();
        }
        return ss.str();
    }
};

struct Formula {
    vector<Clause> clauses;
    set<int> variables;

    Formula(const vector<Clause>& cls) : clauses(cls) {
        for (const Clause& clause : clauses) {
            for (const Literal& lit : clause.literals) {
                variables.insert(lit.variable);
            }
        }
    }

    set<int> get_variables() const {
        return variables;
    }

    string to_string() const {
        stringstream ss;
        for (size_t i = 0; i < clauses.size(); ++i) {
            if (i > 0) ss << " ∧ ";
            ss << "(" << clauses[i].to_string() << ")";
        }
        return ss.str();
    }
};

struct Assignment {
    bool value;
    optional<Clause> antecedent;
    int dl;  // decision level

    Assignment(bool val, optional<Clause> ant, int decision_level)
        : value(val), antecedent(ant), dl(decision_level) {}
};

class Assignments {
public:
    unordered_map<int, Assignment> assignments;
    int dl;

    Assignments() : dl(0) {}

    bool value(const Literal& literal) const {
        auto it = assignments.find(literal.variable);
        if (it == assignments.end()) return false;
        return literal.negation ? !it->second.value : it->second.value;
    }

    void assign(int variable, bool value, const optional<Clause>& antecedent) {
        assignments[variable] = Assignment(value, antecedent, dl);
    }

    void unassign(int variable) {
        assignments.erase(variable);
    }

    bool satisfy(const Formula& formula) const {
        for (const Clause& clause : formula.clauses) {
            bool clause_satisfied = false;
            for (const Literal& lit : clause.literals) {
                if (value(lit)) {
                    clause_satisfied = true;
                    break;
                }
            }
            if (!clause_satisfied) return false;
        }
        return true;
    }

    size_t size() const {
        return assignments.size();
    }
};

bool all_variables_assigned(const Formula& formula, const Assignments& assignments) {
    return formula.get_variables().size() == assignments.size();
}

pair<int, bool> pick_branching_variable(const Formula& formula, const Assignments& assignments) {
    vector<int> unassigned_vars;
    for (int var : formula.get_variables()) {
        if (assignments.assignments.find(var) == assignments.assignments.end()) {
            unassigned_vars.push_back(var);
        }
    }
    random_device rd;
    mt19937 gen(rd());
    uniform_int_distribution<> var_dist(0, unassigned_vars.size() - 1);
    uniform_int_distribution<> val_dist(0, 1);
    int var = unassigned_vars[var_dist(gen)];
    bool val = val_dist(gen);
    return {var, val};
}

void backtrack(Assignments& assignments, int b) {
    vector<int> to_remove;
    for (const auto& [var, assignment] : assignments.assignments) {
        if (assignment.dl > b) {
            to_remove.push_back(var);
        }
    }
    for (int var : to_remove) {
        assignments.unassign(var);
    }
}

pair<string, optional<Clause>> unit_propagation(const Formula& formula, Assignments& assignments) {
    bool finish = false;
    while (!finish) {
        finish = true;
        for (const Clause& clause : formula.clauses) {
            int false_count = 0;
            optional<Literal> unassigned_literal;
            bool clause_satisfied = false;
            for (const Literal& literal : clause.literals) {
                if (assignments.assignments.find(literal.variable) == assignments.assignments.end()) {
                    unassigned_literal = literal;
                } else if (assignments.value(literal)) {
                    clause_satisfied = true;
                    break;
                } else {
                    ++false_count;
                }
            }

            if (clause_satisfied) continue;

            if (false_count == clause.literals.size() - 1 && unassigned_literal.has_value()) {
                assignments.assign(unassigned_literal->variable, !unassigned_literal->negation, clause);
                finish = false;
            } else if (false_count == clause.literals.size()) {
                return {"conflict", clause};
            }
        }
    }
    return {"unresolved", nullopt};
}

pair<int, Clause> conflict_analysis(const Clause& clause, const Assignments& assignments) {
    if (assignments.dl == 0) return {-1, clause};

    Clause learned_clause = clause;
    int decision_level = assignments.dl - 1;

    return {decision_level, learned_clause};
}

optional<Assignments> cdcl_solve(Formula& formula) {
    Assignments assignments;

    auto [reason, clause] = unit_propagation(formula, assignments);
    if (reason == "conflict") return nullopt;

    while (!all_variables_assigned(formula, assignments)) {
        auto [var, val] = pick_branching_variable(formula, assignments);
        assignments.dl++;
        assignments.assign(var, val, nullopt);

        while (true) {
            tie(reason, clause) = unit_propagation(formula, assignments);
            if (reason != "conflict") break;

            auto [b, learned_clause] = conflict_analysis(clause.value(), assignments);
            if (b < 0) return nullopt;

            formula.clauses.push_back(learned_clause);
            backtrack(assignments, b);
            assignments.dl = b;
        }
    }

    return assignments;
}

Formula parse_dimacs_cnf(const string& content) {
    vector<Clause> clauses;
    vector<Literal> current_clause;

    istringstream iss(content);
    string line;
    while (getline(iss, line)) {
        istringstream tokens(line);
        string token;
        while (tokens >> token) {
            if (token == "c" || token == "p") break;

            int lit = stoi(token);
            if (lit == 0) {
                clauses.emplace_back(current_clause);
                current_clause.clear();
            } else {
                int var = abs(lit);
                bool neg = lit < 0;
                current_clause.push_back(Literal(var, neg));
            }
        }
    }

    return Formula(clauses);
}

int main(int argc, char* argv[]) {
    if (argc != 2) {
        cout << "Please provide a DIMACS CNF filename as an argument." << endl;
        return 1;
    }

    ifstream file(argv[1]);
    if (!file.is_open()) {
        cout << "Unable to open the file: " << argv[1] << endl;
        return 1;
    }

    stringstream buffer;
    buffer << file.rdbuf();
    string dimacs_cnf = buffer.str();

    Formula formula = parse_dimacs_cnf(dimacs_cnf);
    optional<Assignments> result = cdcl_solve(formula);

    if (result.has_value()) {
        assert(result->satisfy(formula));
        cout << "Formula is SAT with assignments:" << endl;
        for (const auto& [var, assignment] : result->assignments) {
            cout << var << ": " << (assignment.value ? "True" : "False") << endl;
        }
    } else {
        cout << "Formula is UNSAT." << endl;
        cout << "No satisfying assignment exists for the given formula." << endl;  // Additional output for UNSAT
    }

    return 0;
}
