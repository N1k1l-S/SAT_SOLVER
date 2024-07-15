#include <iostream>
#include <fstream>
#include <sstream>
#include <cctype>
#include "bits/stdc++.h"
using namespace std;

#define UNASSIGNED -1
#define FALSE 0
#define TRUE 1

int y = 0;

void printVectorOfVectors(const vector<vector<int>>& vec) {
    for (const auto& innerVec : vec) {
        for (int num : innerVec) {
            cout << num << " ";
        }
        cout << endl;
    }
}

void printVector(const vector<int>& vec) {
    for (int num : vec) {
        cout << num << " ";
    }
    cout << endl;
}

class CNF{
    
public:
    int var_count,clause_count;
    // vector<int> variables;
    vector<vector<int>> clauses;
    // vector<bool> clauses_t;

    CNF(int vc, int cc) : var_count(vc), clause_count(cc) {}

    void insert_clause(vector<int> clause){
        clauses.push_back(clause);
        // clauses_t.push_back(false);
    }

    // Solve
    // if sat return 1;
    // if unsat return 0;
    // if not enough assignments return 2;
    // NOTE : this function uses its own clauses_t
    int solve(vector<int>& variables){
        vector<bool> clauses_t(clauses.size(),false);
        vector<int> clauses_s(clauses.size(),0);
        for(int c=0;c < clauses.size(); c++){
            for(int v=0;v < clauses[c].size()-1;v++){
                int lit = clauses[c][v];
                if(variables[abs(lit)] != UNASSIGNED){
                    if(lit < 0){
                        if(variables[-1*lit] == 0){
                            // return true;
                            clauses_t[c] = true;
                        }
                        clauses_s[c]++;
                    }
                    else if(lit > 0){
                        if(variables[lit] == 1){
                            // return true;
                            clauses_t[c] = true;
                        }
                        clauses_s[c]++;
                    }
                }
            }
        }
        int fl = 1;
        for(auto b:clauses_t){
            if(b == false){
                fl = 0;
                break;
            }
        }
        if(fl == 1) return 1;

        fl = 1;
        for(int c=0;c<clauses.size();c++){
            if(clauses_s[c] == clauses[c].size() && clauses_t[c] == false){
                fl = 0;
                break;
            }
        }
        if(fl == 0) return 0;

        return 2;
    }

    bool Pure_literal_elimination(vector<int>& variables,vector<bool>& clauses_t){
        // vector<int> pure_literals;
        int fl = 0;
        for(int v=1;v<variables.size()+1;v++){
            if(variables[v] == UNASSIGNED){
                int cur = 2;
                for(int c=0;c<clauses.size();c++){
                    if(clauses_t[c] == false){
                        for(int l=0;l<clauses[c].size();l++){
                            if(v == clauses[c][l] ){ // positive form of literal found
                                if (cur == 2){
                                    cur = 1;
                                }
                                else if(cur == 0){
                                    cur = -1;
                                }
                            }
                            if(v == -1*clauses[c][l] ){ // negative form of literal found
                                if (cur == 2){
                                    cur = 0;
                                }
                                else if(cur == 1){
                                    cur = -1;
                                }
                            }
                        }
                    }
                }
                if(cur == 0){
                    variables[v] = false;
                    fl = 1;
                }
                else if(cur == 1){
                    variables[v] = true;
                    fl = 1;
                }
                // if cur == 2 or -1 pure literal not found
            }
        }
        
        if(fl == 0) return false;
        return true;
    }

    bool Unit_clause_elimination(vector<int>& variables,vector<bool>& clauses_t){
        // vector<int> unit_vars;
        int fl = 0;
        for(int c=0; c<clauses.size(); c++){
            if(clauses_t[c] != true){
                if(clauses[c].back() == 1){
                    clauses_t[c] = true;
                    clauses[c].back() = 0; // No of unassigned vars
                    for(int i=0; i<clauses[c].size()-1; i++){
                        int var = clauses[c][i];
                        if(var < 0){
                            if (variables[-1*var] == UNASSIGNED) {
                                variables[-1*var] = FALSE;
                                fl = 1;
                                // unit_vars.push_back(-1*var);
                            }
                        }
                        else if(var > 0){
                            if (variables[var] == UNASSIGNED) {
                                variables[var] = TRUE;
                                fl = 1;
                                // unit_vars.push_back(var);
                            }
                        }
                    }
                }                
            }
        }

        if(fl == 0) return false; // returning if unit clause elimination not possible
        return true;

        // for(int el:unit_vars){
        //     for(int c=0;c<clauses.size();c++){
        //         if(clauses_t[c] == false){
        //             for(int v=0; v<clauses[c].size()-1; v++){
        //                 if(v == el && variables[el] == true){ // solved
        //                     clauses_t[c] == true;
        //                     clauses[c].back()--;
        //                 }
        //                 else if(v == el && variables[el] == false){ // unsatisfied
        //                     clauses[c].back()--;
        //                     if(clauses[c].back() == 0) return false;
        //                 }
        //                 else if(v == -1*el && variables[el] == false){ // solved
        //                     clauses_t[c] == true;
        //                     clauses[c].back()--;
        //                 }
        //                 else if(v == -1*el && variables[el] == true){ // unsatisfied
        //                     clauses[c].back()--;
        //                     if(clauses[c].back() == 0) return false;
        //                 }
        //             }
        //         }
        //     }
        // }

        // if(unit_vars.size() == 0){ // no unit clauses found
        //     bool pure = Pure_literal_elimination();
        //     if(pure == true) ;
        // }

        // int flag = 1;
        // for(bool tval:clauses_t){
        //     if (tval == false){
        //         flag = 0;
        //         break;
        //     }
        // }

        // if(flag == 1) return true;
    }

    bool DPLL(vector<int> variables,vector<bool> clauses_t){
        // std::cout << y++ << " ";
        int sat = solve(variables);
        if(sat == 1){
            return true;
        }
        else if(sat == 0){
            return false;
        }

        // PLE and UCE
        bool uc = 1,ple = 1;
        while(uc || ple){
            if(uc) uc = Unit_clause_elimination(variables,clauses_t);
            if(ple) ple = Pure_literal_elimination(variables,clauses_t);
        }
        
        sat = solve(variables);
        if(sat == 1){
            return true;
        }
        else if(sat == 0){
            return false;
        }

        // decisison step
        // choose variable;
        int x = -1;
        for(int i=1;i<variables.size()+1;i++){
            if(variables[i] == UNASSIGNED){
                x = i;
                break;
            }
        }

        if(x == -1) return false;

        variables[x] = TRUE;
        bool b = DPLL(variables,clauses_t);
        if(b == true) return true;

        variables[x] = FALSE;
        b = DPLL(variables,clauses_t);
        if(b == true) return true;

        return false;
    }
};

int main(int argc, char* argv[]){
    ifstream inputfile(argv[1]);

    if(!inputfile.is_open()) {
        cerr << "ERROR OPENING FILE\n";
        return 1;
    }

    string s;
    CNF* cnf;

    // INPUT
    int var_count,clause_count;
    // vector<vector<int>> clauses;
    vector<int> clause;
    while(getline(inputfile,s)) {
        stringstream stream(s);
        int num;

        if( s[0] == 'c' ) continue;
        else if( s[0] == 'p' ){
            string temp;
            stream >> temp;
            stream >> temp;
            stream >> var_count;
            stream >> clause_count;
            cnf = new CNF(var_count,clause_count);
            continue;
        }

        clause.clear();
        while(stream >> num){
            if(num != 0){
                clause.push_back(num);
            }
        }
        clause.push_back(clause.size());
        cnf->insert_clause(clause);
        // cout << endl;
    }

    // Print clauses
    // printVectorOfVectors(cnf->clauses);

    // Processing
    vector<int> variables(var_count+1,UNASSIGNED);
    vector<bool> clauses_t(clause_count,false);
    bool sat = cnf->DPLL(variables,clauses_t);

    inputfile.close();

    if(sat == true){
        cout << "SATISFIABLE" << endl;
    }
    else{
        cout << "UNSATISFIABLE" << endl;
    }

    return 0;
}