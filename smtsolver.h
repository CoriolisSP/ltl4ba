#ifndef __SMTSOLVER__
#define __SMTSOLVER__
#include <z3++.h>
#include <map>
#include <vector>
#include "formula/aalta_formula.h"
#include "solver.h"
#include <string>
using namespace std;

class smtSolver
{
private:
    z3::context c;
    z3::solver s;
    vector<z3::expr> atom;
    map<string,int> atom_idx;
    map<string,aalta::aalta_formula*> next_ap;
    vector<z3::expr> intvar;
    map<string,int> intvar_idx;
    int x_num;
    vector<z3::expr> assertion;
    int nu;

    aalta::aalta_formula* xnf(aalta::aalta_formula* f);
    z3::expr get_assertion(aalta::aalta_formula* f,map<string,string> & ap2smt);
    z3::expr get_full_arith_expr(string arith);
    z3::expr get_arith_expr(string arith,bool &only_num,int &re);
public:
    smtSolver(aalta::aalta_formula* f,map<string,string> & ap2smt);
    z3::check_result check_sat(){return s.check();}
    aalta::Transition *get_trans();
};

enum token_type{ident,number,operate,blank};
void del_space(string & s);

#endif