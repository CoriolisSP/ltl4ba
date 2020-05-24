#include "formula/aalta_formula.h"
#include "automata.h"
#include <cstdio>
#include <cstring>
#include <string>
#include <fstream>
#include "carsolver.h"

#define MAXN 100000
char in[MAXN];

using namespace aalta;
using namespace std;

void usage()
{
    printf("Usage: ltl4ba [OPTION...] [FORMULA...]\n");
    printf("Translate LTL formulas in bit-level or word-level into (generalized) Buchi automata.\n");
    printf("By default, input bit-level formula(s), output generalized Buchi automata in HOA format.\n");
    printf("Input option:\n");
    printf("  -f: process bit-level formula in string\n");
    printf("  -F: process each line of file as a bit-level formula\n");
    printf("  -s: process word-level formula in string\n");
    printf("  -S: process each line of file as a word-level formula\n");
    printf("  -b: output Buchi automata (by default generalized Buchi automata)\n");
    printf("  -d: output the autumata in dot language (by default HOA)");
    printf("  --help: get the usage of the tool\n");
}

int main(int argc, char **argv)
{
    int info;
    bool dot=false,ba=false,sat=true,file=false;
    for(int i=1;i<argc;i++)
    {
        if(argv[i][0]=='-')
        {
            switch(argv[i][1])
            {
                case 'd': dot=true; break;
                case 'b': ba=true; break;
                case '-': if(strcmp(argv[i],"--help")==0) usage(); return 0;
                case 'f': break;
                case 'F': file=true; break;
                case 's': sat=false; break;
                case 'S': sat=false; file=true; break;
                default:  printf("Invalid Input.\nTry 'ltl4ba --help' for more information.\n"); return 0;
            }
        }
        else info=i;
    }
    if(sat&&!file)
    {
        strcpy(in, argv[info]);
        aalta_formula *f;
        f = aalta_formula(in).unique();
        
        f = f->nnf();
        f = f->simplify();
        f = f->split_next();
        automata a=automata(f,ba);
        if(!dot) a.print();
        else a.print_dot();
        aalta_formula::destroy();
    }
    else if(sat&&file)
    {
        ifstream fin;
        fin.open(argv[info],ios::in);
        string str;
        while (getline(fin,str))
        {
            aalta_formula *f;
            f = aalta_formula(str.c_str()).unique();
            
            f = f->nnf();
            f = f->simplify();
            f = f->split_next();
            automata a=automata(f,ba);
            if(dot) a.print_dot();
            else a.print();
            aalta_formula::destroy();
        }
        fin.close();
    }
    else if(!sat&&!file)
    {
        strcpy(in, argv[info]);
        extd_automata ea=extd_automata(string(in),ba);
        if(dot) ea.print_dot();
        else ea.print();
        aalta_formula::destroy();
    }
    else
    {
        ifstream fin;
        fin.open(argv[info],ios::in);
        string str;
        while (getline(fin,str))
        {
            extd_automata a=extd_automata(str,ba);
            if(dot) a.print_dot();
            else a.print();
            aalta_formula::destroy();
        }
        fin.close();
    }
    /*
    aalta_formula *f;
    f=aalta_formula(argv[1]).unique();
    f=f->nnf();
    f=f->simplify();
    f=f->split_next();
    aalta::CARSolver *solve = new aalta::CARSolver(f);
    solve->print_cnf();
    delete solve;*/
    return 0;
}
