#ifndef __AUTOMATA_H__
#define __AUTOMATA_H__
#include "formula/aalta_formula.h"
#include "solver.h"
#include <vector>
#include <set>
#include <map>

using namespace std;

class trans
{
private:
    aalta::aalta_formula *label;
    int next;
    set<int> acc_cdt;
    aalta::aalta_formula *remove_tag_get_acc(aalta::aalta_formula *s);

public:
    trans(aalta::aalta_formula *l, int n, bool remove_tag = false, const int &acc_num = 0);
    void print_trans();
    aalta::aalta_formula *get_label() { return label; }
    void print_nxt_acc(bool dot=false);
    int get_level(int j,int m);
    int get_next(){return next;}
    void update_next(int a){next=next+a;}
};

class state
{
private:
    int sid;
    aalta::aalta_formula *property;
    vector<trans *> trans_set;
    int level;
    int lth;
    bool accessible;

public:
    state(int s, aalta::aalta_formula *p,int lv=-1):sid(s),property(p),lth(0),level(lv),accessible(false) {}
    ~state();
    void add_trans(trans *t);
    void print_state();
    aalta::aalta_formula *get_property() { return property; }
    int length() { return lth; }
    int get_level(){return level;}
    trans *get_trans(int idx) { return trans_set[idx]; }
    void arrive();
    bool can_get(){return accessible;}
};

class transition_system
{
protected:
    vector<state *> states;

public:
    transition_system() {}
    transition_system(aalta::aalta_formula *src_f);
    ~transition_system();
    void print();
};

class automata : public transition_system
{
protected:
    string src_formula;
    aalta::aalta_formula *add_acc_tag(aalta::aalta_formula *s);
    void print_label_numeric(aalta::aalta_formula *lb);
    void label2int(aalta::aalta_formula *lb, vector<int> &v);
    static bool U_flag;
    static int until_num;
    int ap_num;
    map<string, int> ap_map;
    vector<string> aps;
    bool is_ba;

public:
    automata(){}
    automata(aalta::aalta_formula *src_f,bool ba=false);
    ~automata() {}
    void print();
    void print_dot();
    void remove_state(int idx);
};

class extd_automata: public automata
{
private:
    aalta::aalta_formula* pre_process(string s);
    map<string,string> ap2smt;
    bool unknow;
public:
    extd_automata(string src,bool ba=false);
    ~extd_automata(){};
    void print_dot();
    void print();
};

#endif