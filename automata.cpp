#include "automata.h"
#include "carsolver.h"
#include "smtsolver.h"
#include <queue>
#include <unordered_map>
#include <string>
#include <cstdio>
#include <iostream>
#include <map>

typedef unsigned long long int ull;
using namespace std;
using namespace aalta;

int automata::until_num = 0;
bool automata::U_flag = false;

aalta_formula *trans::remove_tag_get_acc(aalta_formula *s)
{
    if (s == NULL)
        return s;
    int op = s->oper();
    if(op==aalta::aalta_formula::Not)
    {
        string tmp = (s->r_af()) ->to_string();
        if (tmp.substr(0,3) == "_AC")
            return NULL;
        else
            return s;
    }
    if (op >= 11)
    {
        string tmp = s->to_string();
        if (tmp.substr(0,3) == "_AC")
        {
            acc_cdt.erase(stoi(tmp.substr(3, tmp.find('_', 1) - 2)));
            return NULL;
        }
        else
            return s;
    }
    aalta_formula *l = remove_tag_get_acc(s->l_af());
    aalta_formula *r = remove_tag_get_acc(s->r_af());
    if(l==NULL&&r==NULL) return NULL;
    return aalta_formula(op, l, r).unique();
}
trans::trans(aalta::aalta_formula *l, int n, bool remove_tag, const int &acc_num)
{
    next = n;
    if (!remove_tag)
    {
        label = l;
        return;
    }
    for (int i = 0; i < acc_num; i++)
        acc_cdt.insert(i);
    //cout<<l->to_string()<<endl;
    label = remove_tag_get_acc(l);
    if (label == NULL)
        label = aalta_formula(aalta_formula::True, NULL, NULL).unique();
    //cout<<"dgb  0="<<label->to_string()<<endl;
}
void trans::print_nxt_acc(bool dot)
{
    if(!dot) printf(" %d", next);
    if (acc_cdt.size() == 0)
        return;
    set<int>::iterator it = acc_cdt.begin();
    printf(" {%d", *it);
    for (++it; it != acc_cdt.end(); ++it)
        printf(" %d", *it);
    putchar('}');
}

void trans::print_trans()
{
    cout << "  " << label->to_string() << " to state " << next << '\n';
}

int trans::get_level(int j,int m)
{
    if(j==m) return 0;
    else if(j<m&&acc_cdt.find(j)!=acc_cdt.end()) return j+1;
    else return j;
}

state::~state()
{
    for (int i = 0; i < trans_set.size(); i++)
        delete trans_set[i];
}

void state::add_trans(trans *t)
{
    trans_set.push_back(t);
    lth++;
}

void state::print_state()
{
    cout << "state " << sid << ": " << property->to_string() << '\n';
    for (int i = 0; i < trans_set.size(); i++)
    {
        trans_set[i]->print_trans();
    }
}

void state::arrive()
{
    accessible=true;
}

transition_system::transition_system(aalta_formula *src_f)
{
    //cout << "Get transition system for: " << src_f->to_string() << '\n';
    queue<aalta_formula *> to_process;
    unordered_map<ull, int> existing;
    to_process.push(src_f);
    existing[ull(src_f)] = states.size();
    state *ptr_s;
    ptr_s = new state(states.size(), src_f);
    states.push_back(ptr_s);
    Transition *t;
    while (!to_process.empty())
    {
        aalta_formula *cur;
        cur = to_process.front();
        aalta::CARSolver *solve = new aalta::CARSolver(cur);
        //cout << "Solver for: " << cur->to_string() << '\n';
        while (true)
        {
            bool res = solve->solve_by_assumption(cur);
            if (!res)
            {
                to_process.pop();
                break;
            }
            t = solve->get_transition();
            //cout << "trans: " << (t->label())->to_string() << " to " << (t->next())->to_string() << '\n';

            //solve->block_formula(t->next());
            //cout << "block: " << (t->next())->to_string() << '\n';
            if (existing.find(ull(t->next())) == existing.end())
            {
                to_process.push(t->next());
                existing[ull(t->next())] = states.size();
                ptr_s = new state(states.size(), t->next());
                states.push_back(ptr_s);
            }
            trans *new_trans = new trans(t->label(), existing[ull(t->next())]);
            states[existing[ull(cur)]]->add_trans(new_trans);
            delete t;
        }
        delete solve;
    }
}

transition_system::~transition_system()
{
    for (int i = 0; i < states.size(); i++)
        delete states[i];
}

void transition_system::print()
{
    for (int i = 0; i < states.size(); i++)
    {
        states[i]->print_state();
    }
}

aalta_formula *automata::add_acc_tag(aalta_formula *s)
{
    if (s == NULL)
        return s;
    int op = s->oper();
    if (op >= 11)
    {
        if (ap_map.find(s->to_string()) == ap_map.end())
        {
            ap_map[s->to_string()] = ap_num++;
            aps.push_back(s->to_string());
        }
        return s;
    }
    if (op == aalta_formula::True || op == aalta_formula::False)
        return s;
    aalta_formula *l = add_acc_tag(s->l_af());
    aalta_formula *r = add_acc_tag(s->r_af());
    if (op == aalta_formula::Until)
    {
        automata::U_flag = true;
        string tag_s = "_AC" + to_string(automata::until_num) + "_" /*+ r->to_string()*/;
        automata::until_num++;
        aalta_formula *tag_f = aalta_formula(tag_s.c_str()).unique();
        l = aalta_formula(aalta_formula::And, l, tag_f).unique();
    }
    if (automata::U_flag)
        s = aalta_formula(op, l, r).unique();
    return s;
}

automata::automata(aalta_formula *src_f,bool ba)
    : is_ba(ba),transition_system()
{
    src_formula=src_f->to_string();
    if(!ba)
    {
        ap_num = 0;
        state *ptr_s;
        ptr_s = new state(states.size(), src_f);
        states.push_back(ptr_s);
        src_f = add_acc_tag(src_f)->simplify();
        src_f=src_f->simplify();
        //cout << "Get automata for: " << src_f->to_string() << '\n';
        queue<aalta_formula *> to_process;
        unordered_map<ull, int> existing;
        to_process.push(src_f);
        existing[ull(src_f)] = existing.size();

        Transition *t;
        while (!to_process.empty())
        {
            aalta_formula *cur;
            cur = to_process.front();
            if (cur->oper() == aalta_formula::False)
            {
                to_process.pop();
                continue;
            }
            aalta::CARSolver *solve = new aalta::CARSolver(cur);
            //cout << "Solver for: " << cur->to_string() << '\n';
            while (true)
            {
                bool res = solve->solve_by_assumption(cur);
                if (!res)
                {
                    to_process.pop();
                    break;
                }
                t = solve->get_transition();
                //cout << "trans: " << (t->label())->to_string() << " to " << (t->next())->to_string() << '\n';

                //solve->block_formula(t->next());
                //cout << "block: " << (t->next())->to_string() << '\n';

                if (existing.find(ull(t->next())) == existing.end())
                {
                    to_process.push(t->next());
                    existing[ull(t->next())] = states.size();
                    ptr_s = new state(states.size(), t->next());
                    states.push_back(ptr_s);
                }

                trans *new_trans = new trans(t->label(), existing[ull(t->next())], true, automata::until_num);
                states[existing[ull(cur)]]->add_trans(new_trans);
                delete t;
            }
            delete solve;
        }
    }
    else
    {
        ap_num = 0;
        src_f = add_acc_tag(src_f)->simplify();
        state *ptr_s;
        for(int i=0;i<=automata::until_num;i++)
        {
            ptr_s = new state(states.size(), src_f,i);
            states.push_back(ptr_s);
        }
        
        queue<aalta_formula *> to_process;
        unordered_map<ull, int> existing;
        to_process.push(src_f);
        existing[ull(src_f)] = existing.size();

        Transition *t;
        while (!to_process.empty())
        {
            aalta_formula *cur;
            cur = to_process.front();
            if (cur->oper() == aalta_formula::False)
            {
                to_process.pop();
                continue;
            }
            aalta::CARSolver *solve = new aalta::CARSolver(cur);
            //cout << "Solver for: " << cur->to_string() << '\n';
            while (true)
            {
                bool res = solve->solve_by_assumption(cur);
                if (!res)
                {
                    to_process.pop();
                    break;
                }
                t = solve->get_transition();
                //cout << "trans: " << (t->label())->to_string() << " to " << (t->next())->to_string() << '\n';

                //solve->block_formula(t->next());
                //cout << "block: " << (t->next())->to_string() << '\n';

                if (existing.find(ull(t->next())) == existing.end())
                {
                    to_process.push(t->next());
                    existing[ull(t->next())] = existing.size();
                    for(int i=0;i<=automata::until_num;i++)
                    {
                        ptr_s = new state(states.size(), t->next(),i);
                        states.push_back(ptr_s);
                    }
                }
                trans *new_trans = new trans(t->label(), existing[ull(t->next())], true, automata::until_num);
                for(int j=0;j<=automata::until_num;j++)
                {
                    trans *tr=new trans(new_trans->get_label(),new_trans->get_level(j,automata::until_num)+(automata::until_num+1)*existing[ull(t->next())]);
                    states[existing[ull(cur)]*(automata::until_num+1)+j]->add_trans(tr);
                }
                delete new_trans;
                delete t;
            }
            delete solve;
        }
        queue<int> able;
        states[0]->arrive();
        able.push(0);
        while(!able.empty())
        {
            int f=able.front();
            for(int k=0;k<states[f]->length();k++)
            {
                if(!(states[(states[f]->get_trans(k))->get_next()]->can_get()))
                {
                    states[(states[f]->get_trans(k))->get_next()]->arrive();
                    able.push((states[f]->get_trans(k))->get_next());
                }
            }
            able.pop();
        }
        for(int i=0;i<states.size();i++)
            if(!(states[i]->can_get()))
                remove_state(i--);
    }
}

void automata::label2int(aalta_formula *lb, vector<int> &v)
{
    if (lb == NULL)
        return;
    int op = lb->oper();
    if (op >= 11)
    {
        //cout<<"dbg2: "<<lb->to_string()<<": "<<ap_map[lb->to_string()]<<endl;
        v.push_back(ap_map[lb->to_string()]);
        return;
    }
    else if (op == aalta_formula::Not)
    {
        int tmp = ap_map[(lb->r_af())->to_string()];
        if (tmp == 0)
            v.push_back(ap_num);
        else
            v.push_back(-1 * tmp);
        return;
    }
    label2int(lb->l_af(), v);
    label2int(lb->r_af(), v);
}

void automata::print_label_numeric(aalta::aalta_formula *lb)
{
    if (lb->oper() == aalta_formula::True)
    {
        printf("[t]");
        return;
    }
    //cout<<"dbg1: "<<lb->to_string()<<endl;
    vector<int> v;
    label2int(lb, v);
    if (v.size() == 0)
    {
        printf("[t]");
        return;
    }
    printf("[");
    //cout<<v.size()<<endl;
    for (int i = 0; i < int(v.size()) - 1; i++)
    {
        if (v[i] == ap_num)
            printf("!0&");
        else if (v[i] >= 0)
            printf("%d&", v[i]);
        else
            printf("!%d&", -v[i]);
    }
    if (v.size() > 0)
    {
        if (v[v.size() - 1] == ap_num)
            printf("!0]");
        else if (v[v.size() - 1] < 0)
            printf("!%d]", -v[v.size() - 1]);
        else
            printf("%d]", v[v.size() - 1]);
    }
}

void automata::print_dot()
{
    printf("digraph \"%s\" {\n  rankdir=LR\n  ",(((states[0])->get_property())->to_string()).c_str());
    printf("label=\"formula: %s\\nAP %d",src_formula.c_str(),ap_num);
    vector<string>::iterator it = aps.begin();
    for (; it != aps.end(); ++it)
        printf(" \\\"%s\\\"", (*it).c_str());
    printf("\\n[");
    if(!is_ba)
    {
        printf("generalized Büchi]\\n");
        printf("Acceptance: ");
        if (until_num == 0)
            printf("t\n");
        else
        {
            for (int i = 0; i < until_num - 1; i++)
                printf("Inf(%d)&", i);
            if (until_num > 0)
                printf("Inf(%d)\\n", until_num - 1);
            else
                printf("\\n");
        }
    }
    else printf("Büchi]");
    printf("\"\n  labelloc=\"t\"\n  node [shape=\"circle\"]\n  I [label=\"\", style=invis, width=0]\n  I -> 0\n");
    
    for (int i = 0; i < states.size(); i++)
    {
        printf("  %d [label=\"%d\"",i,i);
        if(is_ba&&states[i]->get_level()==automata::until_num)
            printf(", peripheries=2");
        printf("]\n");

        trans *temp;
        int len = states[i]->length();
        for (int j = 0; j < len; j++)
        {
            temp = states[i]->get_trans(j);
            printf("  %d -> %d [label=\"",i,temp->get_next());
            print_label_numeric((temp->get_label())->nnf());
            if(!is_ba) temp->print_nxt_acc(true);
            printf("\"]\n");
        }
    }
    printf("}\n");
}

void automata::print()
{
    printf("HOA: v1\nname: \"%s\"\n",src_formula.c_str());
    printf("States: %lu\nStart: %d\n", states.size(), 0);
    vector<string>::iterator it = aps.begin();
    printf("AP: %d", ap_num);
    for (; it != aps.end(); ++it)
        printf(" \"%s\"", (*it).c_str());
    if(!is_ba)
    {
        printf("\nacc-name: generalized-Buchi %d\n", until_num);
        printf("Acceptance: %d ", until_num);
        if (until_num == 0)
            printf("t\n");
        else
        {
            for (int i = 0; i < until_num - 1; i++)
                printf("Inf(%d)&", i);
            if (until_num > 0)
                printf("Inf(%d)\n", until_num - 1);
            else
                putchar('\n');
        }
        printf("properties: trans-labels explicit-labels trans-acc\n--BODY--\n");
    }
    else
    {
        printf("\nacc-name: Buchi\n");
        printf("Acceptance: 1 Inf(0)\n");
        printf("properties: trans-labels explicit-labels state-acc\n--BODY--\n");
    }
    for (int i = 0; i < states.size(); i++)
    {
        if(is_ba)
        {
            printf("State: %d", i);
            if(states[i]->get_level()==automata::until_num) printf("{0}");
            putchar('\n');
        }
        else printf("State: %d\n", i);
        trans *temp;
        int len = states[i]->length();
        for (int j = 0; j < len; j++)
        {
            temp = states[i]->get_trans(j);
            //cout<<(temp->get_label())->to_string()<<endl;
            print_label_numeric((temp->get_label())->nnf());
            if(!is_ba) temp->print_nxt_acc();
            else printf(" %d",temp->get_next());
            putchar('\n');
        }
    }
    printf("--END--\n");
}

void automata::remove_state(int idx)
{
    delete states[idx];
    states.erase(states.begin()+idx);
    for(int i=0;i<states.size();i++)
    {
        state *st=states[i];
        for(int j=0;j<(st->length());j++)
        {
            trans* tt=st->get_trans(j);
            if((tt->get_next())>=idx)
                tt->update_next(-1);
        }
    }
}

aalta_formula *extd_automata::pre_process(string s)
{
    char c='"';
    int b=s.find(c);
    int idx=0;
    while(b!=-1)
    {
        int e=s.find(c,b+1);
        string tmp=s.substr(b+1,e-b-1);
        map<string,string>::iterator it;
        for(it=ap2smt.begin();it!=ap2smt.end();++it)
            if((*it).second==tmp) break;
        if(it==ap2smt.end())
        {
            string p="_smt"+to_string(idx++);
            ap2smt[p]=s.substr(b+1,e-b-1);
            s=s.replace(b,e-b+1,p);
        }
        else
        {
            s=s.replace(b,e-b+1,(*it).first);
        }
        b=s.find(c);
    }
    aalta_formula *f=aalta_formula(s.c_str()).unique();
    f = f->nnf();
    f = f->simplify();
    f = f->split_next();
    return f;
}

extd_automata::extd_automata(string s,bool ba)
    : automata()
{
    is_ba=ba;
    int cc=0;
    src_formula=s;
    if(!ba)
    {
        unknow=false;
        aalta_formula *src_f=pre_process(s);
        //cout<<src_f->to_string()<<"\n";
        ap_num=0;
        state *ptr_s;
        ptr_s = new state(states.size(), src_f);
        states.push_back(ptr_s);
        src_f = add_acc_tag(src_f)->simplify();
        queue<aalta_formula *> to_process;
        unordered_map<ull, int> existing;
        to_process.push(src_f);
        existing[ull(src_f)] = existing.size();

        Transition *t;
        while (!to_process.empty())
        {
            aalta_formula *cur;
            cur = to_process.front();
            if (cur->oper() == aalta_formula::False)
            {
                to_process.pop();
                continue;
            }
            //cout<<"state "<<cc++<<endl;
            smtSolver *solve = new smtSolver(cur,ap2smt);
            //cout << "Solver for: " << cur->to_string() << '\n';
            while (true)
            {
                z3::check_result res = solve->check_sat();
                if (res!=z3::sat)
                {
                    if ((!unknow)&& (res==z3::unknown)) unknow=true;
                    to_process.pop();
                    break;
                }
                t = solve->get_trans();
                //cout << "trans: " << (t->label())->to_string() << " to " << (t->next())->to_string() << '\n';
                if (existing.find(ull(t->next())) == existing.end())
                {
                    to_process.push(t->next());
                    existing[ull(t->next())] = states.size();
                    ptr_s = new state(states.size(), t->next());
                    states.push_back(ptr_s);
                }

                trans *new_trans = new trans(t->label(), existing[ull(t->next())], true, automata::until_num);
                states[existing[ull(cur)]]->add_trans(new_trans);
                delete t;
            }
            delete solve;
        }
        for(int i=0;i<states.size();i++)
            if(states[i]->length()==0)
                remove_state(i--);
    }
    else
    {
        unknow=false;
        aalta_formula *src_f=pre_process(s);
        //cout<<src_f->to_string()<<"\n";
        ap_num=0;
        src_f = add_acc_tag(src_f)->simplify();
        state *ptr_s;
        for(int i=0;i<=automata::until_num;i++)
        {
            ptr_s = new state(states.size(), src_f,i);
            states.push_back(ptr_s);
        }
        queue<aalta_formula *> to_process;
        unordered_map<ull, int> existing;
        to_process.push(src_f);
        existing[ull(src_f)] = existing.size();

        Transition *t;
        while (!to_process.empty())
        {
            aalta_formula *cur;
            cur = to_process.front();
            if (cur->oper() == aalta_formula::False)
            {
                to_process.pop();
                continue;
            }
            smtSolver *solve = new smtSolver(cur,ap2smt);
            //cout << "Solver for: " << cur->to_string() << '\n';
            while (true)
            {
                z3::check_result res = solve->check_sat();
                if (res!=z3::sat)
                {
                    if ((!unknow)&& (res==z3::unknown)) unknow=true;
                    to_process.pop();
                    break;
                }
                t = solve->get_trans();
                //cout << "trans: " << (t->label())->to_string() << " to " << (t->next())->to_string() << '\n';
                if (existing.find(ull(t->next())) == existing.end())
                {
                    to_process.push(t->next());
                    existing[ull(t->next())] = existing.size();
                    for(int i=0;i<=automata::until_num;i++)
                    {
                        ptr_s = new state(states.size(), t->next(),i);
                        states.push_back(ptr_s);
                    }
                }

                trans *new_trans = new trans(t->label(), existing[ull(t->next())], true, automata::until_num);
                for(int j=0;j<=automata::until_num;j++)
                {
                    trans *tr=new trans(new_trans->get_label(),new_trans->get_level(j,automata::until_num)+(automata::until_num+1)*existing[ull(t->next())]);
                    states[existing[ull(cur)]*(automata::until_num+1)+j]->add_trans(tr);
                }
                delete new_trans;
                delete t;
            }
            delete solve;
        }
        queue<int> able;
        states[0]->arrive();
        able.push(0);
        while(!able.empty())
        {
            int f=able.front();
            for(int k=0;k<states[f]->length();k++)
            {
                if(!(states[(states[f]->get_trans(k))->get_next()]->can_get()))
                {
                    states[(states[f]->get_trans(k))->get_next()]->arrive();
                    able.push((states[f]->get_trans(k))->get_next());
                }
            }
            able.pop();
        }
        for(int i=0;i<states.size();i++)
            if((!(states[i]->can_get()))||(states[i]->length()==0))
                remove_state(i--);
    }
}

void extd_automata::print()
{
    printf("HOA: v1\nname: \"%s\"\n", src_formula.c_str());
    printf("States: %lu\nStart: %d\n", states.size(), 0);
    vector<string>::iterator it = aps.begin();
    printf("AP: %d", ap_num);
    for (; it != aps.end(); ++it)
    {
        if((*it).substr(0,4)=="_smt")
            printf(" \"%s\"", ap2smt[(*it)].c_str());
        else
            printf(" \"%s\"", (*it).c_str());
    }
    if(!is_ba)
    {
        printf("\nacc-name: generalized-Buchi %d\n", until_num);
        printf("Acceptance: %d ", until_num);
        if (until_num == 0)
            printf("t\n");
        else
        {
            for (int i = 0; i < until_num - 1; i++)
                printf("Inf(%d)&", i);
            if (until_num > 0)
                printf("Inf(%d)\n", until_num - 1);
            else
                putchar('\n');
        }
        printf("properties: trans-labels explicit-labels trans-acc\n--BODY--\n");
    }
    else
    {
        printf("\nacc-name: Buchi\n");
        printf("Acceptance: 1 Inf(0)\n");
        printf("properties: trans-labels explicit-labels state-acc\n--BODY--\n");
    }
    for (int i = 0; i < states.size(); i++)
    {
        if(is_ba)
        {
            printf("State: %d", i);
            if(states[i]->get_level()==automata::until_num) printf("{0}");
            putchar('\n');
        }
        else printf("State: %d\n", i);
        trans *temp;
        int len = states[i]->length();
        for (int j = 0; j < len; j++)
        {
            temp = states[i]->get_trans(j);
            //cout<<(temp->get_label())->to_string()<<endl;
            print_label_numeric((temp->get_label())->nnf());
            if(!is_ba) temp->print_nxt_acc();
            else printf(" %d",temp->get_next());
            putchar('\n');
        }
    }
    printf("--END--\n");
    if(unknow)
        printf("/*The automaton is probably incomplete because of the limitation of the SMT solver's capabilities. *//n");
}

void extd_automata::print_dot()
{
    printf("digraph \"%s\" {\n  rankdir=LR\n  ",src_formula.c_str());
    printf("label=\"formula: %s\\nAP %d",(((states[0])->get_property())->to_string()).c_str(),ap_num);
    vector<string>::iterator it = aps.begin();
    for (; it != aps.end(); ++it)
    {
        if((*it).substr(0,4)=="_smt")
            printf(" \\\"%s\\\"", ap2smt[(*it)].c_str());
        else
            printf(" \\\"%s\\\"", (*it).c_str());
    }
    printf("\\n[");
    if(!is_ba)
    {
        printf("generalized Büchi]\\n");
        printf("Acceptance: ");
        if (until_num == 0)
            printf("t\n");
        else
        {
            for (int i = 0; i < until_num - 1; i++)
                printf("Inf(%d)&", i);
            if (until_num > 0)
                printf("Inf(%d)\\n", until_num - 1);
            else
                printf("\\n");
        }
    }
    else printf("Büchi]");
    printf("\"\n  labelloc=\"t\"\n  node [shape=\"circle\"]\n  I [label=\"\", style=invis, width=0]\n  I -> 0\n");
    
    for (int i = 0; i < states.size(); i++)
    {
        printf("  %d [label=\"%d\"",i,i);
        if(is_ba&&states[i]->get_level()==automata::until_num)
            printf(", peripheries=2");
        printf("]\n");

        trans *temp;
        int len = states[i]->length();
        for (int j = 0; j < len; j++)
        {
            temp = states[i]->get_trans(j);
            printf("  %d -> %d [label=\"",i,temp->get_next());
            print_label_numeric((temp->get_label())->nnf());
            if(!is_ba) temp->print_nxt_acc(true);
            printf("\"]\n");
        }
    }
    printf("}\n");
}