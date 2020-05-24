#include "smtsolver.h"
#include <z3++.h>
#include "utility.h"
#include <vector>
#include <stack>

using namespace std;

void del_space(string & s)
{
    if(s.length()==0) return;
    int a=s.find_first_not_of(' ');
    int b=s.find_last_not_of(' ');
    if(a==-1||b==-1){s=""; return;}
    s=s.substr(a,b-a+1);
}
aalta::aalta_formula* smtSolver::xnf(aalta::aalta_formula* f)
{
    if(s==NULL) return f;
    int op=f->oper();
    if(op==aalta::aalta_formula::True||op==aalta::aalta_formula::False||op>=11)
    {
        string temp=f->to_string();
        if(atom_idx.find(temp)==atom_idx.end())
        {
            atom_idx[temp]=atom.size();
            atom.push_back(c.bool_const(temp.c_str()));
        }
        return f;
    }
    if(op==aalta::aalta_formula::Not)
    {
        string temp=(f->r_af())->to_string();
        {
            atom_idx[temp]=atom.size();
            atom.push_back(c.bool_const(temp.c_str()));
        }
        return f;
    }
    if(op==aalta::aalta_formula::Next)
    {
        map<string,aalta::aalta_formula*>::iterator it;
        it=next_ap.begin();
        aalta::aalta_formula* taf=(f->r_af())->unique();
        for(;it!=next_ap.end();++it)
            if((it->second)==taf) break;
        if(it==next_ap.end())
        {
            string temp="_x"+to_string(x_num++);
            next_ap[temp]=taf;
            atom_idx[temp]=atom.size();
            atom.push_back(c.bool_const(temp.c_str()));
            return aalta::aalta_formula(temp.c_str()).unique();
        }
        else
            return aalta::aalta_formula((it->first).c_str()).unique();
    }
    aalta::aalta_formula *l=xnf(f->l_af());
    aalta::aalta_formula *r=xnf(f->r_af());
    if(op==aalta::aalta_formula::And||op==aalta::aalta_formula::Or)
        return aalta::aalta_formula(op,l,r).unique();
    
    map<string,aalta::aalta_formula*>::iterator it;
    it=next_ap.begin();
    aalta::aalta_formula* taf=f->unique();
    for(;it!=next_ap.end();++it)
        if((it->second)==taf) break;
    aalta::aalta_formula *x;
    if(it==next_ap.end())
    {
        string temp="_x"+to_string(x_num++);
        next_ap[temp]=taf;
        atom_idx[temp]=atom.size();
        atom.push_back(c.bool_const(temp.c_str()));
        x=aalta::aalta_formula(temp.c_str()).unique();
    }
    else
        x=aalta::aalta_formula((it->first).c_str()).unique();

    if(op==aalta::aalta_formula::Until)
        return aalta::aalta_formula(aalta::aalta_formula::Or,r,aalta::aalta_formula(aalta::aalta_formula::And,l,x).unique()).unique();
    else if(op==aalta::aalta_formula::Release)
        return aalta::aalta_formula(aalta::aalta_formula::And,r,aalta::aalta_formula(aalta::aalta_formula::Or,l,x).unique()).unique();
}

bool last_token_num=false;
bool is_letter(char c){return c=='_'||(c>='a'&&c<='z')||(c>='A'&&c<='Z');}
bool is_digit(char c){return c>='0'&&c<='9';}

token_type next_token(string &src,string &token)
{
	del_space(src);
    if(src.length()==0) return blank;
    if(src[0]=='('||src[0]==')'||src[0]=='*'||src[0]=='/'||src[0]=='+'||src[0]=='%')
    {
		if(src[0]==')') last_token_num=true;
        else last_token_num=false;
        token=src.substr(0,1);
		src.erase(0,1);
		return operate;
	}
	else if(src[0]=='-')
    {
        int st=src.find_first_not_of(' ',1);
        char c=src[st];
        if(c>='0'&&c<='9'&&(!last_token_num))
        {
            int ed=st;
            for(;(ed+1)<src.length()&&src[ed+1]>='0'&&src[ed+1]<='9';ed++);
            token="-"+src.substr(st,ed-st+1);
            src=src.substr(ed+1);
            last_token_num=true;
            return number;
        }
        else
        {
            last_token_num=false;
            token=src.substr(0,1);
            src.erase(0,1);
            return operate;
        }
        
    }
    else if(is_letter(src[0]))
    {
        last_token_num=true;
        int ed=0;
        for(;(ed+1)<src.length()&&(is_letter(src[ed+1])||is_digit(src[ed+1]));ed++);
        token=src.substr(0,ed+1);
        src=src.substr(ed+1);
        return ident;
    }
    else if(is_digit(src[0]))
    {
        last_token_num=true;
        int ed=0;
        for(;(ed+1)<src.length()&&is_digit(src[ed+1]);ed++);
        token=src.substr(0,ed+1);
        src=src.substr(ed+1);
        return number;
    }
}

bool is_number(string &s)
{
    char c=s[0];
    return c!='('&&c!=')'&&c!='+'&&(c!='-'||(c=='-'&&s.length()>1))&&c!='*'&&c!='/'&&c!='%';
}

z3::expr smtSolver::get_arith_expr(string arith,bool &only_num,int &re)
{
    string token;
    token_type typ;
    typ=next_token(arith,token);
    vector<string> inv_bl;
    stack<char> op;
    vector<z3::expr> res;
    while(typ!=blank)
    {
        if(typ==ident||typ==number)
            inv_bl.push_back(token);
        else if(typ==operate)
        {
            switch (token[0])
            {
                case '(':
                    op.push('(');
                    break;
                case ')':
                    while((!op.empty())&&(op.top()!='('))
                    {
                        inv_bl.push_back(string(1,op.top()));
                        op.pop();
                    }
                    break;
                case '+': case '-':
                    while((!op.empty())&&(op.top()!='('))
                    {
                        inv_bl.push_back(string(1,op.top()));
                        op.pop();
                    }
                    op.push(token[0]);
                    break;
                case '*': case '/': case '%':
                    while((!op.empty())&&(op.top()=='*'||op.top()=='/'||op.top()=='%'))
                    {
                        inv_bl.push_back(string(1,op.top()));
                        op.pop();
                    }
                    op.push(token[0]);
                    break;
            }
        }
        typ=next_token(arith,token);
    }
    while (!op.empty())
    {
        inv_bl.push_back(string(1,op.top()));
        op.pop();
    }
    if(inv_bl.size()==1)
    {
        if(is_letter(inv_bl[0][0]))
        {
            if(intvar_idx.find(inv_bl[0])==intvar_idx.end())
            {
                intvar_idx[inv_bl[0]]=intvar.size();
                intvar.push_back(c.int_const(inv_bl[0].c_str()));
            }
            return intvar[intvar_idx[inv_bl[0]]];   
        }
        else
        {
            only_num=true;
            re=stoi(inv_bl[0]);
            return c.int_const(("null"+to_string(nu++)).c_str());
        }
    }
    stack<string> num;
    vector<string>::iterator it;
    for(it=inv_bl.begin();it!=inv_bl.end();++it)
    {
        if(is_number(*it))
        {
            num.push((*it));
            continue;
        }
        string left,right,ope;
        ope=(*it);
        right=(num.top());
        num.pop();
        left=(num.top());
        num.pop();
        if(is_letter(left[0])&&is_letter(right[0]))
        {
            if(left.substr(0,6)=="z3expr"&&right.substr(0,6)=="z3expr")
            {
                z3::expr left_=res[stoi(left.substr(6))];
                z3::expr right_=res[stoi(right.substr(6))];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            else if(left.substr(0,6)=="z3expr"&&right.substr(0,6)!="z3expr")
            {
                z3::expr left_=res[stoi(left.substr(6))];
                if(intvar_idx.find(right)==intvar_idx.end())
                {
                    intvar_idx[right]=intvar.size();
                    intvar.push_back(c.int_const(right.c_str()));
                }
                z3::expr right_=intvar[intvar_idx[right]];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            else if(left.substr(0,6)!="z3expr"&&right.substr(0,6)=="z3expr")
            {
                z3::expr right_=res[stoi(right.substr(6))];
                if(intvar_idx.find(left)==intvar_idx.end())
                {
                    intvar_idx[left]=intvar.size();
                    intvar.push_back(c.int_const(left.c_str()));
                }
                z3::expr left_=intvar[intvar_idx[left]];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            else
            {
                if(intvar_idx.find(left)==intvar_idx.end())
                {
                    intvar_idx[left]=intvar.size();
                    intvar.push_back(c.int_const(left.c_str()));
                }
                z3::expr left_=intvar[intvar_idx[left]];
                if(intvar_idx.find(right)==intvar_idx.end())
                {
                    intvar_idx[right]=intvar.size();
                    intvar.push_back(c.int_const(right.c_str()));
                }
                z3::expr right_=intvar[intvar_idx[right]];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
        }
        else if(is_letter(left[0])&&(!is_letter(right[0])))
        {
            if(left.substr(0,6)=="z3expr")
            {
                z3::expr left_=res[stoi(left.substr(6))];
                int right_=stoi(right);
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            else
            {
                if(intvar_idx.find(left)==intvar_idx.end())
                {
                    intvar_idx[left]=intvar.size();
                    intvar.push_back(c.int_const(left.c_str()));
                }
                z3::expr left_=intvar[intvar_idx[left]];
                int right_=stoi(right);
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            
        }
        else if((!is_letter(left[0]))&&is_letter(right[0]))
        {
            int left_=stoi(left);
            if(right.substr(0,6)=="z3expr")
            {
                z3::expr right_=res[stoi(right.substr(6))];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
            else
            {
                if(intvar_idx.find(right)==intvar_idx.end())
                {
                    intvar_idx[right]=intvar.size();
                    intvar.push_back(c.int_const(right.c_str()));
                }
                z3::expr right_=intvar[intvar_idx[right]];
                num.push(("z3expr"+to_string(res.size())));
                switch(ope[0])
                {
                    case '+': res.push_back(left_ + right_); break;
                    case '-': res.push_back(left_ - right_); break;
                    case '*': res.push_back(left_ * right_); break;
                    case '/': res.push_back(left_ / right_); break;
                    case '%': res.push_back(left_ % right_); break;
                }
            }
        }
        else if((!is_letter(left[0]))&&(!is_letter(right[0])))
        {
            int left_=stoi(left);
            int right_=stoi(right);
            switch(ope[0])
            {
                case '+': num.push((to_string(left_ + right_))); break;
                case '-': num.push((to_string(left_ - right_))); break;
                case '*': num.push((to_string(left_ * right_))); break;
                case '/': num.push((to_string(left_ / right_))); break;
                case '%': num.push((to_string(left_ % right_))); break;
            }
        }
    }
    if(res.size()==0)
    {
        only_num=true;
        re=stoi((num.top()));
        return c.int_const(("null"+to_string(nu++)).c_str());
    }
    return res[stoi(((num.top())).substr(6))];
}

//>:0,>=:1,<:2,<=:3,==:4
z3::expr smtSolver::get_full_arith_expr(string arith)
{
    //cout<<arith<<endl;
    int op_p,op;
    string var,con;
    if((op_p=arith.find('>'))!=-1)
    {
        var=arith.substr(0,op_p);
        if((op_p=arith.find('='))!=-1)
            op=1;
        else
        {
            op=0;
            op_p=arith.find('>');
        }
        con=arith.substr(op_p+1);
    }
    else if((op_p=arith.find('<'))!=-1)
    {
        var=arith.substr(0,op_p);
        if((op_p=arith.find('='))!=-1)
            op=3;
        else
        {
            op=2;
            op_p=arith.find('<');
        }
        con=arith.substr(op_p+1);
    }
    else
    {
        op_p=arith.find('=');
        var=arith.substr(0,op_p);
        con=arith.substr(op_p+2);
        op=4;
    }
    del_space(var);
    del_space(con);
    bool l_isn=false,r_isn=false;
    int l_vl,r_vl;
    z3::expr left_=get_arith_expr(var,l_isn,l_vl);
    z3::expr right_=get_arith_expr(con,r_isn,r_vl);
    if(!l_isn&&!r_isn)
    {
        switch (op)
        {
        case 0:
            return (left_ > right_);
        case 1:
            return (left_ >= right_);
        case 2:
            return (left_ < right_);
        case 3:
            return (left_ <= right_);
        case 4:
            return (left_ == right_);
        }
    }
    else if(!l_isn&&r_isn)
    {
        switch (op)
        {
        case 0:
            return (left_ > r_vl);
        case 1:
            return (left_ >= r_vl);
        case 2:
            return (left_ < r_vl);
        case 3:
            return (left_ <= r_vl);
        case 4:
            return (left_ == r_vl);
        }
    }
    else if(l_isn&&!r_isn)
    {
        switch (op)
        {
        case 0:
            return (l_vl > right_);
        case 1:
            return (l_vl >= right_);
        case 2:
            return (l_vl < right_);
        case 3:
            return (l_vl <= right_);
        case 4:
            return (l_vl == right_);
        }
    }
}

z3::expr smtSolver::get_assertion(aalta::aalta_formula* f,map<string,string> & ap2smt)
{
    int op=f->oper();
    if(op==aalta::aalta_formula::True)
    {
        z3::expr t=atom[atom_idx[f->to_string()]];
        assertion.push_back(t);
        return t;
    }
    else if(op==aalta::aalta_formula::False)
    {
        z3::expr f_=atom[atom_idx[f->to_string()]];
        assertion.push_back((! f_));
        return f_;
    }
    else if(op>=11)
    {
        if((f->to_string()).substr(0,4)=="_smt"){
            //cout<<"add: "<<(atom[atom_idx[f->to_string()]] == get_full_arith_expr(ap2smt[f->to_string()]))<<endl;
            s.add(atom[atom_idx[f->to_string()]] == get_full_arith_expr(ap2smt[f->to_string()]));
        }
            
        return atom[atom_idx[f->to_string()]];
    }
    else if(op==aalta::aalta_formula::Not)
        return ((! get_assertion(f->r_af(),ap2smt)));
    else if(op==aalta::aalta_formula::Or)
        return ((get_assertion(f->l_af(),ap2smt)) || (get_assertion(f->r_af(),ap2smt)));
    else if(op==aalta::aalta_formula::And)
    {
        z3::expr l_=get_assertion(f->l_af(),ap2smt);
        z3::expr r_=get_assertion(f->r_af(),ap2smt);
        if((f->r_af())->to_string().substr(0,3)=="_AC")
            s.add(l_ == r_);
        return l_ && r_;
    }
        //return (() && (get_assertion(f->r_af(),ap2smt)));
    //return c.bool_const("test2");
}

smtSolver::smtSolver(aalta::aalta_formula *f,map<string,string> & ap2smt)
: s(z3::solver(c))
{
    x_num=0;
    z3::context c;
    f=xnf(f);
    //cout<<f->to_string()<<endl;
    z3::expr src=get_assertion(f,ap2smt);
    //cout<<"add: "<<src<<endl;
    s.add(src);
    vector<z3::expr>::iterator it=assertion.begin();
    for(;it!=assertion.end();++it)
    {
        //cout<<"add: "<<(*it)<<endl;
        s.add(*it);
    }
}

aalta::Transition *smtSolver::get_trans()
{
    vector<aalta::aalta_formula*> labels,nexts;
    vector<z3::expr> to_block;
    z3::model m=s.get_model();
    //cout<<m<<endl;
    for(int i=0;i<m.size();i++)
    {
        z3::func_decl v=m[i];
        //assert(v.arity() == 0);
        if(((m.get_const_interp(v)).to_string())[0]=='t')
        {
            string tmp=(v.name()).str();
            if(tmp=="true")
                labels.push_back(aalta::aalta_formula("1").unique());
            else if(tmp[0]=='_'&&tmp[1]=='x')
                nexts.push_back(next_ap[tmp]);
            else
                labels.push_back(aalta::aalta_formula(tmp.c_str()).unique());
            to_block.push_back(atom[atom_idx[tmp]]);
        }
        else if(((m.get_const_interp(v)).to_string())[0]=='f')
        {
            string tmp=(v.name()).str();
            /*if(tmp[0]=='_'&&tmp[1]=='x')
                nexts.push_back(next_ap[tmp]);
            else*/
            if(tmp=="false")
                labels.push_back(aalta::aalta_formula("1").unique());
            else if(!(tmp[0]=='_'&&tmp[1]=='x'))
                labels.push_back(aalta::aalta_formula(aalta::aalta_formula::Not,NULL,aalta::aalta_formula(tmp.c_str()).unique()).unique());
            //if(!(tmp[0]=='_'&&tmp[1]=='x'))
                to_block.push_back(! (atom[atom_idx[tmp]]));
        }
    }
    if(!to_block.empty())
    {
        z3::expr sol=to_block[0];
        for(int i=1;i<to_block.size();i++)
            sol= (sol && to_block[i]);
        s.add(! sol);
        //cout<<"add: "<<(! sol)<<endl;
    }
    aalta::aalta_formula *label=formula_from(labels);
    aalta::aalta_formula *next=formula_from(nexts);
    label=label->simplify();
    next=next->simplify();
    aalta::Transition *t = new aalta::Transition (label, next);
    return t;
}