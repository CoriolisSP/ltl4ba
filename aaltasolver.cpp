/* 
 * File:   aaltasolver.cpp
 * Author: Jianwen Li
 * Note: An inheritance class from Minisat::Solver for Aalta use 
 * Created on August 15, 2017
 */
 
#include "aaltasolver.h"
#include <iostream>
#include <vector>
#include <cstring>
#include <cmath>
using namespace std;
using namespace Minisat;

namespace aalta
{
 	
 	Lit AaltaSolver::SAT_lit (int id)
 	{
 		assert (id != 0);
        int var = abs(id)-1;
        while (var >= nVars()) newVar();
        return ( (id > 0) ? mkLit(var) : ~mkLit(var) );
 	}
 	
 	int AaltaSolver::lit_id (Lit l)
    {
    	if (sign(l)) 
            return -(var(l) + 1);
        else 
            return var(l) + 1;
    }
 	
 	bool AaltaSolver::solve_assumption ()
	{
		lbool ret = solveLimited (assumption_);
		if (verbose_)
		{
			cout << "solve_with_assumption: assumption_ is" << endl;
			for (int i = 0; i < assumption_.size (); i ++)
				cout << lit_id (assumption_[i]) << ", ";
			cout << endl;
		}
		if (ret == l_True)
     		return true;
   		else if (ret == l_Undef)
     		exit (0);
   		return false;
	}
	
	//return the model from SAT solver when it provides SAT
	std::vector<int> AaltaSolver::get_model ()
	{
		std::vector<int> res;
		res.resize (nVars (), 0);
   		for (int i = 0; i < nVars (); i ++)
   		{
     		if (model[i] == l_True)
       			res[i] = i+1;
     		else if (model[i] == l_False)
       			res[i] = -(i+1);
   		}
   		if (verbose_)
   		{
   			cout << "original model from SAT solver is" << endl;
   			for (int i = 0; i < res.size (); i ++)
   				cout << res[i] << ", ";
   			cout << endl;
   		}
		res=partial_model(res);
   		return res;
	}

	std::vector<int> AaltaSolver::partial_model(std::vector<int>& res)
	{
		std::vector<int> partial_assign;
		partial_assign.resize(res.size(),0);
		bool selected[res.size()];
		memset(selected,0,sizeof(selected));
		for(int i=0;i<assumption_.size();i++)
		{
			partial_assign[abs(lit_id(assumption_[i]))-1]=lit_id(assumption_[i]);
			selected[abs(lit_id(assumption_[i]))-1]=true;
		}
		std::vector<std::vector<bool> > mat;
		mat.resize(clauses.size ());
		for(int i=0;i<mat.size();i++)
			mat[i].resize(res.size(),false);
		for(int i=0;i<clauses.size();i++)
		{
			Clause& c = ca[clauses[i]];
			int cnt=0,li;
			for (int j = 0; j < c.size (); j ++)
			{
				if(lit_id(c[j])==res[abs(lit_id(c[j]))-1])
				{
					li=lit_id(c[j]);
					mat[i][abs(li)-1]=true;
					cnt++;
				}
			}
			if(cnt==1)
			{
				selected[abs(li)-1]=true;
				partial_assign[abs(li)-1]=li;
			}
		}
		std::vector<std::vector<bool>>::iterator it;
		for(int i=0;i<partial_assign.size();i++)
		{
			if(selected[i])
			{
				for(it=mat.begin();it!=mat.end();++it)
				{
					if((*it)[abs(partial_assign[i])-1])
					{
						mat.erase(it);
						--it;
					}
				}
			}
		}
		while(!mat.empty())
		{
			int mx_idx,mx_cnt=0;
			for(int i=0;i<res.size();i++)
			{
				if(!selected[i])
				{
					int cnt=0;
					for(int j=0;j<mat.size();j++)
						if(mat[j][i])  cnt++;
					if(cnt>mx_cnt)
					{
						mx_cnt=cnt;
						mx_idx=i;
					}
				}
			}
			selected[mx_idx]=true;
			partial_assign[mx_idx]=res[mx_idx];
			for(it=mat.begin();it!=mat.end();++it)
			{
				if((*it)[mx_idx])
				{
					mat.erase(it);
					--it;
				}
			}
		}
		return partial_assign;
	}
	
	//return the UC from SAT solver when it provides UNSAT
 	std::vector<int> AaltaSolver::get_uc ()
 	{
 		std::vector<int> reason;
		if (verbose_)
			cout << "get uc: \n";
 		for (int k = 0; k < conflict.size(); k++) 
 		{
        	Lit l = conflict[k];
        	reason.push_back (-lit_id (l));
			if (verbose_)
				cout << -lit_id (l) << ", ";
    	}
		if (verbose_)
			cout << endl;
    	return reason;
  	}
	
	void AaltaSolver::add_clause (std::vector<int>& v)
 	{
 		vec<Lit> lits;
 		for (std::vector<int>::iterator it = v.begin (); it != v.end (); it ++)
 			lits.push (SAT_lit (*it));
 		/*
 		if (verbose_)
 		{
 			cout << "Adding clause " << endl << "(";
 			for (int i = 0; i < lits.size (); i ++)
 				cout << lit_id (lits[i]) << ", ";
 			cout << ")" << endl;
 			cout << "Before adding, size of clauses is " << clauses.size () << endl;
 		}
 		*/
 		addClause (lits);
 		/*
 		if (verbose_)
 			cout << "After adding, size of clauses is " << clauses.size () << endl;
 		*/
 	}
 	
 	void AaltaSolver::add_clause (int id)
 	{
 		std::vector<int> v;
 		v.push_back (id);
 		add_clause (v);
 	}
 	
 	void AaltaSolver::add_clause (int id1, int id2)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		add_clause (v);
 	}
 	
 	void AaltaSolver::add_clause (int id1, int id2, int id3)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		v.push_back (id3);
 		add_clause (v);
 	}
 	
 	void AaltaSolver::add_clause (int id1, int id2, int id3, int id4)
 	{
 		std::vector<int> v;
 		v.push_back (id1);
 		v.push_back (id2);
 		v.push_back (id3);
 		v.push_back (id4);
 		add_clause (v);
 	}
 	
 	void AaltaSolver::print_clauses ()
	{
		cout << "clauses in SAT solver: \n";
		for (int i = 0; i < clauses.size (); i ++)
		{
			Clause& c = ca[clauses[i]];
			for (int j = 0; j < c.size (); j ++)
				cout << lit_id (c[j]) << ", ";
			cout << endl;
		}
	}

	void AaltaSolver::print_cnf()
	{
		cout<<"p cnf "<<nVars()<<' '<<assumption_.size()+clauses.size()<<endl;
		for(int i=0;i<assumption_.size();i++)
			cout<<lit_id(assumption_[i])<<' '<<0<<endl;
		for(int i=0;i<clauses.size();i++)
		{
			Clause& c=ca[clauses[i]];
			for(int j=0;j<c.size();j++)
				cout<<lit_id(c[j])<<' ';
			cout<<0<<endl;
		}
	}
}
