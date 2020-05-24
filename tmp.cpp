#include <fstream>
#include <string>
#include <cstdlib>
using namespace std;

int rd()
{
    return rand()%5;
}
int main()
{
    string op[5]={">",">=","<","<=","=="};
    ifstream fin;
    fin.open("ltl_test",ios::in);
    ofstream fout;
    fout.open("smt_test",ios::out);
    string line;
    while(getline(fin,line))
    {
        while (line.find("(p")!=string::npos)
        {
            int start=line.find("(p");
            int end=line.find(')',start+1);
            line.replace(start+1,end-start-1,("#p"+op[rd()]+line.substr(start+2,end-start-2)+"#"));
        }
        fout<<line<<endl;
    }
    fin.close();
    fout.close();
    return 0;
}