// building out cocoalib features

#include <iostream>
#include <string>
#include <vector>

using namespace std;

// C++ template to print vector container elements
template <typename T>
ostream& operator<<(ostream& os, const vector<T>& v)
{
    os << "[";
    for(int i = 0; i < v.size(); ++i)
    {
        os << v[i];
        if(i != v.size() - 1)
        {
            os << ", ";
        }
    }
    os << "]";
    return os;
}

// integers sans memory limits
class integer
{
public:
    vector<int> digits;
    // constructors
    integer(int inputcopy)
    {
        int mod = 10;
        while(inputcopy > 0)
        {
            digits.push_back(inputcopy % mod);
            inputcopy = inputcopy / mod;
        }
    }

    integer(string inputcopy)
    {
        for (int i = inputcopy.size()-1 ; i >= 0 ; i--)
        {
            digits.push_back(inputcopy[i]-48);
            
        }
    }

    string toString()
    {
        string toret;
    for(int i = digits.size() - 1 ; i >= 0 ; i--)
    {
        toret += char(digits[i]) + 49 ;
    }
    return toret;

    }

};

// printing integers
ostream& operator<<(ostream& os, const integer& n)
{
    for(int i = n.digits.size() - 1 ; i >= 0 ; i--)
    {
        os << n.digits[i] ;
    }
    return os;
}

// print if not equal
//void isequal(

    // test suite
int main()
{
    // take and print int

    // take and print strings
    string test_str = "12345";
    integer str(test_str);
    cout << test_str << endl;
    cout << str.digits << endl;
    cout << str << endl;

    return 0;
}
