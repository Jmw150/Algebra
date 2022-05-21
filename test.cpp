// went with boost for testing

#include "algebra.cpp"

#define BOOST_TEST_MODULE My Test 
#include <boost/test/included/unit_test.hpp> 

BOOST_AUTO_TEST_CASE(int_input) 
{
    // take and print int
    int testint = 10;
    integer fromint(testint);
    cout << testint << endl;
    cout << fromint.digits << endl;
    cout << fromint << endl;
    
    BOOST_TEST(testint == 10);
}
/*
BOOST_AUTO_TEST_CASE(test_eq) 
{
  int i = 1;
  BOOST_TEST(i); 
  BOOST_TEST(i == 1); 
}
BOOST_AUTO_TEST_CASE(first_test) 
{
  int i = 1;
  BOOST_TEST(i); 
  BOOST_TEST(i == 1); 
}

*/
