add_test( HelloTest.BasicAssertions /home/jmw150/backup/code/projects/algebra/my_project/build/hello_test [==[--gtest_filter=HelloTest.BasicAssertions]==] --gtest_also_run_disabled_tests)
set_tests_properties( HelloTest.BasicAssertions PROPERTIES WORKING_DIRECTORY /home/jmw150/backup/code/projects/algebra/my_project/build)
set( hello_test_TESTS HelloTest.BasicAssertions)
