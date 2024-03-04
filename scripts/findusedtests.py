#! /usr/bin/python3

import argparse
import os
import re

def get_test_files():
    path = os.path.join('src', 'test', 'scala')
    files = [os.path.join(path, f) for f in os.listdir(path)]
    return files

str_rex = re.compile(r'"([^"]+)"')
def get_used_tests(filename):
    testnames = []
    with open(filename, 'rt') as f:
        for l in f:
            m = str_rex.search(l)
            while m:
                testname = m.group(1)
                if testname.startswith('test/') or testname.startswith('./test/'):
                    testnames.append(os.path.normpath(testname))
                m = str_rex.search(l, m.end())

    return testnames

def get_all_tests():
    path = 'test'
    return [os.path.join(path, f) for f in os.listdir(path)]

def print_missing_tests():
    files = (get_test_files())
    tests = []
    for f in files:
        tests += get_used_tests(f)
    testset = set(tests)

    for t in get_all_tests():
        if t not in testset:
            print ('MISSING: %s' % t)


if __name__ == '__main__':
    print_missing_tests()
