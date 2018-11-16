#! /usr/bin/python3
import argparse
import sys
import os
import shutil

FILES = [
    "build.sbt",
    "CONTRIBUTORS.md",
    "DEPENDENCIES",
    "LICENSE",
    "README.md",
    "tutorial/tutorial.pdf"
]

DIRECTORIES = [
    "examples",
    "emacs",
    "lib",
    "project",
    "src",
    "test",
    "vim"
]

DIRECTORIES_TO_CLEAN = DIRECTORIES + [ 
    'tutorial'
]

FILES_TO_CLEAN = FILES

NEW_DIRECTORIES = [
    "tutorial"
]

def check_destination(dest):
    if not os.path.exists(dest):
        print ("Error: '%s' does not exist." % dest)
        sys.exit(1)
    if not os.path.isdir(dest):
        print ("Error: '%s' is not a directory." % dest)
        sys.exit(1)

def cleanup_dir(dest):
    for f in FILES_TO_CLEAN:
        os.unlink(os.path.join(dest, f))
    for d in DIRECTORIES_TO_CLEAN:
        shutil.rmtree(os.path.join(dest, d))
    for nd in NEW_DIRECTORIES:
        os.mkdir(os.path.join(dest, nd))

def copy_to_dir(pwd, dest):
    for f in FILES:
        f1 = os.path.join(pwd, f)
        f2 = os.path.join(dest, f)
        shutil.copyfile(f1, f2)

    for d in DIRECTORIES:
        d1 = os.path.join(pwd, d)
        d2 = os.path.join(dest, d)
        shutil.copytree(d1, d2)

def main():
    parser = argparse.ArgumentParser(description='Publish UCLID5 from private to public repository.')
    parser.add_argument('destination', type=str, help='Location of UCLID5 public repository.')
    args = parser.parse_args()

    dest = args.destination
    check_destination(dest)
    cleanup_dir(dest)
    copy_to_dir(os.getcwd(), dest)

if __name__ == '__main__':
    main()
