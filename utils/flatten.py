#!/usr/bin/env python
#
# This flattens the annnoying tree structure from star exec
#
#  flatten.py  dir0 will turn all files of the form
#  
#   dir0/dir1/dir2/dir3/foo.smt2
#
#   dir0_dir1_dir2_dir3_foo.smt2

import sys
import os
import shutil

def flatten_dir(prefix, directory):
    if not os.path.isdir(directory):
        return
    else:
        files = os.listdir(directory)
        for file in files:
            path = os.path.join(directory, file)
            if os.path.isdir(path):
                flatten_dir('{0}_{1}'.format(prefix, file), path)
            else:
                flatten_file(prefix, file, path)
                
            
def flatten_file(prefix, file, source):
    filename, extension = os.path.splitext(file)
    if extension == '.smt2':
        target = '{0}_{1}'.format(prefix, file)
        shutil.copyfile(source, target)

def main(args):

    if len(args) < 2:
        print 'Usage: {0} <dir>'.format(args[0])
    else:
        flatten_dir(args[1], args[1])


if __name__ == '__main__':
    sys.exit(main(sys.argv))

