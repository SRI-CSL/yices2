from setuptools import setup, find_packages
import os
import glob

from codecs import open
from os import path

here = path.abspath(path.dirname(__file__))

#FIXME:
# Get the long description from the README file
#with open(path.join(here, 'README.rst'), encoding='utf-8') as f:
#    long_description = f.read()
long_description = "This is the long description."

# use the in house version number so we stay in synch with ourselves.
from yices import yices_python_version

setup(
    name='yices',
    version=yices_python_version,
    description='Python Bindings for the Yices SMT Solver',
    long_description=long_description,
    url='https://github.com/SRI-CSL/yices2',
    author='Sam Owre, Ian A. Mason, Bruno Dutertre.',
    author_email='iam@csl.sri.com',


    include_package_data=True,

    packages=find_packages(),

    entry_points = {
        'console_scripts': [
            'yices_python_info = yices:yices_python_info_main',
        ],
    },

    license='GPLv3',

    #FIXME: pypi rejects the license and windows strings. Find ones that work.
    classifiers=[
        'Development Status :: 4 - Beta',
        'Natural Language :: English',
        'Intended Audience :: Science/Research',
        'Intended Audience :: Developers',
        'Topic :: Software Development :: Compilers',
        'License :: OSI Approved :: GNU General Public License v3 (GPLv3)',
        'Operating System :: Microsoft :: Windows',
        'Operating System :: MacOS',
        'Operating System :: POSIX :: Linux',
        'Operating System :: POSIX :: BSD',
        'Programming Language :: C',
        'Programming Language :: Python',
        'Programming Language :: Python :: 2',
        'Programming Language :: Python :: 2.7',
        'Programming Language :: Python :: 3',
        'Programming Language :: Python :: 3.4',
        'Programming Language :: Python :: 3.5',
        'Programming Language :: Python :: 3.6',
        'Topic :: Scientific/Engineering :: Mathematics',
        'Topic :: Software Development :: Libraries :: Python Modules',
    ],

    py_modules=['yices'],

)
