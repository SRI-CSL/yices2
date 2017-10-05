#iam's makefile; maybe migrate some targets to the main Makefile when done.

all: help


help:
	@echo ''
	@echo 'Here are the targets:'
	@echo ''
	@echo 'To test                :    "make check"'
	@echo 'To develop             :    "make develop"'
	@echo 'To install             :    "make install"'
	@echo 'To publish             :    "make publish"'
	@echo 'To pylint (errors)     :    "make lint"'
	@echo 'To pylint (all)        :    "make lint_all"'
	@echo ''



check:
	pytest


#local editable install for developing
develop:
	pip install -e .

iam:
	python -m pip install -e .

dist: clean
	python setup.py bdist_wheel

# If you need to push this project again,
# INCREASE the version number in yices/version.py,
# otherwise the server will give you an error.

publish: dist
	python setup.py sdist upload

install:
	pip install

clean:
	rm -f  *.pyc *~



PYLINT = $(shell which pylint)


check_lint:
ifeq ($(PYLINT),)
	$(error lint target requires pylint)
endif


lint: check_lint
# for detecting just errors:
	@ $(PYLINT) -E  yices.py test/*.py examples/sudoku/sudoku.py

#	@ $(PYLINT) --rcfile=.pylintrc yices.py test/*.py

sudoku: check_lint
# for detecting just errors:
	@ $(PYLINT) -E  sudoku/sudoku.py

gui: check_lint
# for detecting just errors:
	@ $(PYLINT) -E  gui/*.py

#	@ $(PYLINT) --rcfile=.pylintrc yices.py test/*.py

lint_all: check_lint
# for detecting more than just errors:
	@ $(PYLINT) --rcfile=.pylintrc yices.py #test/*.py

.PHONY: test lint lint check_lint
