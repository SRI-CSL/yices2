

test:
	pytest


PYLINT = $(shell which pylint)


check_lint:
ifeq ($(PYLINT),)
	$(error lint target requires pylint)
endif


lint: check_lint
# for detecting just errors:
	@ $(PYLINT) -E  yices.py #test/*.py

#	@ $(PYLINT) --rcfile=.pylintrc yices.py test/*.py

lint_all: check_lint
# for detecting more than just errors:
	@ $(PYLINT) --rcfile=.pylintrc yices.py #test/*.py

.PHONY: test lint lint check_lint
