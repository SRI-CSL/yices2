

test:
	pytest


PYLINT = $(shell which pylint)

lint:
ifeq ($(PYLINT),)
	$(error lint target requires pylint)
endif
	@ $(PYLINT) -E  yices.py test/*.py
# for detecting more than just errors:
#	@ $(PYLINT) --rcfile=.pylintrc yices.py test/*.py

.PHONY: test lint
