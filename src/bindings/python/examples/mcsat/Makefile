
all: clean mcsat python


mcsat: mcsat.c
	${CC} mcsat.c -o mcsat -lyices -lpoly
	./mcsat

python: mcsat.py
	./mcsat.py

PYLINT = $(shell which pylint)

check_lint:
ifeq ($(PYLINT),)
	$(error lint target requires pylint)
endif


lint: check_lint
# for detecting just errors:
	@ $(PYLINT) -E  mcsat.py

clean:
	rm -f *~ mcsat
