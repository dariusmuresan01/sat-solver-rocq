COQC = coqc

VFILES := project_lib.v sat_solver.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

sat_solver.vo: project_lib.vo

%.vo: %.v
	$(COQC) $<

clean:
	rm -f *.vo *.glob *.aux .*.aux *.vos *.vok

.PHONY: all clean
