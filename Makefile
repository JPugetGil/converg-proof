# Makefile for ConVerG Rocq formalization
#
# Usage:
#   make           - Build all Rocq files
#   make clean     - Remove generated files
#   make doc       - Generate documentation (requires rocqdoc)

COQMAKEFILE := Makefile.coq

all: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE)

$(COQMAKEFILE): _CoqProject
	rocq makefile -f _CoqProject -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf

doc: $(COQMAKEFILE)
	@$(MAKE) -f $(COQMAKEFILE) html

.PHONY: all clean doc
