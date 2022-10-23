# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile doc src/html
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile src/_CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile src/_CoqProject
	cd src/; $(COQBIN)coq_makefile -f _CoqProject -o CoqMakefile 

invoke-coqmakefile: CoqMakefile
	cd src/; $(MAKE) -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

doc: CoqMakeFile
	cd src/; $(MAKE) -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS)) gallinahtml
	mv src/html/* ./docs/coqdoc/
	rm -rf src/html


.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
