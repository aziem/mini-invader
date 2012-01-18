export OCAMLMAKEFILE = OcamlMakefile

SOURCES = gensym.cmi gensym.ml config.mli config.ml error.mli error.ml genlinenum.cmi genlinenum.ml global.cmi global.ml parsetree.cmi parsetree.ml heapstuff.cmi heapstuff.ml utils.cmi utils.ml symbexec.cmi symbexec.ml analysis.cmi analysis.ml parser.mly lexer.mll trans.cmi trans.ml main.ml


MAIN = SOURCES="$(SOURCES)" RESULT=mini-invader

all:
	$(MAKE) -f $(OCAMLMAKEFILE) $(MAIN)

debug: 
	$(MAKE) -f $(OCAMLMAKEFILE) debug-code $(MAIN)

profile: 
	$(MAKE) -f $(OCAMLMAKEFILE) pnc $(MAIN)
clean:
	-rm -f *.cmo *.cmi lexer.ml parser.ml parser.mli mini-invader
