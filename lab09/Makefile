OCAMLBUILD = ocamlbuild

#  number of parallel jobs, 0 means unlimited.
JOBS = 0

# dynlink should precede camlp4lib
LIBSB = dynlink,camlp4lib
LIBSN = dynlink,camlp4lib
LIBS2 = dynlink,camlp4lib

INCLUDES = -I,+camlp4
 
FLAGS = $(INCLUDES),-dtypes
GFLAGS = $(INCLUDES),-g,-dtypes

# -no-hygiene flag to disable "hygiene" rules
OBB_FLAGS = -no-links -pp camlp4of.opt -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS)
OBBC_FLAGS = -no-links -libs $(LIBSB) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 
OBN_FLAGS = -no-links -pp camlp4of.opt -libs $(LIBSN) -cflags $(FLAGS) -lflags $(FLAGS) -lexflag -q -yaccflag -v  -j $(JOBS) 

all: byte 

byte: dplu.byte

# native: splt.native spli.native

lab09 : dplu.byte test

test:
	./dplu > b
	diff b soln_dplu.txt

.PHONY: test

parser : sPL_parser.cmo

sPL_parser.cmo:
	@ocamlbuild $(OBB_FLAGS) sPL_parser.cmo

dPL.byte: 
	@ocamlbuild $(OBB_FLAGS) dPL_type_m.byte
	cp -u _build/dPL_type_m.byte dplt

dplu.byte: 
	@ocamlbuild $(OBB_FLAGS) dPL_unify.byte
	cp -u _build/dPL_unify.byte dplu

splt.byte: 
	@ocamlbuild $(OBB_FLAGS) sPL_type_m.byte
	cp -u _build/sPL_type_m.byte splt

# splt.native:
# 	@ocamlbuild $(OBN_FLAGS) sPL_type_m.native
# 	cp -u _build/sPL_type_m.native splt

dpli.byte: 
	@ocamlbuild $(OBB_FLAGS) dPL_inter1.byte dPL_inter2.byte
	cp -u _build/dPL_inter1.byte spli
	cp -u _build/dPL_inter2.byte spli2

dvm.byte:
	@ocamlbuild $(OBB_FLAGS) dVM_exec.byte
	cp -u _build/dVM_exec.byte dvm

dvm2.byte:
	@ocamlbuild $(OBB_FLAGS) dVM_exec2.byte
	cp -u _build/dVM_exec2.byte svm2

dplc.byte: 
	@ocamlbuild $(OBB_FLAGS) dPL_compile.byte
	cp -u _build/dPL_compile.byte dplc

# spli.native:
# 	@ocamlbuild $(OBN_FLAGS) sPL_inter1.native sPL_inter2.native
# 	cp -u _build/sPL_inter1.native spli
# 	cp -u _build/sPL_inter2.native spli2

# Clean up
clean:
	$(OCAMLBUILD) -quiet -clean 
	rm -f splt spli spli2
	rm -f *cma *.cmo *.cmi *.cmx *.o *.mli *.output *.annot
	# rm sPL_lexer.ml
