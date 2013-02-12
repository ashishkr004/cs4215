ocamlc -annot ePL.ml 
ocamlc -annot -I +camlp4 dynlink.cma camlp4lib.cma -pp camlp4of.opt ePL_parser.ml -a -o ePL_parser.cma
ocamlc -annot ePL.cmo ePL_parser.cma ePL_compile.ml -o eplc
ocamlc -annot ePL.cmo ePL_parser.cma eVM_exec.ml -o evm
