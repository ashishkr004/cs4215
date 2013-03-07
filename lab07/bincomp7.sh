mkdir -p _build
cp -p *.ml _build
cp -p *.mll _build
cp binary/* _build
cd _build
ocamlc -annot debug.ml 
ocamlc -annot sPL.ml -a -o sPL.cma
ocamlc -annot sPLc.ml -a -o sPLc.cma
ocamlc -annot -I +camlp4 dynlink.cma camlp4lib.cma -pp camlp4of.opt sPL_token.ml -a -o sPL_token.cma 
ocamllex sPL_lexer.mll
ocamlc -annot -I +camlp4 dynlink.cma camlp4lib.cma -pp camlp4of.opt sPL_lexer.ml -a -o sPL_lexer.cma
ocamlc -annot -I +camlp4 dynlink.cma camlp4lib.cma -pp camlp4of.opt sPL_parser.ml -a -o sPL_parser.cma
#ocamlc -annot sPL_type.ml -a -o sPL_type.cma
ocamlc -annot sPL_inter.ml -a -o sPL_inter.cma
ocamlc -annot debug.cmo sPL.cma sPLc.cma sPL_token.cma sPL_lexer.cmo sPL_parser.cmo sPL_type.cma sPL_inter.cma sPL_inter1.ml -o spli
ocamlc -annot debug.cmo sPL.cma sPLc.cma sPL_token.cma sPL_lexer.cmo sPL_parser.cmo sPL_type.cma sPL_inter.cma sPL_inter2.ml -o spli2
cp -f spli ..
cp -f spli2 ..
