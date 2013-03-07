ocamlc -annot debug.ml -a -o debug.cma
ocamlc -annot sPL.ml -a -o sPL.cma
ocamlc -annot sPLc.ml -a -o sPLc.cma
ocamlc -annot sPL_type.ml -a -o sPL_type.cma
ocamlc -i sPL_type.ml > sPL_type.mli
ocamlc -c sPL_type.mli
mv sPL_type.mli binary
mv sPL_type.cma binary
mv sPL_type.cmi binary
rm sPL_type.ml
rm *.cmo *.annot *.cmi *cma

