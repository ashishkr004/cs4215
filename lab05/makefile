INPUT = $(shell find *.epl)
FILENAMES = $(notdir $(INPUT))
OUTPUT = $(INPUT:.epl=.out)

all: clean compile $(OUTPUT)
	@echo "done"

clean:
	rm *.out

compile: ePL_type.ml ePL_compile.ml eVM_exec.ml
	./bincomp5.sh

%.out: %.epl ePL_compile.ml eVM_exec.ml
	./eplc $<
	./evm $(basename $<) > $@


test: $(OUTPUT)
	@echo "########## Testing for equality ##########"
#	for i in $(basename $(FILENAMES)); do \
#		echo "$$i diff result--";\
#		diff $$i.out test/out.$$i; \
#	done
	@echo "########## Done testing ##########"
