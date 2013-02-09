INPUT = $(shell find test/*.epl)
FILENAMES = $(notdir $(INPUT))
OUTPUT = $(FILENAMES:.epl=.out)

all: clean compile test
	@echo "done"

clean:
	rm *.out

compile: ePL_inter.ml
	./bincomp4.sh

%.out: %.epl ePL_inter.ml
	./epli $< > $@

test: $(OUTPUT)
	@echo "########## Testing for equality ##########"
	for i in $(basename $(FILENAMES)); do \
		echo "$$i diff result--";\
		diff $$i.out test/out.$$i; \
	done
	@echo "########## Done testing ##########"
