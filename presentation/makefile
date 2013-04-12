all:

clean:
	rm -f slides.pdf

slides.pdf: slides.tex
	pdflatex slides.tex
	cp -u slides.pdf U096857U_slides.pdf
.PHONY: all clean
