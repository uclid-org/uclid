all: tutorial.pdf

tutorial.pdf: *.tex
	pdflatex -halt-on-error tutorial.tex
	pdflatex -halt-on-error tutorial.tex
		
.PHONY: clean
	

clean:
	rm -f tutorial.ps tutorial.pdf *.dvi *.bbl *.aux *.log *.blg *.out

open:
	if which okular > /dev/null; then okular cc17.pdf; else open cc17.pdf; fi
