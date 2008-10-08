all: slides.pdf

slides.pdf: slides.dvi
	dvipdf slides

slides.dvi: slides.tex
	latex slides

clean:
	rm -f *.aux *.log *.dvi *.pdf *.bm *.toc
