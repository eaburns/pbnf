all: graphs.pdf

graphs.pdf: graphs.dvi
	dvipdf $^

graphs.dvi: graphs.tex
	latex $^

clean:
	rm -f *.pdf *.dvi *.aux *.log
