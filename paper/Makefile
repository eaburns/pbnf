all: eaburns.pdf snlemons.pdf

eaburns.pdf: eaburns.dvi
	dvipdf $^

eaburns.dvi: eaburns.tex master.bib
	latex eaburns
	bibtex eaburns
	latex eaburns
	latex eaburns

snlemons.pdf: snlemons.dvi
	dvipdf $^

snlemons.dvi: snlemons.tex master.bib
	latex snlemons
	bibtex snlemons
	latex snlemons
	latex snlemons

clean:
	rm -f *.aux *.log
	rm -f *.bbl *.blg
	rm -f eaburns.dvi eaburns.pdf snlemons.dvi snlemons.pdf
