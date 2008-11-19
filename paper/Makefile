eaburns.pdf: eaburns.dvi
	dvipdf $^

eaburns.dvi: eaburns.tex
	latex eaburns
	latex eaburns
	bibtex eaburns
	bibtex eaburns
	latex eaburns

clean:
	rm -f *.aux *.log
	rm -f *.bbl *.blg
	rm -f eaburns.dvi eaburns.pdf
