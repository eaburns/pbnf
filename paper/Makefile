eaburns.pdf: eaburns.dvi
	dvipdf $^

eaburns.dvi: eaburns.tex master.bib
	latex eaburns
	bibtex eaburns
	latex eaburns
	latex eaburns

clean:
	rm -f *.aux *.log
	rm -f *.bbl *.blg
	rm -f eaburns.dvi eaburns.pdf
