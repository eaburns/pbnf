all: eaburns.pdf snlemons.pdf

eaburns.pdf: snlemons.tex
	rubber --ps --pdf snlemons.tex

snlemons.pdf: eaburns.tex
	rubber --ps --pdf eaburns.tex

clean:
	rubber --ps --pdf --clean eaburns.tex
	rubber --ps --pdf --clean snlemons.tex
