all: eaburns.pdf snlemons.pdf

eaburns.pdf: eaburns.tex
	rubber --ps --pdf eaburns.tex

snlemons.pdf: snlemons.tex
	rubber --ps --pdf snlemons.tex

clean:
	rubber --ps --pdf --clean eaburns.tex
	rubber --ps --pdf --clean snlemons.tex
