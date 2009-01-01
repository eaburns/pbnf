all: graphs.pdf tiles.pdf

graphs.pdf: graphs.tex
	rubber --ps --pdf graphs.pdf

tiles.pdf: tiles.tex
	rubber --ps --pdf tiles.tex

clean:
	rubber --ps --pdf --clean graphs.tex
	rubber --ps --pdf --clean tiles.tex
