all: riscvspecdeps.svg riscvcsimdeps.svg

%.pdf: %.tex
	pdflatex $<

%.svg: %.pdf %.tex
	dvisvgm -Z 1.5 --pdf $<

clean:
	rm riscvspecdeps.pdf riscvspecdeps.aux riscvspecdeps.log
	rm riscvcsimdeps.pdf riscvcsimdeps.aux riscvcsimdeps.log
