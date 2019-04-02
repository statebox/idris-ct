.PHONY=all pdf clean cleanAuxiliary cleanBinaries cleanSources

MAIN=main
AUX=auxiliary
SOURCES=sources

all: pdf

pdf:
	mkdir -p ${AUX}
	mkdir -p ${SOURCES}
	lhs2TeX -o ${SOURCES}/${MAIN}.tex ${MAIN}.lidr
	latexmk -pdf ${SOURCES}/${MAIN}.tex -outdir=${AUX}
	mv ${AUX}/${MAIN}.pdf ${MAIN}.pdf

clean:
	rm -f ${AUX}/* ${SOURCES}/*

cleanAuxiliary:
	rm -f ${AUX}/*

cleanSources:
	rm -f ${SOURCES}/*
