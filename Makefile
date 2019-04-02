.PHONY=all pdf clean cleanAuxiliary cleanBinaries cleanSources

all: pdf

pdf:
	$(MAKE) -C docs pdf

clean:
	$(MAKE) -C docs clean

cleanAuxiliary:
	$(MAKE) -C docs cleanAuxiliary

cleanBinaries:
	$(MAKE) -C docs cleanBinaries

cleanSources:
	$(MAKE) -C docs cleanSources
