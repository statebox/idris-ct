# SPDX-License-Identifier: AGPL-3.0-only

# This file is part of `idris-ct` Category Theory in Idris library.

# Copyright (C) 2019 Stichting Statebox <https://statebox.nl>

# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.

# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.

# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

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
