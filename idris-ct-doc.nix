# SPDX-License-Identifier: AGPL-3.0-only
#
# This file is part of `idris-ct` Category Theory in Idris library.
#
# Copyright (C) 2019 Stichting Statebox <https://statebox.nl>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

{ stdenv, haskellPackages, texlive }:

stdenv.mkDerivation rec {
  name = "idris-ct-doc-${version}";
  version = "dev";
  src = ./.;

  buildInputs = [
    haskellPackages.lhs2tex
    texlive.combined.scheme-full
  ];

  buildPhase = ''
    cd docs
    mkdir out
    lhs2TeX -o out/main.tex main.lidr
    cd out
    HOME="$PWD" pdflatex main.tex
  '';

  installPhase = ''
    mkdir -p $out/share/doc/idris-ct
    cp main.pdf $out/share/doc/idris-ct
  '';

  meta = {
    description = "Idris category theory library";
    homepage = "https://github.com/statebox/idris-ct";
  };
}
