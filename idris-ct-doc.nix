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
