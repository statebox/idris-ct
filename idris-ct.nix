{ stdenv, pkgs, idrisPackages }:

idrisPackages.build-idris-package {
  name = "idris-ct";
  version = "dev";
  src = ./.;
  doCheck = true;

  idrisDeps = with idrisPackages; [
    contrib
  ];

  meta = {
    description = "Idris category theory library";
    homepage = "https://github.com/statebox/idris-ct";
  };
}
