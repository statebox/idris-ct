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

# Nix package for development
#
## INSTALL
#
# To build and install the packages in the user environment, use:
#
# $ nix-env -f . -i
#
## BUILD ONLY
#
# To build the packages and add it to the nix store, use:
#
# $ nix-build
#
## SHELL
#
# To launch a shell with all dependencies installed in the environment:
#
# $ nix-shell -A idris-ct
#
# After entering nix-shell, build it:
#
# $ make
#
## NIXPKGS
#
# For all of the above commands, nixpkgs to use can be set the following way:
#
# a) by default it uses nixpkgs pinned to a known working version
#
# b) use the default nixpkgs from the system:
#    --arg pkgs 0
#
# c) use nixpkgs from an URL
#    --arg pkgs 0 -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/18.09.tar.gz
#
# c) use nixpkgs at a given path
#    --arg pkgs /path/to/nixpkgs

{
 pkgs ? null,
}:

let
  syspkgs = import <nixpkgs> { };
  pinpkgs = syspkgs.fetchFromGitHub {
    owner = "NixOS";
    repo = "nixpkgs";

    # binary cache exists for revisions listed in https://nixos.org/channels/
    rev = "b425012fdf450e7b3397d5a3d28d6091de24546f";
    sha256 = "14zg1m59788j37qnylnsad09al9kzcq0mqsfr0pa4zd4r7rfc4ny";
  };
  usepkgs = if null == pkgs then
             import pinpkgs {}
            else
              if 0 == pkgs then
                import <nixpkgs> { }
              else
                import pkgs {};
  stdenv = usepkgs.stdenvAdapters.keepDebugInfo usepkgs.stdenv;

in {
  idris-ct = usepkgs.callPackage ./idris-ct.nix {};
  idris-ct-doc = usepkgs.callPackage ./idris-ct-doc.nix {};
}
