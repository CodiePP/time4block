{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, base, bytestring, unix
      , stdenv, zlib, ncurses, libiconv
      }:
      mkDerivation {
        pname = "time4block";
        version = "0.1.0.0";
        sha256 = "0";
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [ base bytestring unix  ];
        executableHaskellDepends = [ base bytestring unix ];
        libraryPkgconfigDepends = [ ncurses libiconv zlib ];
        homepage = "https://github.com/CodiePP/time4block";
        description = "Cardano block to time calculator";
        license = stdenv.lib.licenses.mit;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv

