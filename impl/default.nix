{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, array, base, containers, directory, filepath
      , haskeline, megaparsec, mtl, prettyprinter, protolude, repline
      , scientific, stdenv, tasty, tasty-hspec, text, unbound-generics
      }:
      mkDerivation {
        pname = "sedel";
        version = "0.1.0.0";
        src = ./.;
        isLibrary = true;
        isExecutable = true;
        libraryHaskellDepends = [
          array base containers directory filepath haskeline megaparsec mtl
          prettyprinter protolude repline scientific text unbound-generics
        ];
        executableHaskellDepends = [
          array base containers directory filepath haskeline megaparsec mtl
          prettyprinter protolude repline scientific text
        ];
        testHaskellDepends = [
          array base containers directory filepath haskeline megaparsec mtl
          prettyprinter protolude repline scientific tasty tasty-hspec text
        ];
        description = "type system for first-class traits";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = pkgs.haskell.lib.dontHaddock (variant (haskellPackages.callPackage f {}));

in

  if pkgs.lib.inNixShell then drv.env else drv
