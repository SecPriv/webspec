let nixpkgs = fetchTarball {
      url = "https://github.com/nixos/nixpkgs/archive/29a15e2c1f5ad64c235d78ba5e29a56fe520ad45.tar.gz";
    };
    pkgs = import (nixpkgs) {};
    customOCamlPackages = pkgs.ocaml-ng.ocamlPackages_4_11;
    customCoq = pkgs.callPackage (nixpkgs + "/pkgs/applications/science/logic/coq") {
      version = "8.13";
      ocamlPackages_4_05 = null; ocamlPackages_4_09 = null; ocamlPackages_4_10 = null;
      inherit customOCamlPackages;
    };
    coq_procrastination = with pkgs; callPackage ./nix/coq-procrastination.nix { coq = customCoq; };
    patched_z3 = with pkgs; callPackage ./nix/z3-patched.nix {};
    mkCoqDerivation = with pkgs; callPackage (nixpkgs + "/pkgs/build-support/coq") { coq = customCoq; };
    coqhammer = (with pkgs; callPackage (nixpkgs + "/pkgs/development/coq-modules/coqhammer") {
        coq = customCoq;
        version = "v1.3.1-coq8.13";
        inherit mkCoqDerivation;
    }).overrideAttrs (super: {
      src = fetchTarball {
          url = "https://github.com/lukaszcz/coqhammer/archive/refs/tags/v1.3.1-coq8.13.tar.gz";
      };
    });
    customCoqPackages = pkgs.mkCoqPackages customCoq;
    coq-ext-lib = pkgs.stdenv.mkDerivation {
      name = "coq-ext-lib";
      version = "0.11.6";
      src = fetchTarball {
        url = "https://github.com/coq-community/coq-ext-lib/archive/refs/tags/v0.11.6.tar.gz";
      };
      buildInputs = [ customCoq ];
      installFlags = "COQLIB=$(out)/lib/coq/${customCoq.coq-version}/";

      meta = {
        description = "A collection of theories and plugins that may be useful in other Coq developments.";
        homepage = "https://github.com/coq-community/coq-ext-lib";
      };
    };
    simple-io = pkgs.stdenv.mkDerivation {
      name = "coq-simple-io";
      version = "1.3.0";
      src = fetchTarball {
        url = "https://github.com/Lysxia/coq-simple-io/archive/refs/tags/1.3.0.tar.gz";
      };
      buildInputs = [ customCoq coq-ext-lib ] ++ (with customCoq.ocamlPackages; [ zarith ocaml ocamlbuild cppo findlib ]);
      installFlags = "COQLIB=$(out)/lib/coq/${customCoq.coq-version}/";

      meta = {
        description = "Purely functional IO for Coq";
        homepage = "https://github.com/Lysxia/coq-simple-io";
      };

    };
    quickchick = pkgs.stdenv.mkDerivation rec {
      name = "quickchick";
      version = "1.5.0";
      src = fetchTarball {
        url = "https://github.com/QuickChick/QuickChick/archive/refs/tags/v1.5.0.tar.gz";
      };
      buildInputs = [ pkgs.ncurses  customCoq customCoqPackages.coqPackages.ssreflect coq-ext-lib simple-io ] ++ (with customCoq.ocamlPackages; [ ocaml ocamlbuild zarith num findlib ]);
      installFlags = "COQLIB=$(out)/lib/coq/${customCoq.coq-version}/";
      enableParallelBuilding = false;
      preConfigure = ''
        substituteInPlace Makefile --replace quickChickTool.byte quickChickTool.native
      '';
      installPhase = ''
        runHook preInstall
        echo $out
        make -f Makefile.coq COQPREFIX=$out/lib/coq/${customCoq.coq-version}/  COQLIB=$out/lib/coq/${customCoq.coq-version}/ install
        runHook postInstall
      '';

      meta = {
        description = "Randomized property-based testing plugin for Coq";
        homepage = "https://github.com/QuickChick/QuickChick";
      };
    };
in
pkgs.mkShell rec {
  name = "model";
  buildInputs =  (with pkgs; [ gnumake dune_2 customCoq patched_z3 coq_procrastination coqhammer plantuml z3-tptp vampire cvc4 eprover librsvg ])
              ++ (with customOCamlPackages; [
                   ocaml z3 findlib ocamlbuild sexplib utop merlin yojson ppx_deriving ppx_deriving_yojson ppx_import jingoo base64 uuidm])
              ++ ([ quickchick customCoqPackages.coqPackages.ssreflect  coq-ext-lib simple-io ]);
}
