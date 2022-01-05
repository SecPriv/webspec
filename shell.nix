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
    coqhammer = with pkgs; callPackage (nixpkgs + "/pkgs/development/coq-modules/coqhammer") {
        coq = customCoq; 
        version = "v1.3.1-coq8.13";
        inherit mkCoqDerivation;
    };
in
pkgs.mkShell rec {
  name = "model";
  buildInputs =  (with pkgs; [ gnumake dune_2 customCoq patched_z3 coq_procrastination plantuml coqhammer z3-tptp vampire cvc4 eprover librsvg ])
              ++ (with customOCamlPackages; [
                   ocaml z3 findlib ocamlbuild sexplib utop merlin ]);
}
