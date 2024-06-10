with import <nixpkgs> {};
mkShell {
    name="gui";
    buildInputs = [
      (callPackage ./tklib.nix {})
      (callPackage ./arc-theme.nix {})
    ];
}
