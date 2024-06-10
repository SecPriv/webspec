{ lib
, tcl
}:

tcl.mkTclDerivation rec {
  pname = "arc-theme";
  version = "0.1";

  src = fetchTarball {
    url = "https://github.com/TkinterEP/ttkthemes/archive/refs/heads/master.tar.gz";
  };

  installPhase = ''
    mkdir -p $out/lib
    cp -r  ttkthemes/png/arc $out/lib/arc
  '';
}
