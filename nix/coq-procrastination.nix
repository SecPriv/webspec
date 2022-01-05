{ stdenv, fetchFromGitHub, coq }:

stdenv.mkDerivation {
  name = "coq-procrastination";
  version = "199dab4435148e4bdfdf934836c644c2c4e44073";
  src = fetchFromGitHub {
    owner = "Armael";
    repo = "coq-procrastination";
    rev = "199dab4435148e4bdfdf934836c644c2c4e44073";
    sha256 = "0mnm0knzgn0mvq875pfghg3fhwvkr3fpkgwd6brb7hadfxh2xjay";
    fetchSubmodules = true;
  };
  
  buildInputs = [ coq ];
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = {
    description = "A small Coq library for collecting side conditions and deferring their proof.";
    homepage = "https://github.com/Armael/coq-procrastination";
  };
}
