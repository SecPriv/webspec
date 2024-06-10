{ lib
, fetchzip
, tcl
}:

tcl.mkTclDerivation rec {
  pname = "tklib";
  version = "0.7";

  src = fetchzip {
    url = "https://core.tcl-lang.org/tklib/tarball/tklib-0.7.tar.gz?uuid=tklib-0.7";
    hash = "sha256-Km7MBJB43lK9ss8VmVHJiHDfDyy7mTm0eKMOzs/DSa8=";
  };

  buildFlags = [ "all" ] ;

  meta = {
    homepage = "https://core.tcl-lang.org/tklib/";
    description = "A companion to Tcllib, for Tk related packages.";
    license = lib.licenses.tcltk;
    platforms = lib.platforms.unix;
  };
}
