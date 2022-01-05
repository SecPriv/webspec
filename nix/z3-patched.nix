{ stdenv, z3 }:

z3.overrideAttrs (oldAttrs: rec {
  patches = [ ./z3_bmc_initial_unrolling_level.patch ];
})
