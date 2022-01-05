# WebSpec

Towards Machine-Checked Analysis of Browser Security Mechanisms


## Repo Structure

- `model`: Browser Model and Web Invariants
  - The proofs of our proposed changes to the Web platform are provided in the `{Host,CSP,TT,SW}Invariant.v` files
- `compiler`: Compiler from Coq to SMT-LIB

## Running WebSpec

WebSpec can be run using docker or nix
- **Docker**: the `webspec/coq` docker image conatins a copy of the WebSpec environment.
  To run the query of the, e.g., `HttpOnlyInvariant`, run the following command from the repo directory
  ```
  docker run --rm -ti -v $PWD:/mnt webspec/coq scripts/run.sh HttpOnlyInvariant
  ```
- **Nix**: enter the WebSpec environment with the `NIXPKGS_ALLOW_UNFREE=1 nix-shell` command and then run the query with `scripts/run.sh <InvariantName>`. Note that the nix build might take a while!

