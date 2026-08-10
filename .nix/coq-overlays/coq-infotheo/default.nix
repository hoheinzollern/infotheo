{ lib, mkCoqDerivation, coq, mathcomp, mathcomp-analysis,
  mathcomp-reals-stdlib, mathcomp-algebra-tactics, hierarchy-builder,
  interval, version ? null }:

## infotheo is not in nixpkgs under this attribute; the version is
## overridden to the local sources by coq-nix-toolbox
mkCoqDerivation {
  pname = "coq-infotheo";
  owner = "affeldt-aist";
  repo = "infotheo";

  inherit version;
  defaultVersion = null;

  propagatedBuildInputs = [
    mathcomp.ssreflect mathcomp.fingroup mathcomp.algebra
    mathcomp.solvable mathcomp.field
    mathcomp-analysis mathcomp-reals-stdlib mathcomp-algebra-tactics
    hierarchy-builder interval
  ];

  meta = with lib; {
    description = "Discrete probabilities and information theory for Rocq";
    license = licenses.lgpl21Plus;
  };
}
