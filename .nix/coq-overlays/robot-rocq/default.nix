{ lib, mkCoqDerivation, coq, mathcomp, mathcomp-analysis,
  mathcomp-real-closed, mathcomp-algebra-tactics, hierarchy-builder,
  version ? null }:

mkCoqDerivation {
  pname = "robot-rocq";
  owner = "affeldt-aist";
  repo = "robot-rocq";

  release."0.3.2".sha256 = "0n7k2wcy24zc8k2wjb7f2bzv3ij32pi7cx7s7csg1axqv7w7c6bm";
  release."0.3.0".sha256 = "0xa92bcl0s8kfaci21fg8clkma4qc2n77r2xdcajqygi7isysa61";

  inherit version;
  ## 0.3.1+ require mathcomp >= 2.5.0; 0.3.0 works with mathcomp 2.3/2.4
  defaultVersion = with lib.versions; lib.switch [ coq.version mathcomp.version ] [
    { cases = [ (range "9.0" "9.1") (isGe "2.5.0") ]; out = "0.3.2"; }
    { cases = [ (range "9.0" "9.1") (range "2.3.0" "2.4.0") ]; out = "0.3.0"; }
  ] null;

  propagatedBuildInputs = [
    mathcomp.ssreflect mathcomp.fingroup mathcomp.algebra
    mathcomp.solvable mathcomp.field
    mathcomp-analysis mathcomp-real-closed mathcomp-algebra-tactics
    hierarchy-builder
  ];

  ## proof compatibility fixes for Rocq 9.2 + released mathcomp 2.6.0 /
  ## analysis 1.17.0; written against upstream master 4e8bedb4 (the
  ## Rocq 9.1 adaptation was merged upstream in robot-rocq#52)
  patches = lib.optional
    (builtins.elem version [ "master" "4e8bedb43bd20f379a27a6ef622d09912fe23953" ])
    ./mathcomp-master-compat.patch;

  meta = with lib; {
    description = "Formal foundations for modeling robot manipulators";
    license = licenses.lgpl21Plus;
  };
}
