From mathcomp Require Rstruct.  (* Remove this line when requiring Rocq >= 9.2 *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix mxalgebra.
From mathcomp Require Import sesquilinear spectral complex.
From mathcomp Require Import Rstruct reals mathcomp_extra.
Import GRing.Theory Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope sesquilinear_scope.
Local Open Scope complex_scope.

(*
Rayleigh quotient bound for real symmetric matrices, proved via the
spectral theorem for Hermitian matrices (mathcomp's spectral.v), by
complexifying A into R[i] and transporting the eigenvalue bound back
along the real embedding real_complex R : R -> R[i].
*)

Section real_complex_helpers.
Variable R : realType.

(* R[i] gets a numClosedFieldType structure because realType coerces
   to rcfType; the lemmas below only use that coercion. *)

Lemma real_complex_sum (n : nat) (E : 'I_n -> R) :
  (\sum_k E k)%:C = \sum_k (E k)%:C.
Proof.
by rewrite (big_morph (real_complex R) (rmorphD (real_complex R)) (rmorph0 (real_complex R))).
Qed.

Lemma real_complex_mulmx_mx (m n p : nat) (X : 'M[R]_(m,n)) (Y : 'M[R]_(n,p)) :
  map_mx (real_complex R) X *m map_mx (real_complex R) Y = map_mx (real_complex R) (X *m Y).
Proof.
apply/matrixP => i j.
rewrite !mxE (@real_complex_sum n (fun k => X i k * Y k j)).
by apply: eq_bigr => k _; rewrite rmorphM !mxE.
Qed.

Lemma real_complex_mulmx (m n p : nat) (X : 'M[R]_(m,n)) (Y : 'M[R]_(n,p)) i j :
  ((X *m Y) i j)%:C = (map_mx (real_complex R) X *m map_mx (real_complex R) Y) i j.
Proof.
rewrite !mxE (@real_complex_sum n (fun k => X i k * Y k j)).
by apply: eq_bigr => k _; rewrite rmorphM !mxE.
Qed.

Lemma real_conjC_fix (m n : nat) (M : 'M[R]_(m,n)) :
  (map_mx (real_complex R) M)^t* = map_mx (real_complex R) (M^T).
Proof.
apply/matrixP => i j.
rewrite !mxE.
apply/eqP.
by rewrite -CrealE; apply/complex_realP; exists (M j i).
Qed.

End real_complex_helpers.

Section rayleigh.
Context {R : realType} (d : nat).
Variable A : 'M[R]_d.
Hypothesis Asym : A^T = A.
Variable lambda_max : R.
Hypothesis lambda_max_spec : forall a, eigenvalue A a -> a <= lambda_max.

(*
Rayleigh quotient
RQ(v) = v^T A v / v^T v
*)
Definition RQ (v : 'rV[R]_d) : R :=
  (v *m A *m v^T) (@ord0 0) (@ord0 0) / (v *m v^T) (@ord0 0) (@ord0 0).

Let Ac : 'M[R[i]]_d := map_mx (real_complex R) A.

(* ------------------------------------------------------------------ *)
(* Complexification of A is Hermitian and normal                      *)
(* ------------------------------------------------------------------ *)

Lemma Ac_real : Ac \is a (mxOver Num.real).
Proof.
apply/mxOverP => i j; rewrite mxE.
by apply/complex_realP; exists (A i j).
Qed.

Lemma Ac_sym : Ac \is symmetricmx.
Proof.
rewrite qualifE /= expr0 scale1r /Ac.
by rewrite map_trmx Asym map_mx_id.
Qed.

Lemma Ac_herm : Ac \is hermsymmx.
Proof. exact: realsym_hermsym Ac_sym Ac_real. Qed.

Lemma Ac_normal : Ac \is normalmx.
Proof. exact: hermitian_normalmx Ac_herm. Qed.

(* ------------------------------------------------------------------ *)
(* A coordinate axis is an eigenvector of a diagonal matrix            *)
(* ------------------------------------------------------------------ *)

Lemma delta_mx_diag_eigen (sp : 'rV[R[i]]_d) (i0 : 'I_d) :
  delta_mx (@ord0 0) i0 *m diag_mx sp = sp (@ord0 0) i0 *: delta_mx (@ord0 0) i0.
Proof.
rewrite mul_mx_diag.
apply/matrixP => x y.
rewrite !mxE (ord1 x) eqxx /=.
case: eqP => [-> | _]; last by rewrite mul0r mulr0.
by rewrite mulrC.
Qed.

(* Every spectral diagonal entry of a normal matrix is one of its
   eigenvalues, witnessed by the corresponding row of the spectral
   (unitary) change-of-basis matrix. *)
Lemma eigen_spectral (M : 'M[R[i]]_d) (Mnormal : M \is normalmx) (i0 : 'I_d) :
  eigenvalue M (spectral_diag M (@ord0 0) i0).
Proof.
apply/eigenvalueP.
pose P := spectralmx M.
pose sp := spectral_diag M.
pose v := delta_mx (@ord0 0) i0 *m P.
have AeqPD : M = invmx P *m diag_mx sp *m P.
  exact/orthomx_spectralP.
have Punit : P \in unitmx := unitarymx_unit (spectral_unitarymx M).
have PPV : P *m invmx P = 1%:M := mulmxV Punit.
exists v.
- have step1 : v *m M = delta_mx (@ord0 0) i0 *m (P *m invmx P) *m diag_mx sp *m P.
    by rewrite /v AeqPD !mulmxA.
  rewrite step1 PPV mulmx1 delta_mx_diag_eigen.
  by rewrite /v scalemxAl.
- apply/eqP => v0.
  have hd0 : delta_mx (@ord0 0) i0 = (0 : 'rV[R[i]]_d).
    by rewrite -(mulmxK Punit (delta_mx (@ord0 0) i0)) -/v v0 mul0mx.
  move/matrixP: hd0 => /(_ (@ord0 0) i0) h1.
  rewrite !mxE !eqxx /= in h1.
  move/eqP: h1.
  by rewrite oner_eq0.
Qed.

(* ------------------------------------------------------------------ *)
(* Complex quadratic-form expansions along a unitary eigenbasis        *)
(* ------------------------------------------------------------------ *)

Lemma cqf_diag (w sp : 'rV[R[i]]_d) :
  (w *m (diag_mx sp) *m w^t*) (@ord0 0) (@ord0 0)
  = \sum_i (sp (@ord0 0) i * (w (@ord0 0) i * (w (@ord0 0) i)^*)).
Proof.
rewrite -mulmxA mul_diag_mx !mxE.
apply: eq_bigr => i _.
by rewrite !mxE mulrCA.
Qed.

Lemma cqf_self (w : 'rV[R[i]]_d) :
  (w *m w^t*) (@ord0 0) (@ord0 0) = \sum_i (w (@ord0 0) i * (w (@ord0 0) i)^*).
Proof.
rewrite mxE.
apply: eq_bigr => i _.
by rewrite !mxE.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridge: the real eigenvalue bound on A transports to the complex    *)
(* spectral diagonal of Ac, via mathcomp's eigenvalue_map              *)
(* ------------------------------------------------------------------ *)

Lemma spc_bound (i0 : 'I_d) :
  exists2 k : R, spectral_diag Ac (@ord0 0) i0 = k%:C & k <= lambda_max.
Proof.
have spc_real : spectral_diag Ac \is a (mxOver Num.real) :=
  hermitian_spectral_diag_real Ac_herm.
have hreal : spectral_diag Ac (@ord0 0) i0 \is Num.real.
  by move/mxOverP: spc_real => /(_ (@ord0 0) i0).
move/complex_realP: hreal => [k hk].
exists k => //.
have eig_i0 : eigenvalue Ac (spectral_diag Ac (@ord0 0) i0) :=
  eigen_spectral Ac_normal i0.
rewrite hk in eig_i0.
have eig_map := eigenvalue_map (real_complex R) A k.
have eig_A_k : eigenvalue A k.
  by rewrite -eig_map.
exact: (lambda_max_spec eig_A_k).
Qed.

(* ------------------------------------------------------------------ *)
(* Real quadratic-form helpers (self-contained, no robot/euclidean)    *)
(* ------------------------------------------------------------------ *)

Lemma qf_self_R (u : 'rV[R]_d) : (u *m u^T) (@ord0 0) (@ord0 0) = \sum_i (u (@ord0 0) i)^+2.
Proof.
rewrite mxE.
apply: eq_bigr => i _.
by rewrite !mxE expr2.
Qed.

Lemma qf_self_pos (u : 'rV[R]_d) : u != 0 -> 0 < (u *m u^T) (@ord0 0) (@ord0 0).
Proof.
move=> u0.
rewrite qf_self_R.
have hge0 : forall i : 'I_d, true -> 0 <= (u (@ord0 0) i)^+2.
  by move=> i _; exact: sqr_ge0.
rewrite lt0r.
apply/andP; split; last first.
  by apply: sumr_ge0 => i _; exact: sqr_ge0.
apply/eqP => hsum0.
move/eqP: u0; apply.
apply/matrixP => x y.
rewrite (ord1 x) mxE.
have h0 := psumr_eq0P hge0 hsum0.
have h0y := h0 y isT.
by move/eqP: h0y; rewrite sqrf_eq0 => /eqP.
Qed.

(* ------------------------------------------------------------------ *)
(* Real <-> complex quadratic-form comparison                          *)
(* ------------------------------------------------------------------ *)

Lemma realA (v : 'rV[R]_d) :
  ((v *m A *m v^T) (@ord0 0) (@ord0 0))%:C
  = (map_mx (real_complex R) v *m Ac *m (map_mx (real_complex R) v)^t*) (@ord0 0) (@ord0 0).
Proof.
have hconj : (map_mx (real_complex R) v)^t* = map_mx (real_complex R) v^T.
  apply/matrixP => i j.
  rewrite !mxE.
  apply/eqP.
  by rewrite -CrealE; apply/complex_realP; exists (v j i).
rewrite hconj /Ac.
rewrite real_complex_mulmx_mx real_complex_mulmx_mx mxE.
rewrite (@real_complex_sum R d _) [RHS]mxE [in RHS]mxE (@real_complex_sum R d _).
apply: eq_bigr => j _.
by rewrite rmorphM.
Qed.

Lemma realI (v : 'rV[R]_d) :
  ((v *m v^T) (@ord0 0) (@ord0 0))%:C
  = (map_mx (real_complex R) v *m (map_mx (real_complex R) v)^t*) (@ord0 0) (@ord0 0).
Proof.
have hconj : (map_mx (real_complex R) v)^t* = map_mx (real_complex R) v^T.
  apply/matrixP => i j.
  rewrite !mxE.
  apply/eqP.
  by rewrite -CrealE; apply/complex_realP; exists (v j i).
rewrite hconj.
exact: real_complex_mulmx.
Qed.

(* ------------------------------------------------------------------ *)
(* Main theorem                                                        *)
(* ------------------------------------------------------------------ *)

(*
Property of the Rayleigh Quotient:
v != 0 -> v^T A v / v^T v <= lambda_max,
whenever A is symmetric and lambda_max bounds every eigenvalue of A.
*)
Theorem rayleigh_le_max (v : 'rV[R]_d) : v != 0 -> RQ v <= lambda_max.
Proof.
move=> v0.
pose vc : 'rV[R[i]]_d := map_mx (real_complex R) v.
pose P := spectralmx Ac.
pose sp := spectral_diag Ac.
pose w : 'rV[R[i]]_d := vc *m P^t*.
have AeqPD : Ac = invmx P *m diag_mx sp *m P := (orthomx_spectralP Ac_normal).
have Punitary : P \is unitarymx := spectral_unitarymx Ac.
have Punit : P \in unitmx := unitarymx_unit Punitary.
have invPeq : invmx P = P^t* := invmx_unitary Punitary.
have AeqPtDP : Ac = P^t* *m diag_mx sp *m P by rewrite AeqPD invPeq.
have PtP : P^t* *m P = 1%:M by rewrite -invPeq mulVmx.
have hwt : P *m vc^t* = w^t*.
  by rewrite /w trmx_mul map_mxM trmxCK.
have numC_eq : vc *m Ac *m vc^t* = w *m diag_mx sp *m w^t*.
  have step1 : vc *m Ac *m vc^t* = vc *m (P^t* *m diag_mx sp *m P) *m vc^t*.
    by rewrite AeqPtDP.
  have step2 : vc *m (P^t* *m diag_mx sp *m P) *m vc^t*
             = (vc *m P^t*) *m diag_mx sp *m (P *m vc^t*).
    by rewrite !mulmxA.
  by rewrite step1 step2 hwt.
have denC_eq : vc *m vc^t* = w *m w^t*.
  have step1 : w *m w^t* = vc *m P^t* *m (P *m vc^t*).
    by rewrite {1}/w hwt.
  rewrite step1 mulmxA -(mulmxA vc) PtP mulmx1.
  by [].
have numC : ((v *m A *m v^T) (@ord0 0) (@ord0 0))%:C
          = \sum_i (sp (@ord0 0) i * (w (@ord0 0) i * (w (@ord0 0) i)^*)).
  by rewrite (realA v) numC_eq cqf_diag.
have denC : ((v *m v^T) (@ord0 0) (@ord0 0))%:C
          = \sum_i (w (@ord0 0) i * (w (@ord0 0) i)^*).
  by rewrite (realI v) denC_eq cqf_self.
have term_le : forall i0, sp (@ord0 0) i0 * (w (@ord0 0) i0 * (w (@ord0 0) i0)^*)
             <= lambda_max%:C * (w (@ord0 0) i0 * (w (@ord0 0) i0)^*).
  move=> i0.
  have [k hk hkle] := spc_bound i0.
  rewrite hk.
  apply: ler_wpM2r; first exact: mulcJ_ge0.
  by rewrite lecR.
have sum_le : \sum_i (sp (@ord0 0) i * (w (@ord0 0) i * (w (@ord0 0) i)^*))
            <= \sum_i (lambda_max%:C * (w (@ord0 0) i * (w (@ord0 0) i)^*)).
  by apply: ler_sum => i0 _; exact: term_le.
have mainC : ((v *m A *m v^T) (@ord0 0) (@ord0 0))%:C
           <= lambda_max%:C * ((v *m v^T) (@ord0 0) (@ord0 0))%:C.
  rewrite numC denC mulr_sumr.
  exact: sum_le.
have main_real : (v *m A *m v^T) (@ord0 0) (@ord0 0)
              <= lambda_max * (v *m v^T) (@ord0 0) (@ord0 0).
  move: mainC.
  by rewrite -rmorphM lecR.
rewrite /RQ.
rewrite ler_pdivrMr; last exact: qf_self_pos v0.
exact: main_real.
Qed.

End rayleigh.
