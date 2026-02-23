From mathcomp Require Rstruct.  (* Remove this line when requiring Rocq >= 9.2 *)
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import lra ring.
From mathcomp Require boolp.
From mathcomp Require Import normedtype.
From mathcomp Require Import Rstruct reals mathcomp_extra.
From mathcomp Require Import mxalgebra.
From mathcomp Require Import landau.
From robot Require Import euclidean. 
From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba.
Require coqRE.


Require Import Coq.Reals.Reals Lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope reals_ext_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Import Order.POrderTheory Order.Theory Num.Theory GRing.Theory.

Require Import Interval.Tactic.
Require Import Program.Wf.
Require Import robustmean.
From mathcomp.algebra_tactics Require Import ring.

Section test.
Variables (R : realType) (U : finType) (P : R.-fdist U).
Variables (n : nat) (X : {RV P -> ('rV[R]_n)^o}) (Y : {RV P -> 'rV[R]_n}).
Lemma test : (Ex P X = Ex P Y).
Abort.

End test.

Section expectation.
Variables (U : finType) (P : R.-fdist U). 

Lemma Ex_add_lmod (V : lmodType R) (X Y : {RV P -> V}) :
  `E (X + Y) = `E X + `E Y.
Proof.
by rewrite linearD.
Qed.

Lemma Ex_sub_lmod (V : lmodType R) (X Y : {RV P -> V}) :
  `E (X - Y) = `E X - `E Y.
Proof.
by rewrite linearB.
Qed.

Lemma Ex_opp_lmod (V : lmodType R) (X : {RV P -> V}) :
  `E (-- X) = - `E X.
Proof.
Admitted.

Definition sub_RV_lmod (V : lmodType R) (X Y : {RV P -> V}) : {RV P -> V} :=
  fun u => X u - Y u.


Lemma Ex_const_lmod (V : lmodType R) (m : V) :
  `E (const_RV P (T := V) m) = m.
Proof.
rewrite /Ex /const_RV /=.
(* rewrite -big_distrl /=. *)
(* by rewrite FDist.f1 scale1r. *)
Admitted.

End expectation.


Section covariance. 
Local Open Scope ring_scope.
Context {R : realType}.

Variables (U : finType) (d : nat) (P : R.-fdist U) (X Y: {RV P -> 'rV[R]_d})
(V : lmodType R). 

Check `E X.
Check `E X ord0.

Definition mu : 'rV[R]_d := `E X.

Definition transpose_rv {m n :nat}
  (Y : {RV P -> 'M[R]_(m, n)} ) : {RV P -> 'M[R]_(n, m)}
  := fun u => (Y u)^T.

Notation "X ^TT" := (transpose_rv X).


Lemma E_transpose {m n} (Z : {RV P -> 'M[R]_(m,n)}) :
  `E (transpose_rv Z) = (`E Z)^T.
Proof.
  rewrite /transpose_rv /Ex /=.
  apply/matrixP=> i j.
  rewrite !mxE !summxE.
  apply: eq_bigr => u _; by rewrite !mxE.
Qed.



Definition matrix_to_rv {m n} (M : 'M[R]_(m, n)) : {RV P -> 'M[R]_(m, n)} := 
  const_RV P M. 

Coercion matrix_to_rv : matrix >-> RV_of. 

Definition mat_rv_mul {m n o} 
  (f : {RV P -> 'M[R]_(m, o)}) (g : {RV P -> 'M[R]_(o, n)}) 
  : {RV P -> 'M[R]_(m, n)} :=
  fun u => (f u) *m (g u).

Lemma matrix_to_rvE {m n} (M : 'M[R]_(m,n)) u :
  matrix_to_rv M u = M.
Proof. by rewrite /matrix_to_rv /const_RV. Qed. 

Notation "A *M B" := (mat_rv_mul A B) (at level 40, left associativity).



Lemma E_mat_scalel_RV {m n o:nat} (k : 'M[R]_(m, o)) (Z: {RV P -> 'M[R]_(o, n)}) :
   `E (k *M Z) = k *m `E Z.
Proof. 
rewrite /mat_rv_mul.
rewrite /Ex.
rewrite mulmx_sumr.
apply: eq_bigr => u _.
by rewrite scalemxAr.
Qed.

Lemma E_mat_scalel_RV_r {m n o:nat} (k : 'M[R]_(o, n)) (Z: {RV P -> 'M[R]_(m, o)}) :
   `E (Z *M (matrix_to_rv k)) = `E Z *m k.
Proof. 
rewrite /mat_rv_mul.
rewrite /Ex.
rewrite mulmx_suml.
apply: eq_bigr => u _.
by rewrite scalemxAl.
Qed.

Lemma E_mat_scale {m n o:nat} (A : 'M[R]_(m, o)) (B: 'M[R]_(o, n)):
   `E ((matrix_to_rv) A *M (matrix_to_rv B)) = `E A *m `E B.
Proof.
rewrite /matrix_to_rv /const_RV.
rewrite /mat_rv_mul.
rewrite /Ex /=.
rewrite -[ \sum_(u in U) P u *: (A *m B)]scaler_suml.
rewrite -[ \sum_(u in U) P u *: A]scaler_suml.
rewrite -[ \sum_(u in U) P u *: B]scaler_suml. 
have hP : \sum_(u in U) P u = 1.
- case: P => p /= Hp.
  move/andP: Hp => [_ /eqP hP].
  exact: hP.
rewrite hP.
by rewrite !scale1r. 
Qed. 


Lemma EE_eq_E {m n} (A : {RV P -> 'M[R]_(m, n)}) : 
  `E (`E A) = `E A. 
Proof.
  rewrite /Ex /=.
  rewrite /Ex /=.
  rewrite -[ \sum_(u in U) P u *: (\sum_(u0 in U) P u0 *: A u0)]scaler_suml.
  have hP : \sum_(u in U) P u = 1.
  - case: P => p /= Hp.
    move/andP: Hp => [_ /eqP hsum].
    exact: hsum.
  rewrite hP.
  by rewrite scale1r.
Qed.

(* Cov[X, Y] = E[(X - E[X]) (Y - E[Y])^T] *)
Definition Cov : 'M[R]_(d, d) :=
  (* transpose cannot apply on matrix/vector of "RV P -> 'rV[R]_d" *) 
  `E ((X `-cst `E X)^TT *M (Y `-cst `E Y)). 

(* 
\mathrm{Cov}[X, Y] = \mathbb{E}[X^T Y] - \mathbb{E}[X] \mathbb{E}[Y]^T
*)

Lemma trmxB {m n} (A B : 'M[R]_(m, n)) : (A - B)^T = A^T - B^T.
Proof. by apply/matrixP => i j; rewrite !mxE. Qed.

Lemma mulmxBl {m n p} (A B : 'M[R]_(m, n)) (C : 'M[R]_(n, p)) :
  (A - B) *m C = A *m C - B *m C.
Proof. by rewrite mulmxDl mulNmx. Qed.

Lemma mulmxBr {m n p} (A : 'M[R]_(m, n)) (B C : 'M[R]_(n, p)) :
  A *m (B - C) = A *m B - A *m C.
Proof. by rewrite mulmxDr mulmxN. Qed.

Lemma mat_opp_mix_transpose 
  {m n} (A: {RV P -> 'M[R]_(m, n)}) (B : 'M[R]_(m, n)) :
  (A `-cst B)^TT = A^TT `-cst B^T. 
Proof.
rewrite /transpose_rv.
rewrite /trans_sub_RV.
apply /boolp.funext=>x/=.
exact: trmxB.
Qed.

(* (A + B)^T = A^T + B^T for RV-valued matrices *)
Lemma mat_add_mix_transpose 
  {m n} (A B : {RV P -> 'M[R]_(m, n)}) :
  (A + B)^TT = A^TT + B^TT.
Proof.
  rewrite /transpose_rv /trans_add_RV.
  apply /boolp.funext=>u /=.
  apply/matrixP=> i j; by rewrite !mxE.
Qed.

Lemma mat_rv_sub_mul_mix_bl 
  {m n p} (A : {RV P -> 'M[R]_(m, n)}) (B : 'M[R]_(m, n)) (C : {RV P -> 'M[R]_(n, p)}) :
  (A `-cst B) *M C = A *M C - B *M C.
Proof.
rewrite /mat_rv_mul /matrix_to_rv /const_RV.
rewrite /trans_sub_RV.
rewrite /sub_RV_lmod.
apply/boolp.funext => u /=.
apply: mulmxBl.
Qed.

Lemma mat_rv_sub_mul_mix_br 
  {m n p} (A : {RV P -> 'M[R]_(m, n)}) (B : {RV P -> 'M[R]_(n, p)}) (C : 'M[R]_(n, p)) :
  A *M (B `-cst C) = A *M B - A *M C.
Proof.
rewrite /mat_rv_mul /matrix_to_rv /const_RV.
rewrite /trans_sub_RV /sub_RV_lmod.
apply/boolp.funext => u /=.
apply: mulmxBr.
Qed.

(* (A + B) * C = A*C + B*C for RV-valued matrices *)
Lemma mat_rv_add_mul_mix_bl 
  {m n p} (A B : {RV P -> 'M[R]_(m, n)}) (C : {RV P -> 'M[R]_(n, p)}) :
  (A + B) *M C = A *M C + B *M C.
Proof.
  rewrite /mat_rv_mul.
  apply/boolp.funext => u /=.
  exact: mulmxDl.
Qed.

Lemma mat_rv_add_mul_mix_br 
  {m n p} (A : {RV P -> 'M[R]_(m, n)}) (B C : {RV P -> 'M[R]_(n, p)}) :
  A *M (B + C) = A *M B + A *M C.
Proof.
  rewrite /mat_rv_mul.
  apply/boolp.funext => u /=.
  exact: mulmxDr.
Qed.

(* Expand (A+B)^T (C+D) *)
Lemma expand_transpose_add_mul_mix {m n: nat}
  (A C : {RV P-> 'M[R]_(m, n)}) 
  (B D : 'M[R]_(m, n)):
  (A^TT `+cst B^T) *M (C `+cst D) =
      A^TT *M C + B^T *M C + A^TT *M D + B^T *M D.
Proof.
  rewrite mat_rv_add_mul_mix_bl mat_rv_add_mul_mix_br mat_rv_add_mul_mix_br.
  rewrite -!addrA.
  congr (_ + _).
  rewrite addrCA; congr (_ + _); rewrite addrC; by [].
Qed.



Lemma expand_transpose_sub_mul_mix {m n: nat}
  (A C : {RV P-> 'M[R]_(m, n)}) 
  (B D : 'M[R]_(m, n)):
  (A^TT `-cst B^T) *M (C `-cst D) = A^TT *M C - B^T *M C - A^TT *M D + B^T *M D.
Proof.
rewrite mat_rv_sub_mul_mix_bl mat_rv_sub_mul_mix_br mat_rv_sub_mul_mix_br.
rewrite -!addrA.        (* Distribute Right again *)
congr(_ + _).
rewrite opprB addrCA.
congr(_ + _).
rewrite addrC.
by [].
Qed.


(* 
\mathrm{Cov}[X, Y] = \mathbb{E}[X^T Y] - \mathbb{E}[X] \mathbb{E}[Y]^T
*)
Lemma Cov_Ex:  
  Cov = (`E (X^TT *M Y))- (`E X)^T *m (`E Y).
Proof.
rewrite /Cov.
rewrite mat_opp_mix_transpose.
rewrite expand_transpose_sub_mul_mix. 
rewrite !(linearD (`E)) !(linearN (`E)). 
rewrite -E_mat_scalel_RV.
apply: (addrI (-(`E (X ^TT *M Y) - `E ((`E X)^T *M Y)))).
rewrite addNr. 
set Z := (`E (X^TT *M Y) - `E ((`E X)^T *M Y)).  
rewrite addrA addrA addNr add0r addrC.        (* -A + B  ->  B + -A *)
rewrite [X in _ - X] E_mat_scalel_RV_r. 
rewrite [X in X - _] E_mat_scale.
rewrite EE_eq_E. 
rewrite -[(`E X)^T](E_transpose X).
rewrite EE_eq_E.  
by rewrite subrr.
Qed. 

End covariance.

Notation "X ^TT" := (transpose_rv X).
Notation "A *M B" := (mat_rv_mul A B) (at level 40, left associativity).


Section conditional_covariance.
Context {R : realType}. 
Variables (m n d : nat).
Variables (U : finType) (P : R.-fdist U). 

Variables  (Good : {set U}) (Bad : {set U}).  (* 事件划分 *)

(*
Write indicator RV consistent with the type of RV: {RV P -> V}
For event u \in F \subset U, 
mask_RV = I_F * X = I_F(u) * X(u), denoting event F occuring "and" X. 
*)
Definition mask_RV {V : lmodType R} 
  (F : {set U}) (X : {RV P -> V}) : {RV P -> V} :=
  fun u => (Ind F u) *: X u.

(* Generic alias of [mask_RV]; kept for local proofs below *)
Definition mask_rv {V : lmodType R} (F : {set U}) (X : {RV P -> V}) :=
  mask_RV F X.

(* Mask distributes over RV subtraction *)
Lemma mask_rv_sub {V : lmodType R} (F : {set U}) (A B : {RV P -> V}) :
  mask_rv F (A `- B) = mask_rv F A `- mask_rv F B.
Proof.
  rewrite /mask_rv /mask_RV /sub_RV /=.
  apply/boolp.funext => u /=; by rewrite scalerBr.
Qed.

(* Mask distributes over RV addition *)
Lemma mask_rv_add {V : lmodType R} (F : {set U}) (A B : {RV P -> V}) :
  mask_rv F (A + B) = mask_rv F A + mask_rv F B.
Proof.
  rewrite /mask_rv /mask_RV /add_RV /=.
  apply/boolp.funext => u /=; by rewrite scalerDr.
Qed.

(* Mask commutes with transpose on vectors (seen as 1×d matrices) *)
Lemma mask_rv_transpose (F : {set U}) (Y : {RV P -> 'rV[R]_d}) :
  (mask_rv F Y)^TT = mask_rv F (Y^TT).
Proof.
  rewrite /mask_rv /mask_RV /transpose_rv.
  apply/boolp.funext => u /=.
  apply/matrixP=> i j; by rewrite !mxE.
Qed.

(* Mask pulls out of quadratic form *)
Lemma mask_rv_mul (F : {set U}) (A B : {RV P -> 'rV[R]_d}) :
  (mask_rv F A)^TT *M (mask_rv F B) = mask_rv F (A^TT *M B).
Proof.
  rewrite /mask_rv /mask_RV /mat_rv_mul /transpose_rv.
  apply/boolp.funext => u /=.
  rewrite /Ind.
  case: ifPn => _.
  - by rewrite !scale1r.
  - by rewrite !scale0r mulmx0.
Qed.

(* Mask pushes through left-constant multiplication *)
Lemma mask_rv_const_mul {m1 o1 n1} (F : {set U}) (K : 'M[R]_(m1, o1))
      (Z : {RV P -> 'M[R]_(o1, n1)}) :
  mask_rv F (K *M Z) = K *M (mask_rv F Z).
Proof.
  rewrite /mask_rv /mask_RV /mat_rv_mul /const_RV.
  apply/boolp.funext => u /=.
  rewrite /Ind.
  case: ifPn => _.
  - by rewrite !scale1r.
  - by rewrite !scale0r mulmx0.
Qed.

(* Mask pushes through right-constant multiplication *)
Lemma mask_rv_mul_const {m1 o1 n1} (F : {set U}) (Z : {RV P -> 'M[R]_(m1, o1)})
      (K : 'M[R]_(o1, n1)) :
  mask_rv F (Z *M K) = (mask_rv F Z) *M K.
Proof.
  rewrite /mask_rv /mask_RV /mat_rv_mul /const_RV.
  apply/boolp.funext => u /=.
  rewrite /Ind.
  case: ifPn => _.
  - by rewrite !scale1r.
  - by rewrite !scale0r mul0mx.
Qed.

(* 
idempotent for indicators RV:
1_F * 1_F = 1_F
*)
Lemma mask_rv_idem (F : {set U}) (W : {RV P -> 'rV[R]_d}) :
  mask_rv F (mask_rv F W) = mask_rv F W.
Proof.
  rewrite /mask_rv /mask_RV.
  apply/boolp.funext=>u/=.
  case Fu: (u \in F).
  - by rewrite /Ind Fu /= !scale1r.
  - by rewrite /Ind Fu /= !scale0r.
Qed.

(*
F \cap G = \emptyset -> 1_F(u) * 1_G(u) * X(u) = 0
*)
Lemma mask_rv_disjoint (F G : {set U}) (W : {RV P -> 'rV[R]_d}) :
  F :&: G = set0 -> mask_rv F (mask_rv G W) = const_RV P 0.
Proof.
  move=> FG0; rewrite /mask_rv /mask_RV /const_RV.
  move/setP: FG0 => FG0.
  apply/boolp.funext=>u/=.
  rewrite !/Ind.
  case Fu: (u \in F); case Gu: (u \in G); rewrite /= ?scale0r ?scale1r //.
  move: (FG0 u); rewrite !inE Fu Gu /=.
  by [].
Qed.

(* refer to cEx_ExInd in robust_mean.v: 
E(mask_RV F X) = \sum_{u\in U} P(u),1_{u \ in U} *: X(u)).
(Pr P F) <=> P(F) 
*)
Definition cEx_Ind_lmod {V : lmodType R} (F : {set U}) (X : {RV P -> V}) : 
  V :=(Pr P F)^-1 *: `E (mask_RV F X). 

Definition cEx_Ind_vec (F : {set U}) (Y : {RV P -> 'rV[R]_d}) : 'rV[R]_d :=
  cEx_Ind_lmod F Y.

(*
E[1_F Y] = P(F) E[Y | F]
*)
Lemma Emask_cEx_vec (F : {set U}) (Y : {RV P -> 'rV[R]_d}) :
  `E (mask_rv F Y) = (Pr P F) *: cEx_Ind_vec F Y.
Proof.
  rewrite /cEx_Ind_vec /cEx_Ind_lmod.
  case PF0 : (Pr P F == 0).
  - move: PF0.
    move/eqP.
    move=> PF0.
    rewrite PF0 invr0 !scale0r.
    rewrite /Ex /mask_rv /mask_RV.
    apply/rowP => i; rewrite summxE mxE.
    have hP0 : forall u, u \in F -> P u = 0.
      move=> u HuF.
      move/eqP : PF0; rewrite /Pr psumr_eq0 ?FDist.ge0 // => /allP hPF.
      have := hPF u (mem_index_enum u).
      by rewrite HuF implyTb => /eqP.
    rewrite big1 ?mxE // => u _.
    rewrite !mxE.
    case HuF: (u \in F).
    - rewrite /Ind HuF /=.
      have Pu0 := hP0 u HuF.
      by rewrite Pu0 ?mul0r ?mulr0.
    - by rewrite /Ind HuF /= ?mul0r ?mulr0.
  - have PF0' : Pr P F != 0.
      apply/negP => /eqP PF0'.
      move: PF0; by rewrite PF0' eq_refl.
    by rewrite scalerKV ?PF0'.
Qed.

Lemma Emask_cEx_mx {m0 n0} (F : {set U}) (W : {RV P -> 'M[R]_(m0,n0)}) :
  `E (mask_rv F W) = (Pr P F) *: cEx_Ind_lmod F W.
Proof.
  rewrite /cEx_Ind_lmod.
  case PF0 : (Pr P F == 0).
  - move/eqP: PF0 => PF0.
    rewrite PF0 invr0 !scale0r.
    rewrite /Ex /mask_rv /mask_RV.
    apply/matrixP => i j; rewrite !mxE.
    have hP0 : forall u, u \in F -> P u = 0.
      move=> u HuF.
      move/eqP : PF0; rewrite /Pr psumr_eq0 ?FDist.ge0 // => /allP hPF.
      have := hPF u (mem_index_enum u).
      by rewrite HuF implyTb => /eqP.
    rewrite big1; last first.
      move=> u _.
      case HuF: (u \in F).
      + rewrite /Ind HuF /=.
        have Pu0 := hP0 u HuF.
        by rewrite Pu0 scale0r.
      + by rewrite /Ind HuF /= scale0r scaler0.
    by rewrite mxE.
  - have PF0' : Pr P F != 0.
      apply/negP => /eqP PF0'.
      move: PF0; by rewrite PF0' eq_refl.
    by rewrite scalerKV ?PF0'.
Qed.

(*
For const v, E[1_F * v ] = P(F) * v
*)
Lemma E_mask_const {V : lmodType R} (F : {set U}) (v : V) :
  `E (mask_rv F (const_RV P (T := V) v)) = (Pr P F) *: v.
Proof.
  rewrite /mask_rv /mask_RV /Ex /const_RV /=.
  transitivity (\sum_(u in U) (P u * Ind F u) *: v).
    apply: eq_bigr => u _.
    by rewrite scalerA.
  rewrite -scaler_suml.
  have -> : \sum_(u in U) (P u * Ind F u) = \sum_(u in F) P u.
    rewrite [in RHS]big_mkcond /=.
    apply: eq_bigr => u _; rewrite /Ind.
    by case: ifPn => _ /=; rewrite ?mulr1 ?mulr0.
  by rewrite /Pr.
Qed.

(* Conditional Covariance Cov[Y | F] *)
(*
Cov[Y | F] = E[(1_F (Y - \mu_F)) (1_F (Y - \mu_F))^T] / P(F)
*)
Definition cCov (F : {set U}) (Y : {RV P -> 'rV[R]_d}) : 'M[R]_(d,d) :=
  let muF := cEx_Ind_vec F Y in
  (Pr P F)^-1 *:
    `E ((mask_rv F (Y `-cst muF))^TT *M (mask_rv F (Y `-cst muF))).


End conditional_covariance.


Section total_covariance. 
Context {R : realType}.
Variable d : nat.
Variables (U : finType) (P : R.-fdist U) (A : finType).
Variable B Y : {RV P -> 'rV[R]_d}.
Variable Z : {RV P -> A}.           
Variable D : 'rV[R]_d. 

(*
F_z(a) = Z^{-1}({a}) = { u \in U | Z(u) = a} 
Get the event u that makes random variable Z(u) has value a
*)
Local Notation Fz a := (finset (Z @^-1 a)).

(* 
Partition expectation by the preimage of Z 
E[W] = \sum_{a \in A} E[1_{Z = a} W] 
*)
Lemma E_partition_preim {m n} (W : {RV P -> 'M[R]_(m,n)}) :
  `E W = \sum_(a in A) `E (mask_rv (Fz a) W).
Proof.
  rewrite /Ex.
  have hZT : Z @^-1: [set: A] = [set: U].
    apply/setP => u; by rewrite !inE.
  have hpart := partition_big_preimset _ Z [set: A] (fun u => P u *: W u).
  rewrite hZT in hpart.
  have hsetT : \sum_(u in [set: U]) P u *: W u = \sum_(u in U) P u *: W u.
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => u _; rewrite inE.
  rewrite -hsetT.
  rewrite hpart /=.
  have hsetTA :
      \sum_(a in [set: A]) \sum_(u in U | Z u == a) P u *: W u =
      \sum_(a in A) \sum_(u in U | Z u == a) P u *: W u.
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => a _; rewrite inE.
  rewrite hsetTA.
  have hFzE u a0 : (u \in Fz a0) = (Z u == a0).
    by rewrite inE.
  apply: eq_bigr => a _.
  rewrite /mask_rv /mask_RV.
  rewrite [LHS]big_mkcond /=.
  apply: eq_bigr => u _.
  rewrite /Ind (hFzE u a).
  case Hz: (Z u == a).
  - by rewrite /= scale1r.
  - by rewrite /= scale0r scaler0.
Qed.

(* 
rewrite {Z = a} as an indicator random variable.
\mu_{Y | Z = a} = E [Y | Z = a] 
*)
Definition mu_given_Z a : 'rV[R]_d := cEx_Ind_vec (Fz a) Y.

(*
Regard conditional expectation as a random variable with type {RV P -> 'rV[R]_d}
*)
Definition muZ_rv : {RV P -> 'rV[R]_d} :=
  fun u => mu_given_Z (Z u).

(*
Conditional Covariance with Z = a as a normal matrix 
\Sigma_{Y | Z = a} = Cov 
*)
Definition Cov_given_Z a : 'M[R]_(d,d) :=  cCov (Fz a) Y.

(*
First Term in Law of Total Covariance: 
E[Cov (Y | Z )]
*)
Definition ECov_given_Z : 'M[R]_(d,d) :=
  \sum_(a in A) (Pr P (Fz a)) *: Cov_given_Z a.
  
Definition Cov_total_Z : 'M[R]_(d,d) :=  Cov Y Y.

(* Expectation of the piecewise-constant conditional mean RV 
E[\mu_Z] = E[E[Y | Z]] = E[Y ]
aka law of total expectation
*)
Lemma E_muZ_rv : `E muZ_rv = `E Y.
Proof.
  rewrite /muZ_rv /mu_given_Z /Ex.
  have hZT : Z @^-1: [set: A] = [set: U].
    apply/setP => u; by rewrite !inE.
  have hpart := partition_big_preimset _ Z [set: A]
      (fun u => P u *: cEx_Ind_vec (Fz (Z u)) Y).
  rewrite hZT in hpart.
  have hsetT : \sum_(u in [set: U]) P u *: cEx_Ind_vec (Fz (Z u)) Y =
               \sum_(u in U) P u *: cEx_Ind_vec (Fz (Z u)) Y.
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => u _; rewrite inE.
  rewrite -hsetT.
  rewrite hpart /=.
  have hsetTA :
      \sum_(a in [set: A]) \sum_(u in U | Z u == a)
        P u *: cEx_Ind_vec (Fz (Z u)) Y =
      \sum_(a in A) \sum_(u in U | Z u == a)
        P u *: cEx_Ind_vec (Fz (Z u)) Y.
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => a _; rewrite inE.
  rewrite hsetTA.
  rewrite (eq_bigr (fun a => (Pr P (Fz a)) *: cEx_Ind_vec (Fz a) Y)); last first.
    move=> a _; rewrite /Pr.
    have hFzE u a0 : (u \in Fz a0) = (Z u == a0).
      by rewrite inE.
    have hPrF : \sum_(u in Fz a) P u = \sum_(u in U | Z u == a) P u.
      rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
      by apply: eq_bigr => u _; rewrite (hFzE u a).
    have -> :
        \sum_(u in U | Z u == a) P u *: cEx_Ind_vec (Fz (Z u)) Y =
        \sum_(u in U | Z u == a) P u *: cEx_Ind_vec (Fz a) Y.
      rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
      apply: eq_bigr => u _.
      case Hu: (Z u == a); first by move/eqP: Hu => ->.
      by [].
    by rewrite hPrF scaler_suml.
  have EY_by_parts :
      \sum_(u in U) P u *: Y u = \sum_(a in A) `E (mask_rv (Fz a) Y).
    exact: E_partition_preim.
  rewrite EY_by_parts; apply: eq_bigr => a _.
  by rewrite Emask_cEx_vec.
Qed.

(* Expectation of the quadratic form of [muZ_rv] 
E[(E[Y | Z]) (E[Y | Z])^T] = \sum_{a \in A} P(Z = a) \mu_a \mu_a^T
where 
\mu_a = E[Y | Z = a]
*)
Lemma E_muZ_quad :
  `E (muZ_rv^TT *M muZ_rv) =
  \sum_(a in A) (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
Proof.
  rewrite /muZ_rv /mu_given_Z /Ex.
  have hZT : Z @^-1: [set: A] = [set: U].
    apply/setP => u; by rewrite !inE.
  have hpart := partition_big_preimset _ Z [set: A]
      (fun u => P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m
                        (cEx_Ind_vec (Fz (Z u)) Y))).
  rewrite hZT in hpart.
  have hsetT :
      \sum_(u in [set: U]) P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m
                                   (cEx_Ind_vec (Fz (Z u)) Y)) =
      \sum_(u in U) P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m
                            (cEx_Ind_vec (Fz (Z u)) Y)).
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => u _; rewrite inE.
  rewrite -hsetT.
  rewrite hpart /=.
  have hsetTA :
      \sum_(a in [set: A]) \sum_(u in U | Z u == a)
        P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m (cEx_Ind_vec (Fz (Z u)) Y)) =
      \sum_(a in A) \sum_(u in U | Z u == a)
        P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m (cEx_Ind_vec (Fz (Z u)) Y)).
    rewrite [LHS]big_mkcond /=.
    by apply: eq_bigr => a _; rewrite inE.
  rewrite hsetTA.
  apply: eq_bigr => a _.
  rewrite /Pr.
  have hFzE u a0 : (u \in Fz a0) = (Z u == a0).
    by rewrite inE.
  have hPrF : \sum_(u in Fz a) P u = \sum_(u in U | Z u == a) P u.
    rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
    by apply: eq_bigr => u _; rewrite (hFzE u a).
  have -> :
      \sum_(u in U | Z u == a)
        P u *: ((cEx_Ind_vec (Fz (Z u)) Y)^T *m (cEx_Ind_vec (Fz (Z u)) Y)) =
      \sum_(u in U | Z u == a)
        P u *: ((cEx_Ind_vec (Fz a) Y)^T *m (cEx_Ind_vec (Fz a) Y)).
    rewrite [LHS]big_mkcond [RHS]big_mkcond /=.
    apply: eq_bigr => u _.
    case Hu: (Z u == a); first by move/eqP: Hu => ->.
    by [].
  by rewrite hPrF scaler_suml.
Qed.

(* Masked mixed terms reduce to Pr(F) * mu^T mu 
E[1_{Z = a} \mu_a Y^T] = P(Z = a) \mu_a \mu_a^T 
where
\mu_a = E[Y | Z = a]
*)
Lemma E_mask_mu_left a :
  `E (mask_rv (Fz a) ((mu_given_Z a)^T *M Y)) =
  (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
Proof.
  rewrite mask_rv_const_mul E_mat_scalel_RV.
  by rewrite Emask_cEx_vec scalemxAr.
Qed.

Lemma E_mask_mu_right a :
  `E (mask_rv (Fz a) (Y^TT *M (mu_given_Z a))) =
  (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
Proof.
  rewrite /mu_given_Z.
  rewrite mask_rv_mul_const E_mat_scalel_RV_r.
  rewrite -mask_rv_transpose E_transpose Emask_cEx_vec.
  rewrite [((Pr P (Fz a)) *: cEx_Ind_vec (Fz a) Y)^T]linearZ /=.
  by rewrite scalemxAl.
Qed.

(*
Cov(Y) = E[Cov(Y | Z)] + Cov(E[Y | Z])
*)
Lemma law_total_covariance :
  Cov_total_Z = ECov_given_Z + Cov muZ_rv muZ_rv.
Proof.
  (* Cov in ``E[X^T Y] - EX^T EY`` form *)
  have CovY   := @Cov_Ex R U d P Y Y.
  have CovMuZ := @Cov_Ex R U d P muZ_rv muZ_rv.
  rewrite /Cov_total_Z CovY.
  rewrite /ECov_given_Z /Cov_given_Z /cCov.
  (* Move probability factor inside each summand *)
  have -> : \sum_(a in A) (Pr P (Fz a)) *:
        ((Pr P (Fz a))^-1 *:
          `E ((mask_rv (Fz a) (Y `-cst mu_given_Z a))^TT
               *M (mask_rv (Fz a) (Y `-cst mu_given_Z a)))) =
          \sum_(a in A) `E (mask_rv (Fz a)
               ((Y `-cst mu_given_Z a)^TT *M (Y `-cst mu_given_Z a))).
    apply: eq_bigr => a _.
    rewrite mask_rv_mul.
    rewrite -(@Emask_cEx_mx R U P _ _ (Fz a)
        ((Y `-cst mu_given_Z a)^TT *M (Y `-cst mu_given_Z a))).
    by rewrite /cEx_Ind_lmod.
  (* Expand the square *)
  rewrite (eq_bigr (fun a =>
     `E (mask_rv (Fz a)
        (Y^TT *M Y
          - (mu_given_Z a)^T *M Y
          - Y^TT *M (mu_given_Z a)
          + (mu_given_Z a)^T *M (mu_given_Z a))))) ; last first.
    move=> a _.
    rewrite mat_opp_mix_transpose.
    by rewrite -expand_transpose_sub_mul_mix.
  have hsplit_sum :
      \sum_(a in A)
        (@Ex R _ U P (mask_rv (Fz a)
             (Y^TT *M Y
               - (mu_given_Z a)^T *M Y
               - Y^TT *M (mu_given_Z a)
               + (mu_given_Z a)^T *M (mu_given_Z a)))) =
      \sum_(a in A)
        ((@Ex R _ U P (mask_rv (Fz a) (Y^TT *M Y)))
          - (@Ex R _ U P (mask_rv (Fz a) ((mu_given_Z a)^T *M Y)))
          - (@Ex R _ U P (mask_rv (Fz a) (Y^TT *M (mu_given_Z a))))
          + (@Ex R _ U P (mask_rv (Fz a) ((mu_given_Z a)^T *M (mu_given_Z a))))).
    apply: eq_bigr => a _.
    rewrite mask_rv_add !mask_rv_sub.
    rewrite (linearD (@Ex R _ U P)).
    rewrite (linearB (@Ex R _ U P)).
    by rewrite (linearB (@Ex R _ U P)).
  rewrite hsplit_sum.
  rewrite big_split /= !sumrB /=.
  set S1 := \sum_(a in A) `E (mask_rv (Fz a) (Y^TT *M Y)).
  set S2 := \sum_(a in A) `E (mask_rv (Fz a) ((mu_given_Z a)^T *M Y)).
  set S3 := \sum_(a in A) `E (mask_rv (Fz a) (Y^TT *M (mu_given_Z a))).
  set S4 := \sum_(a in A) `E (mask_rv (Fz a) ((mu_given_Z a)^T *M (mu_given_Z a))).
  (* S1 collapses by partition on Z *)
  have -> : S1 = `E (Y^TT *M Y) by rewrite /S1 E_partition_preim.
  (* Closed forms for S2,S3,S4 *)
  have -> : S2 = \sum_(a in A) (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
    apply: eq_bigr => a _; exact: E_mask_mu_left.
  have -> : S3 = \sum_(a in A) (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
    apply: eq_bigr => a _; exact: E_mask_mu_right.
  have -> : S4 = \sum_(a in A) (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
    apply: eq_bigr => a _.
    have -> : mask_rv (Fz a) ((mu_given_Z a)^T *M (mu_given_Z a)) =
              mask_RV (Fz a) (const_RV P ((mu_given_Z a)^T *m (mu_given_Z a))).
      apply/boolp.funext=>u /=; by rewrite /mask_RV /const_RV.
    exact: E_mask_const.
  set T := \sum_(a in A) (Pr P (Fz a)) *: ((mu_given_Z a)^T *m (mu_given_Z a)).
  (* ECov_given_Z simplifies to E[Y^T Y] - T *)
  (* Cov muZ part *)
  rewrite CovMuZ /Cov.
  rewrite E_muZ_quad E_muZ_rv.
  (* Final algebra *)
  set M := ((`E Y)^T *m `E Y).
  apply: (addrI (- `E (Y ^TT *M Y))).
  rewrite !addrA addNr !add0r.
  rewrite -!addrA.
  rewrite [(- T + (T + (T - M)))]addrA.
  rewrite addNr add0r.
  rewrite [T - M]addrC.
  rewrite addrA [(- T + - M)]addrC.
  by rewrite -addrA addNr addr0.
Qed.


End total_covariance. 

Definition eigenvalue_rv (n : nat) (g : {RV P -> 'M[R]_n}) (a: {RV P -> R}) 
 := forall u, eigenvalue (g u) (a u).

End covariance.


Section total_variation_distance. 
Variables (R : realType) (U : finType) (P Q : R.-fdist U).

Definition total_variation_distance := 
  2^-1 * \sum_(u in U) `| P u - Q u |.

End total_variation_distance.

Section additive_contamination.
(* X is an eps‑additive contamination of D if there exists a distribution E
   such that
     X = (1 - eps) * D + eps * E
where E is an error distribution. *)
Local Open Scope ring_scope.
Let R := Rdefinitions.R.
(* Context {R : realType}.  *)

(* {prob R} *)
Variables (U : finType) (V: lmodType R) (D E : R.-fdist U) (eps : {oprob R}).

Definition addtive_contamination_dist:= E <| eps |> D.

End additive_contamination.


Section stable. 
Local Open Scope ring_scope.
Context {R : realType}.
Variables (d : nat) (U : finType) (P : R.-fdist U) (X: {RV P -> 'rV[R]_d})
 (mu: 'rV[R]_d) (eps delta : R). 
Hypothesis eps012: 0 < eps < 2^-1.  
Hypothesis delta_ge_eps : delta >= eps. 

(*
Lemma Ex_fdist_cond (V : lmodType R) (X : {RV P -> V}) :
  let X' := X : {RV (fdist_cond E0) -> V} in
  `E X' = `E_[ X | E ].
Admitted.
*)

(* *d comes from robot-coq *) 
Definition stable (S : {set U}) (mu: 'rV[R]_d)  :=  
  forall (v: 'rV[R]_d), mx_norm v = 1 -> 
  forall (S' : {set U}), S' \subset S -> 
  Pr P S' >= (1 - eps) * Pr P S -> 
  ( `| (Pr P S')^-1 * \sum_(u in S') (v *d (X u - mu)) | <= delta )
&& ( `| (Pr P S')^-1 * \sum_(u in S') ((v *d (X u - mu)))^+2 - 1| 
  <= delta^+2 / eps ).

Definition stableT (mu: 'rV[R]_d)  :=  
  forall (v: 'rV[R]_d), mx_norm v = 1 -> 
  forall (S' : {set U}), Pr P S' >= (1 - eps) -> 
  ( `| (Pr P S')^-1 * \sum_(u in S') (v *d (X u - mu)) | <= delta )
&& ( `| (Pr P S')^-1 * \sum_(u in S') ((v *d (X u - mu)))^+2 - 1| 
  <= delta^+2 / eps ).


Definition stableT_rv (mu: 'rV[R]_d)  :=  
  forall (v: 'rV[R]_d), mx_norm v = 1 -> 
  forall (S' : {set U}), Pr P S' >= (1 - eps) -> 
  forall (PSneq0 : Pr P S' != 0), 
  let Q := fdist_cond PSneq0 in 
  ( `| Ex Q (fun u => (v *d (X u - mu)): R^o) | <= delta )
&& ( `| Ex Q (fun u => ((v *d (X u - mu)))^+2 : R^o)- 1| 
  <= delta^+2 / eps ).

(*we might need definition of a distribution is stable *)

Lemma stableT_eq : forall mu, @stableT mu <-> @stableT_rv mu.
Admitted. 


End stable.


Section subtractive_contamination. 
Local Open Scope ring_scope. 
Context {R : realType}. 

(* Indicator Variable here*)

(* Q is an eps‑subtractive contamination of P if there exists an event Rset
   of probability 1 - eps under P, and Q is the mixture
     Q = (1 - eps) * (P conditioned on Rset) + eps * Qadv
   where Qadv is an arbitrary adversarial distribution. *)

(* Definition subtractive_contamination (U : finType) (P Q : {fdist U}) (eps : R) : Prop :=
  exists (Rset : {set U}) (Qadv : {fdist U}),
    Pr P Rset = 1 - eps /\
    (forall u, Q u =
       (1 - eps) * (if u \in Rset then P u / Pr P Rset else 0) + eps * Qadv u).
*)

End subtractive_contamination.

(**md**************************************************************************)
(* # Bachmann-Landau notations: $f=o(e)$, $f=O(e)$                            *)
(*                                                                            *)
(* This library is very asymmetric, in multiple respects:                     *)
(* - most rewrite rules can only be rewritten from left to right.             *)
(*   e.g., an equation 'o_F f = 'O_G g can be used only from LEFT TO RIGHT    *)
(* - conversely most small 'o_F f in your goal are very specific,             *)
(*   only 'a_F f is mutable                                                   *)
(*                                                                            *)
(* Most notations are either parse only or print only.                        *)
(* Indeed all the 'O_F notations contain a function which is NOT displayed.   *)
(* This might be confusing as sometimes you might get 'O_F g = 'O_F g         *)
(* and not be able to solve by reflexivity.                                   *)
(*   - In order to have a look at the hidden function, rewrite showo.         *)
(*   - Do not use showo during a normal proof.                                *)
(*   - All theorems should be stated so that when an impossible reflexivity   *)
(*     is encountered, it is of the form 'O_F g = 'O_F g so that you          *)
(*     know you should use eqOE in order to generalize your 'O_F g            *)
(*     to an arbitrary 'O_F g                                                 *)
(*                                                                            *)
(* In this file, F is a filter and V W X Y Z are normed spaces over K.        *)
(*                                                                            *)
(* To prove that f is a bigO of g near F, you should go back to filter        *)
(* reasoning only as a last resort. To do so, use the view eqOP. Similarly,   *)
(* you can use eqaddOP to prove that f is equal to g plus a bigO of e near F  *)
(* using filter reasoning.                                                    *)
(*                                                                            *)
(* ## Parsable notations                                                      *)
(* ```                                                                        *)
(*    [bigO of f] == recovers the canonical structure of big-o of f           *)
(*                   expands to itself                                        *)
(*       f =O_F h == f is a bigO of h near F,                                 *)
(*                   this is the preferred way for statements.                *)
(*                   expands to the equation (f = 'O_F h)                     *)
(*                   rewrite from LEFT to RIGHT only                          *)
(*   f = g +O_F h == f is equal to g plus a bigO near F,                      *)
(*                   this is the preferred way for statements.                *)
(*                   expands to the equation (f = g + 'O_F h)                 *)
(*                   rewrite from LEFT to RIGHT only                          *)
(*                   /!\ When you have to prove                               *)
(*                   (f =O_F h) or (f = g +O_F h).                            *)
(*                   you must (apply: eqOE) as soon as possible in a proof    *)
(*                   in order to turn it into 'a_O_F f with a shelved content *)
(*                   /!\ under rare circumstances, a hint may do that for you *)
(*   [O_F h of f] == returns a function with a bigO canonical structure       *)
(*                   provably equal to f if f is indeed a bigO of h           *)
(*                   provably equal to 0 otherwise                            *)
(*                   expands to ('O_F h)                                      *)
(*           'O_F == pattern to match a bigO with a specific F                *)
(*             'O == pattern to match a bigO with a generic F                 *)
(* f x =O_(x \near F) e x == alternative way of stating f =O_F e (provably    *)
(*                   equal using the lemma eqOEx                              *)
(* ```                                                                        *)
(*                                                                            *)
(* WARNING: The piece of syntax "=O_(" is only valid in the syntax            *)
(*          "=O_(x \near F)", not in the syntax "=O_(x : U)".                 *)
(*                                                                            *)
(* ## Printing only notations:                                                *)
(* ```                                                                        *)
(*        {O_F f} == the type of functions that are a bigO of f near F        *)


Section law_of_total_covariance.


(* Law of total covariance *)
End law_of_total_covariance.

(*
Fromalize Lemma 2.7 in Algorithmic High-Dimensional Robust Statistics
*)
Section Certificate_for_Empirical_Mean. 
Local Open Scope ring_scope.
Context {R : realType}.
Variables (d: nat) (U : finType) (P : R.-fdist U) (V : lmodType R) 
  (X Y E: {RV P -> 'rV[R]_d}) 
  (Good : {set U})  (* good set *)
  (bad : {set U})  (* bad set *)
  (C : {ffun U -> R})

  (mu: 'rV[R]_d)
(* What is S here `b`b*)
  (S : {set U}) (eps delta lambda: R).  

Hypothesis eps0: 0 < eps. 
Hypothesis delta_ge_eps : delta >= eps. 
Hypothesis lambda0: 0 <= lambda.
(* Hypothesis X_stable_mu: *)
Hypothesis lambda_eigen: forall a, eigenvalue (Cov Y) a -> a <= 1 + lambda.
Hypothesis S_eps: Pr P S = eps.


(* Ind in proba.v *) 
(* Independence in proba.v *)
(* "Ind" in Robustmean.v *) 
(* TODO @20 Nov
  - prove ||mu_X - mu ||_2 <= delta under the defintion of stable. 
  - go through the proof of Lemma 2.7 in the paper and formalize each step.
  - Big O notation (follow up Dianonicolas)
we need 
  - use indicator function to define Y  （Proba.v section Ind.)
  - definition of conditional covariance
  - lemma, totoal covariance and total expectation 
*)




Lemma Certificate_for_Empirical_Mean : 
  exists C, mx_norm (`E Y - mu) <= C * (delta + Num.sqrt (eps * lambda)).
Proof.
pose I : {RV P -> R } := Ind S. (* move to let *)

Check I.
Check `Pr[I = 0]:R.
Check Pr P S:R.
Check Pr P S = eps.
have: `Pr[I=0] = 1 - eps.

Search `Pr[_=_] Pr.
rewrite pfwd1E.
have: finset (preim I (pred1 0)) = ~:S.
apply /setP.
move=> x. 
rewrite !inE.
rewrite /I.
rewrite /Ind.
case: ifPn => //=.
Search (1 == 0).
rewrite oner_eq0//. 
rewrite eqxx//.

(* 
- Express (\epsilon, \delat) stable distribution
- define total vartiation distance between two distributions
- define mean and covariance of distribution (multi dimensional) 
- define eigenvalues and eigenvectors of covariance matrix 
- norm_L2 
*)
Abort.


End Certificate_for_Empirical_Mean.
