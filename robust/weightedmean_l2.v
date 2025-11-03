From mathcomp Require Import all_ssreflect ssralg ssrnum matrix.
From mathcomp Require Import lra ring.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct reals mathcomp_extra.
Require Import ssr_ext ssralg_ext bigop_ext realType_ext realType_ln.
Require Import fdist proba.
Require coqRE.
Require Import Coq.Reals.Reals.


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

Section multi_random_variables.

(*TODO Does U mean the possible outcomes of the RV, which is finite *)
Variables (U : finType) (P : {fdist U}) (d : nat) (n : nat) (m: nat) (F : {set U}).
Let R := Rdefinitions.R.
(* 'I_n is a map here *)
Check 'I_d.
Locate "'I_d".

(* 'I_n is a type of n elements, which is a vector of size n, each element is an index from 0 to n-1 *)
(* vfdist is the type of all functions that, given an index i : 'I_d, return an object of type {fdist U}. *)
Definition vfdist d U := 'I_d -> {fdist U}.

Check vfdist.

(* vRV is the type of all functions that, given an index i : 'I_n, return an object of type {RV P >-> R}. *)
Definition vRV := 'I_d -> {RV P -> R}.

Check vRV. 
About vRV.

(* Definition vRV := 'rV[{RV P -> R}]_n. *)
(* Definition trans_min_vRV (X : vRV) (m : vRV): 'rV[R]_n := \row_(i < n) trans_min_RV (X i) (m i). *)
Definition vEx (X : vRV) : 'rV[R]_d := \row_(i < d) `E (X i). 

Local Notation "`EE_[ X ]" := (vEx X) (at level 1).

Definition mEx m n (P: {fdist U}) (X : 'M[{RV P -> R}]_(m,n)) : 'M[R]_(m,n) := 
  \matrix_(i < m, j < n) `E (X i j). 

Notation "'mE_ P [ X ]" := (@mEx _ _ P X). 

(* TODO What is F G z %R here*)
Definition mulmxfun [m n p] (A : 'M[{RV P -> R}]_(m,n)) (B : 'M[{RV P -> R}]_(n,p)) F G z: 'M[{RV P -> R}]_(m,p) := 
  \matrix_(i, k) \big[F/z]_j (G (A i j) (B j k))%R. 

(* TODO dimension problem,  
why the input of a covariance matrix is a matrix of random variables, isn't it a vector of random variables?
or does it mean for n x p matrix, there are n random variables and p samples for each rv?
*) 

Context (X : 'M[{RV P -> R}]_(m,n)) (Y : 'M[{RV P -> R}]_(m,n)). 

(* TODO what is cst here *)
(* Definition A : 'rV[{RV P -> R}]_n:= \row_(i < n) (X i  `-cst `E (X i)).*)
(* Definition B : 'rV[{RV P -> R}]_n := \row_(i < n) (Y i `-cst `E (X i)). *)

Definition A : 'M[{RV P -> R}]_(m,n) :=  \matrix_(i < m, j < n) ((X i j) `-cst `E (X i j)).  
Definition B : 'M[{RV P -> R}]_(m,n) :=  \matrix_(i < m, j < n) ((Y i j) `-cst `E (X i j)).   

(* TODO deal with constRV P 0 better *)
Definition matrix_covariance (X : vRV) (Y: vRV) := 
  'mE_P[ mulmxfun A B^T (GRing.add_fun) (GRing.mul_fun) (const_RV P 0) ]%R. 

(* conditional expectation*)
Definition cEx_v (X : vRV) : 'rV[R]_d := \row_(i < d) `E_[ X i | F ].

Check 'rV[R]_d.

Check cEx_v.

Local Notation "`EE_[ X | F ]" := (cEx_v X F) (at level 1). 

(* Output should be a vec  *)
(* Definition Cov_rv (X Y : vRV) : R := \sum_(i < d) \sum_(j < n) (`E ((X i) `* (Y j)) - `E (X i) * `E (Y j)). *)

(*
Definition cVar_rv (X : vRV) F := 
  let mu := `EE_[X | F] in
  `E_[(X `-cst mu) `^2 | F]. (*TODO what does -cst do here*)
*)

(* Definition l2_norm (X : vRV) : R := Num.sqrt (\sum_(i < n) `E ((X i)`^2)).  *)

Definition vfinType : Type := 'I_d -> U. 


Check vfinType.

(* TODO what is the type of wgt? *)

End multi_random_variables.


Module Weighted.
Section def.
Local Open Scope ring_scope.
Let R := Rdefinitions.R.
Variables (d : nat).
Variables (A : finType) (d0 : {fdist A}) (g_d : 'I_d -> {ffun A -> R}).

Hypothesis g0 : forall (i : 'I_d) (a : A), 0 <= g_d i a. 

Definition total : 'rV[R]_d :=
  \row_(i < d) \sum_(a in A) (g_d i a * d0 a).

Definition total_i (i : 'I_d) := total (inord 0) i.

Hypothesis total_each_neq0 : forall i : 'I_d, total_i i != 0.


Lemma total_gt0 : forall i : 'I_d, 0 < total_i i.
Proof.
  move=> i.
  have ge0 : 0 <= total_i i.
  { rewrite /total_i /total mxE.
    (* 用 big_ind（布尔序）证明和的非负：基、加法保非负、每项非负 *)
    elim/big_ind : _ => [|x y Hx Hy|a _].
    - by apply: lexx 0.                       (* 0 <= 0 *)
    - by apply: addr_ge0.                   (* Hx,Hy -> 0 <= x+y *)
    - by apply: mulr_ge0; [apply: g0 | apply: FDist.ge0].  (* 每项 ≥ 0 *)
  }
  have nz : total_i i != 0 := total_each_neq0 i.
  by rewrite lt_def ge0 andbT (negbTE nz).
Qed.

Lemma total_le1 : (forall (i : 'I_d) (a : A), a \in A -> g_d i a <= 1) ->
  forall i : 'I_d, total_i i <= 1.
Proof.
  move=> g1 i.
  rewrite /total_i /total mxE.
  have step1 : \sum_(a in A) (g_d i a * d0 a) <= \sum_(a in A) 1 * d0 a.
  { apply: ler_sum => a aInA.
    have Hg : g_d i a <= 1 := g1 i a aInA.
    have Hd : 0 <= d0 a := FDist.ge0 d0 a. 
    rewrite ler_pM; last by [].  
    by [].            
    by apply: g0.     (* 0 <= g_d i a *)
    by apply: FDist.ge0. (* 0 <= d0 a *)
    by apply: g1.     (* g_d i a <= 1 *)
  }
Admitted.

End def.
End Weighted.

(* TODO what is the type of wgt? *)


Module Split.

Section def.


End def.

End Split.


Section empirical.  (* TODO, why when merge with the section above, there was error *)
Variables (U : finType) (P : {fdist U}) (n : nat). 

(* Context is variable *)
Context (f : nneg_finfun U) (f0 : Weighted.total P f != 0).

Definition P' := wgt f0.

Definition emprirical_mean (X : vRV P n) := vEx (X : vRV P' n). 
Definition empirical_cov (X : vRV P n ) := Cov_rv (X : vRV P' n) (X : vRV P' n).

End empirical. 



Section robustmean_l2.

Variables (U : finType) (P : {fdist U}) (n : nat) .

(* Lemma 2.6 *) 
(* Hø̈lder’s inequality in mathcomp/analysis *) 


(*
Theorem robust_mean_l2 (good drop: {set U}) (X : vRV P n) (eps : R):  
    let bad := ~: good in 
    let mu_hat := cEx_v X (~: drop) in (* TODO why do we need this conditional mean?*) 
    let mu := cEx_v X good in
*)


End robustmean_l2.

