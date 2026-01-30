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

Section test.
Variables (R : realType) (U : finType) (P : R.-fdist U).
Variables (n : nat) (X : {RV P -> ('rV[R]_n)^o}) (Y : {RV P -> 'rV[R]_n}).
Lemma test : (Ex P X = Ex P Y).
Abort.

End test.

Section expectation.
Variables (U : finType) (P : R.-fdist U). 

Lemma Ex_add_lmod (V : lmodType R) (X Y : {RV P -> V}) :
  `E (X `+ Y) = `E X + `E Y.
Proof.
rewrite /Ex /add_RV.
rewrite -big_split.
by apply: eq_bigr => u _; rewrite scalerDr.
Qed.

Lemma Ex_opp_lmod (V : lmodType R) (X : {RV P -> V}) :
  `E (`-- X) = - `E X.
Proof.
rewrite /Ex /opp_RV.
(* rewrite big_morph_oppr /=. *)
(* by apply: eq_bigr => u _; rewrite scalerN. *)
Admitted.

Definition sub_RV_lmod (V : lmodType R) (X Y : {RV P -> V}) : {RV P -> V} :=
  fun u => X u - Y u.

Lemma Ex_sub_lmod (V : lmodType R) (X Y : {RV P -> V}) :
  `E (sub_RV_lmod X Y) = `E X - `E Y.
Proof.
rewrite /sub_RV_lmod.
(* rewrite (sub_RV_neg X Y). *)
(* rewrite Ex_add_lmod. *)
Admitted.

Lemma Ex_const_lmod (V : lmodType R) (m : V) :
  `E (const_RV P (T := V) m) = m.
Proof.
rewrite /Ex /const_RV /=.
(* rewrite -big_distrl /=. *)
(* by rewrite FDist.f1 scale1r. *)
Admitted.

End expectation.

Locate addrA. 
About addrA.

Search (_ + (_ - _) = _ + _ - _).

Section Expand.
Variable R : ringType.
Variables (m n p : nat).
Variables (A B : 'M[R]_(m, n)) (C D : 'M[R]_(m, n)).

Lemma my_addrB (T : zmodType) (x y z : T) :
  x + (y - z) = x + y - z.
Proof. 
  rewrite addrA. 
  by [].
Qed.

Locate "*m".

Lemma expand_transpose_sub_mul :
  (A^T - B^T) *m (C - D)
  = A^T *m C - B^T *m C - A^T *m D + B^T *m D.
Proof.
  rewrite mulmxBl.
  rewrite mulmxBr.
rewrite mulmxBr.        (* Distribute Right again *)
rewrite opprB.   (* Fixes the sign:  ... + (B^T D - B^T C) ... *)
rewrite addrA.   (* Removes parens:  ... + B^T D - B^T C ...   *)
rewrite addrAC.  (* Swaps middle:    ... - B^T C + B^T D ...   *)
rewrite addrAC.  (* Swaps end:       ... - A^T D + B^T D       *)
by ring.
set t1 := A^T *m C.
set t2 := B^T *m C.
set t3 := A^T *m D.
set t4 := B^T *m D.
Admitted.
End Expand.



Section covariance. 
Local Open Scope ring_scope.
Context {R : realType}.

Variables (U : finType) (d : nat) (P : R.-fdist U) (X Y: {RV P -> 'rV[R]_d}). 

Check `E X.
Check `E X ord0.
(* Check `E ((X `-cst `E X)^T *m (X `-cst `E X)^T). *)

Locate "`-cst". 

About "`-cst".

Definition mu : 'rV[R]_d := `E X.

Definition transpose_rv {m n :nat}
  (Y : {RV P -> 'M[R]_(m, n)} ) : {RV P -> 'M[R]_(n, m)}
  := fun u => (Y u)^T.

Local Notation "X ^TT" := (transpose_rv X).

Check (X `-cst mu)^TT.
Check Y^TT.

Definition matmul_rv {m n o:nat} 
  (Y : {RV P -> 'M[R]_(m, o)}) (Z : {RV P -> 'M[R]_(o, n)}) 
  :{RV P -> 'M[R]_(m, n)} := 
  fun u => (Y u) *m (Z u).

Local Notation "Y *M Z" := (matmul_rv Y Z) (at level 40, left associativity).

Check (X `-cst mu)^TT *M (Y `-cst `E Y).


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
Admitted.


Check mulmxDr.


Lemma Cov_Ex:  
  Cov = (`E (X^TT *M Y))- (`E X)^T *m (`E Y).
Proof.
rewrite /Cov.
rewrite mat_opp_mix_transpose.
Qed.


Check eigenvalue.
Print eigenvalue.
Print eigenspace. 

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
