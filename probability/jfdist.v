(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg fingroup perm finalg matrix.
From mathcomp Require boolp.
From mathcomp Require Import Rstruct.
Require Import Reals.
Require Import ssrR Reals_ext logb ssr_ext ssralg_ext bigop_ext Rbigop fdist.
Require Import proba.

(******************************************************************************)
(*        Conditional probabilities over joint finite distributions           *)
(*                                                                            *)
(*       \Pr_P [ A | B ] == conditional probability of A given B where P is a *)
(*                          joint distribution                                *)
(*  jfdist_cond0 PQ a a0 == The conditional distribution derived from PQ      *)
(*                          given a; PQ is a joint distribution               *)
(*                          {fdist A * B}, a0 is a proof that                 *)
(*                          fdist_fst PQ a != 0, the result is a              *)
(*                          distribution {fdist B}                            *)
(*      jfdist_cond PQ a == The conditional distribution derived from PQ      *)
(*                          given a; same as jfdist_cond0 when                *)
(*                          fdist_fst PQ a != 0.                              *)
(*           PQ `(| a |) == notation jfdist_cond PQ a                         *)
(*      jfdist_prod_type == pair of a fdist and a stochastic matrix           *)
(*           jfdist_prod == fdist_prop of jfdist_prod_type                    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\Pr_ P [ A | B ]" (at level 6, P, A, B at next level,
  format "\Pr_ P [ A  |  B ]").
Reserved Notation "\Pr_[ A | B ]" (at level 6, A, B at next level,
  format "\Pr_[ A  |  B ]").
Reserved Notation "P `(| a ')'" (at level 6, a at next level, format "P `(| a )").

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope R_scope.
Local Open Scope proba_scope.
Local Open Scope fdist_scope.

Lemma jfdist_RV2 (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) : fdistX `d_[% X, Y] = `d_[% Y, X].
Proof. by rewrite /fdistX /dist_of_RV fdistmap_comp. Qed.

Module Self.
Section def.
Variable (A : finType) (P : {fdist A}).
Definition f := [ffun a : A * A => if a.1 == a.2 then P a.1 else 0].
Lemma f0 x : 0 <= f x.
Proof. rewrite /f ffunE; case: ifPn => [/eqP -> //| _]; exact: leRR. Qed.
Lemma f1 : \sum_(x in {: A * A}) f x = 1.
Proof.
rewrite (eq_bigr (fun a => f (a.1, a.2))); last by case.
rewrite -(pair_bigA _ (fun a1 a2 => f (a1, a2))) /=.
rewrite -(FDist.f1 P); apply/eq_bigr => a _.
under eq_bigr do rewrite ffunE.
rewrite /= (bigD1 a) //= eqxx.
by rewrite big1 ?addR0 // => a' /negbTE; rewrite eq_sym => ->.
Qed.
Definition d : {fdist A * A} := locked (FDist.make f0 f1).
Lemma dE a : d a = if a.1 == a.2 then P a.1 else 0.
Proof. by rewrite /d; unlock; rewrite ffunE. Qed.
End def.
Section prop.
Variables (A : finType) (P : {fdist A}).
Lemma fst : (d P)`1 = P.
Proof.
apply/fdist_ext => a /=; rewrite fdist_fstE (bigD1 a) //= dE eqxx /=.
by rewrite big1 ?addR0 // => a' /negbTE; rewrite dE /= eq_sym => ->.
Qed.
Lemma swap : fdistX (d P) = d P.
Proof.
apply/fdist_ext => -[a1 a2].
by rewrite fdistXE !dE /= eq_sym; case: ifPn => // /eqP ->.
Qed.
End prop.
End Self.

Definition ex2C (T : Type) (P Q : T -> Prop) : @ex2 T P Q <-> @ex2 T Q P.
Proof. by split; case=> x H0 H1; exists x. Qed.

Module TripA.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition f (x : A * B * C) := (x.1.1, (x.1.2, x.2)).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {fdist A * (B * C)} := fdistmap f P.
Lemma dE x : d x = P (x.1, x.2.1, x.2.2).
Proof.
case: x => a [b c]; rewrite /d fdistmapE /= -/(f (a, b, c)) big_pred1_inj //.
exact/inj_f.
Qed.

Lemma domin a b c : d (a, (b, c)) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (a, (b, c)) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin H. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma fst : (d P)`1 = (P`1)`1.
Proof. by rewrite /fdist_fst /d 2!fdistmap_comp. Qed.

Lemma fst_snd : ((d P)`2)`1 = (P`1)`2.
Proof. by rewrite /d /fdist_snd /fdist_fst /= !fdistmap_comp. Qed.

Lemma snd_snd : ((d P)`2)`2 = P`2.
Proof. by rewrite /d /fdist_snd !fdistmap_comp. Qed.

Lemma snd_swap : (fdistX (d P))`2 = (P`1)`1.
Proof. by rewrite /d /fdist_snd /fdistX /fdist_fst /= 3!fdistmap_comp. Qed.

Lemma snd_fst_swap : ((fdistX (d P))`1)`2 = P`2.
Proof. by rewrite /fdist_snd /fdist_fst /fdistX !fdistmap_comp. Qed.

Lemma imset E F G : [set f x | x in (E `* F) `* G] = E `* (F `* G).
Proof.
apply/setP=> -[a [b c]]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /f !inE !xpair_eqE /= => /andP [] /eqP -> /andP [] /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [aE /andP [bF cG]]; exists ((a, b), c); rewrite // !inE /= aE bF cG.
Qed.

Lemma Pr E F G : Pr (d P) (E `* (F `* G)) = Pr P (E `* F `* G).
Proof. by rewrite /d (Pr_fdistmap (@inj_f A B C)) imset. Qed.

End prop.
End TripA.
Arguments TripA.inj_f {A B C}.

Module TripA'.
Section def.
Variables (A B C : finType) (P : {fdist A * (B * C)}).
Definition f (x : A * (B * C)) := (x.1, x.2.1, x.2.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[? [? ?]] [? [? ?]] /= [-> -> ->]. Qed.
Definition d : {fdist A * B * C} := fdistmap f P.
Lemma dE x : d x = P (x.1.1, (x.1.2, x.2)).
Proof.
case: x => -[a b] c; rewrite /d fdistmapE /= -/(f (a, (b, c))).
by rewrite (big_pred1_inj inj_f).
Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * (B * C)}).
Lemma Pr a b c : Pr P (a `* (b `* c)) = Pr (d P) ((a `* b) `* c).
Proof.
rewrite /Pr !big_setX /=; apply eq_bigr => a0 _.
rewrite !big_setX; apply eq_bigr => b0 _; apply eq_bigr => c0 _; by rewrite dE.
Qed.
End prop.
End TripA'.
Arguments TripA'.inj_f {A B C}.

Module TripC12.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Let f (x : A * B * C) := (x.1.2, x.1.1, x.2).
Lemma inj_f : injective f.
Proof. by rewrite /f => -[[? ?] ?] [[? ?] ?] /= [-> -> ->]. Qed.
Definition d : {fdist B * A * C} := fdistmap f P.
Lemma dE x : d x = P (x.1.2, x.1.1, x.2).
Proof.
case: x => -[b a] c; rewrite /d fdistmapE /= -/(f (a, b, c)).
by rewrite (big_pred1_inj inj_f).
Qed.

Lemma snd : d`2 = P`2.
Proof. by rewrite /fdist_snd /d fdistmap_comp. Qed.

Lemma fst : d`1 = fdistX (P`1).
Proof. by rewrite /fdist_fst /d /fdistX 2!fdistmap_comp. Qed.

Lemma fstA : (TripA.d d)`1 = (P`1)`2.
Proof. by rewrite /fdist_fst /TripA.d /fdist_snd !fdistmap_comp. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Lemma dI : d (d P) = P.
Proof.
rewrite /d fdistmap_comp (_ : _ \o _ = ssrfun.id) ?fdistmap_id //.
by rewrite boolp.funeqE => -[[]].
Qed.
Lemma Pr E F G : Pr (d P) (E `* F `* G) = Pr P (F `* E `* G).
Proof.
rewrite /Pr !big_setX /= exchange_big; apply eq_bigr => a aF.
by apply eq_bigr => b bE; apply eq_bigr => c cG; rewrite dE.
Qed.
End prop.
End TripC12.

Module TripAC.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition f := fun x : A * B * C => (x.1.1, x.2, x.1.2).
Lemma inj_f : injective f. Proof. by move=> -[[? ?] ?] [[? ?] ?] [-> -> ->]. Qed.
Definition d : {fdist A * C * B} := fdistX (TripA.d (TripC12.d P)).
Lemma dE x : d x = P (x.1.1, x.2, x.1.2).
Proof. by case: x => x1 x2; rewrite /d fdistXE TripA.dE TripC12.dE. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).

Lemma snd : (d P)`2 = (P`1)`2.
Proof. by rewrite /d fdistX2 TripC12.fstA. Qed.

Lemma fstA : (TripA.d (d P))`1 = (TripA.d P)`1.
Proof. by rewrite /fdist_fst !fdistmap_comp. Qed.

Lemma fst_fst : ((d P)`1)`1 = (P`1)`1.
Proof. by rewrite /fdist_fst !fdistmap_comp. Qed.

Lemma sndA : (TripA.d (d P))`2 = fdistX ((TripA.d P)`2).
Proof. by rewrite /fdist_snd /fdistX !fdistmap_comp. Qed.

Lemma imset E F G : [set f x | x in E `* F `* G] = E `* G `* F.
Proof.
apply/setP => -[[a c] b]; apply/imsetP/idP.
- rewrite ex2C; move=> [[[a' b'] c']] /eqP.
  by rewrite /f !inE !xpair_eqE /= => /andP [] /andP [] /eqP -> /eqP -> /eqP -> /andP [] /andP [] -> -> ->.
- by rewrite !inE /= => /andP [] /andP [] aE cG bF; exists ((a, b), c); rewrite // !inE  /= aE cG bF.
Qed.

Lemma Pr E F G : Pr (d P) (E `* G `* F) = Pr P (E `* F `* G).
Proof. by rewrite /d -Pr_fdistX TripA.Pr TripC12.Pr. Qed.
End prop.
End TripAC.
Arguments TripAC.inj_f {A B C}.

Module TripC13.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist C * B * A} := TripC12.d (fdistX (TripA.d P)).
Lemma dE x : d x = P (x.2, x.1.2, x.1.1).
Proof. by rewrite /d TripC12.dE fdistXE TripA.dE. Qed.

Lemma fst : d`1 = fdistX ((TripA.d P)`2).
Proof. by rewrite /d /fdist_fst /fdistX !fdistmap_comp. Qed.

Lemma snd : d`2 = (P`1)`1.
Proof. by rewrite /d TripC12.snd TripA.snd_swap. Qed.

Lemma fst_fst : (d`1)`1 = P`2.
Proof. by rewrite /fdist_fst /fdist_snd !fdistmap_comp. Qed.

Lemma sndA : (TripA.d d)`2 = fdistX (P`1).
Proof. by rewrite /fdist_snd /fdistX !fdistmap_comp. Qed.
End def.
End TripC13.

Module Proj13.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist A * C} := (TripA.d (TripC12.d P))`2.
Lemma dE x : d x = \sum_(b in B) P (x.1, b, x.2).
Proof.
by rewrite /d fdist_sndE; apply eq_bigr => b _; rewrite TripA.dE TripC12.dE.
Qed.

Lemma domin a b c : d (a, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE /= => /psumR_eq0P ->. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (a, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP/domin. Qed.

Lemma snd : d`2 = P`2.
Proof. by rewrite /d TripA.snd_snd TripC12.snd. Qed.

Lemma fst : d`1 = (TripA.d P)`1.
Proof. by rewrite /d TripA.fst_snd TripC12.fst fdistX2 TripA.fst. Qed.

End def.
End Proj13.

Module Proj23.
Section def.
Variables (A B C : finType) (P : {fdist A * B * C}).
Definition d : {fdist B * C} := (TripA.d P)`2.
Lemma dE x : d x = \sum_(a in A) P (a, x.1, x.2).
Proof. by rewrite /d fdist_sndE; apply eq_bigr => a _; rewrite TripA.dE. Qed.

Lemma domin a b c : d (b, c) = 0 -> P (a, b, c) = 0.
Proof. by rewrite dE /= => /psumR_eq0P ->. Qed.

Lemma dominN a b c : P (a, b, c) != 0 -> d (b, c) != 0.
Proof. by apply: contra => /eqP H; apply/eqP; apply: domin. Qed.

Lemma fst : d`1 = (P`1)`2.
Proof. by rewrite /d TripA.fst_snd. Qed.
Lemma snd : d`2 = P`2.
Proof. by rewrite /d TripA.snd_snd. Qed.
End def.
Section prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma Pr_domin E F G :
  Pr (d P) (F `* G) = 0 -> Pr P (E `* F `* G) = 0.
Proof.
move/Pr_set0P => H; apply/Pr_set0P => -[[? ?] ?].
rewrite !inE /= -andbA => /and3P[aE bF cG].
by apply/domin/H; rewrite inE /= bF cG.
Qed.
End prop.
End Proj23.

Section Proj_prop.
Variables (A B C : finType) (P : {fdist A * B * C}).
Lemma Proj13_TripAC : Proj13.d (TripAC.d P) = P`1.
Proof.
rewrite /Proj13.d /fdist_snd /TripA.d /TripC12.d /TripAC.d /fdist_fst.
rewrite !fdistmap_comp /=; congr (fdistmap _ _).
by rewrite boolp.funeqE => -[[]].
Qed.
End Proj_prop.

Section conditional_probability.

Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).

Definition jcPr E F := Pr P (E `* F) / Pr (P`2) F.

Local Notation "\Pr_[ E | F ]" := (jcPr E F).

Lemma jcPrE E F : \Pr_[E | F] = `Pr_P [E `*T | T`* F].
Proof. by rewrite /jcPr -Pr_setTX setTE /cPr EsetT setIX !(setIT,setTI). Qed.

Lemma jcPrET E : \Pr_[E | setT] = Pr (P`1) E.
Proof. by rewrite jcPrE TsetT cPrET -Pr_XsetT EsetT. Qed.

Lemma jcPrE0 E : \Pr_[E | set0] = 0.
Proof. by rewrite jcPrE Tset0 cPrE0. Qed.

Lemma jcPr_ge0 E F : 0 <= \Pr_[E | F].
Proof. by rewrite jcPrE. Qed.

Lemma jcPr_max E F : \Pr_[E | F] <= 1.
Proof. by rewrite jcPrE; apply cPr_max. Qed.

Lemma jcPr_gt0 E F : 0 < \Pr_[E | F] <-> \Pr_[E | F] != 0.
Proof. by rewrite !jcPrE; apply cPr_gt0. Qed.

Lemma Pr_jcPr_gt0 E F : 0 < Pr P (E `* F) <-> 0 < \Pr_[E | F].
Proof.
split.
- rewrite -{1}(setIT E) -{1}(setIT F) (setIC F) -setIX jcPrE.
  by move/Pr_cPr_gt0; rewrite -setTE -EsetT.
- move=> H; rewrite -{1}(setIT E) -{1}(setIT F) (setIC F) -setIX.
  by apply/Pr_cPr_gt0; move: H; rewrite jcPrE -setTE -EsetT.
Qed.

Lemma jcPr_cplt E F : Pr (P`2) F != 0 ->
  \Pr_[ ~: E | F] = 1 - \Pr_[E | F].
Proof.
by move=> PF0; rewrite 2!jcPrE EsetT setCX cPr_cplt ?EsetT // setTE Pr_setTX.
Qed.

Lemma jcPr_diff E1 E2 F : \Pr_[E1 :\: E2 | F] = \Pr_[E1 | F] - \Pr_[E1 :&: E2 | F].
Proof.
rewrite jcPrE DsetT cPr_diff jcPrE; congr (_ - _).
by rewrite 2!EsetT setIX setTI -EsetT jcPrE.
Qed.

Lemma jcPr_union_eq E1 E2 F :
  \Pr_[E1 :|: E2 | F] = \Pr_[E1 | F] + \Pr_[E2 | F] - \Pr_[E1 :&: E2 | F].
Proof. by rewrite jcPrE UsetT cPr_union_eq !jcPrE IsetT. Qed.

Section total_probability.

Variables (I : finType) (E : {set A}) (F : I -> {set B}).
Let P' := fdistX P.
Hypothesis dis : forall i j, i != j -> [disjoint F i & F j].
Hypothesis cov : cover (F @: I) = [set: B].

Lemma jtotal_prob_cond :
  Pr P`1 E = \sum_(i in I) \Pr_[E | F i] * Pr P`2 (F i).
Proof.
rewrite -Pr_XsetT -EsetT.
rewrite (@total_prob_cond _ _ _ _ (fun i => T`* F i)); last 2 first.
  move=> i j ij; rewrite -setI_eq0 !setTE setIX setTI.
  by move: (dis ij); rewrite -setI_eq0 => /eqP ->; rewrite setX0.
  (* TODO: lemma? *)
  apply/setP => -[a b]; rewrite inE /cover.
  apply/bigcupP => /=.
  move: cov; rewrite /cover => /setP /(_ b).
  rewrite !inE => /bigcupP[b'].
  move/imsetP => [i _ ->{b'} bFi].
  exists (T`* F i).
  by apply/imsetP; exists i.
  by rewrite inE.
apply eq_bigr => i _.
rewrite -Pr_setTX -setTE; congr (_ * _).
by rewrite jcPrE.
Qed.

End total_probability.

End conditional_probability.

Notation "\Pr_ P [ E | F ]" := (jcPr P E F) : proba_scope.

(* wip *)
Section jPr_Pr.
Variables (U : finType) (P : fdist U) (A B : finType) (X : {RV P -> A}) (Y : {RV P -> B}).
Variables (E : {set A}) (F : {set B}).

Lemma jPr_Pr : \Pr_(fdistmap [% X, Y] P) [E | F] = `Pr[X \in E |Y \in F].
Proof.
rewrite /jcPr.
rewrite Pr_fdistmap_RV2/=.
rewrite cpr_eq_setE.
rewrite /cPr.
congr (_ / _).
rewrite Pr_fdist_snd.
rewrite setTE.
rewrite Pr_fdistmap_RV2/=.
rewrite (_ : [set x | X x \in [set: A]] = setT); last first.
  by apply/setP => x; rewrite !inE.
by rewrite setTI.
Qed.

End jPr_Pr.
(* /wip *)

Section bayes.
Variables (A B : finType) (PQ : {fdist A * B}).
Let P := PQ`1. Let Q := PQ`2. Let QP := fdistX PQ.
Implicit Types (E : {set A}) (F : {set B}).

Lemma jBayes E F : \Pr_PQ[E | F] = \Pr_QP [F | E] * Pr P E / Pr Q F.
Proof.
rewrite 2!jcPrE Bayes /Rdiv -2!mulRA.
rewrite EsetT Pr_XsetT setTE Pr_setTX /cPr; congr ((_ / _) * (_ / _)).
by rewrite /QP setIX Pr_fdistX -setIX -EsetT -setTE.
by rewrite Pr_fdistX -setTE.
Qed.

Lemma jBayes_extended (I : finType) (E : I -> {set A}) (F : {set B}) :
  (forall i j, i != j -> [disjoint E i & E j]) ->
  cover [set E i | i in I] = [set: A] ->
  forall i,
  \Pr_PQ [E i | F] = (\Pr_QP [F | E i] * Pr P (E i)) /
                     \sum_(j in I) \Pr_ QP [F | E j] * Pr P (E j).
Proof.
move=> dis cov i; rewrite jBayes; congr (_ / _).
move: (@jtotal_prob_cond _ _ QP I F E dis cov).
rewrite {1}/QP fdistX1 => ->.
by apply eq_bigr => j _; rewrite -/QP {2}/QP fdistX2.
Qed.

End bayes.

Section conditional_probability_prop3.
Variables (A B C : finType) (P : {fdist A * B * C}).

Lemma jcPr_TripC12 (E : {set A}) (F : {set B }) (G : {set C}) :
  \Pr_(TripC12.d P)[F `* E | G] = \Pr_P[E `* F | G].
Proof. by rewrite /jcPr TripC12.Pr TripC12.snd. Qed.

Lemma jcPr_TripA_TripAC (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripAC.d P))[E | G `* F] = \Pr_(TripA.d P)[E | F `* G].
Proof.
rewrite /jcPr 2!TripA.Pr TripAC.Pr; congr (_ / _).
by rewrite TripAC.sndA Pr_fdistX fdistXI.
Qed.

Lemma jcPr_TripA_TripC12 (E : {set A}) (F : {set B}) (G : {set C}) :
  \Pr_(TripA.d (TripC12.d P))[F | E `* G] = \Pr_(TripA.d (fdistX (TripA.d P)))[F | G `* E].
Proof.
rewrite /jcPr; congr (_ / _).
by rewrite TripA.Pr TripC12.Pr TripA.Pr [in RHS]Pr_fdistX fdistXI TripA.Pr.
rewrite -/(Proj13.d _) -(fdistXI (Proj13.d P)) Pr_fdistX fdistXI; congr Pr.
(* TODO: lemma? *)
by rewrite /Proj13.d /fdistX /fdist_snd /TripA.d !fdistmap_comp.
Qed.

End conditional_probability_prop3.

Section product_rule.

Section main.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma jproduct_rule_cond E F G :
  \Pr_P [E `* F | G] = \Pr_(TripA.d P) [E | F `* G] * \Pr_(Proj23.d P) [F | G].
Proof.
rewrite /jcPr; rewrite !mulRA; congr (_ * _); last by rewrite Proj23.snd.
rewrite -mulRA -/(Proj23.d _) -TripA.Pr.
case/boolP : (Pr (Proj23.d P) (F `* G) == 0) => H; last by rewrite mulVR ?mulR1.
suff -> : Pr (TripA.d P) (E `* (F `* G)) = 0 by rewrite mul0R.
rewrite TripA.Pr; exact/Proj23.Pr_domin/eqP.
Qed.
End main.

Section variant.
Variables (A B C : finType) (P : {fdist A * B * C}).
Implicit Types (E : {set A}) (F : {set B}) (G : {set C}).
Lemma product_ruleC E F G :
  \Pr_P [ E `* F | G] = \Pr_(TripA.d (TripC12.d P)) [F | E `* G] * \Pr_(Proj13.d P) [E | G].
Proof. by rewrite -jcPr_TripC12 jproduct_rule_cond. Qed.
End variant.

Section prod.
Variables (A B : finType) (P : {fdist A * B}).
Implicit Types (E : {set A}) (F : {set B}).
Lemma jproduct_rule E F : Pr P (E `* F) = \Pr_P[E | F] * Pr (P`2) F.
Proof.
have [/eqP PF0|PF0] := boolP (Pr (P`2) F == 0).
  rewrite jcPrE /cPr -{1}(setIT E) -{1}(setIT F) -setIX.
  rewrite Pr_domin_setI; last by rewrite Pr_fdistX Pr_domin_setX // fdistX1.
  by rewrite setIC Pr_domin_setI ?(div0R,mul0R) // setTE Pr_setTX.
rewrite -{1}(setIT E) -{1}(setIT F) -setIX product_rule.
rewrite -EsetT setTT cPrET Pr_setT mulR1 jcPrE.
rewrite /cPr {1}setTE {1}EsetT.
by rewrite setIX setTI setIT setTE Pr_setTX -mulRA mulVR ?mulR1.
Qed.
End prod.

End product_rule.

Lemma Pr_fdistmap_r (A B B' : finType) (f : B -> B') (d : {fdist A * B}) (E : {set A}) (F : {set B}):
  injective f ->
  \Pr_d [E | F] = \Pr_(fdistmap (fun x => (x.1, f x.2)) d) [E | f @: F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_fdistmap _ _ (fun x => (x.1, f x.2))) /=; last by move=> [? ?] [? ?] /= [-> /injf ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists b'.
  - case=> aE /imsetP[b' b'F] ->{b}; by exists (a, b') => //; rewrite inE /= aE.
by rewrite /fdist_snd fdistmap_comp (@Pr_fdistmap _ _ f) // fdistmap_comp.
Qed.
Arguments Pr_fdistmap_r [A] [B] [B'] [f] [d] [E] [F] _.

Lemma Pr_fdistmap_l (A A' B : finType) (f : A -> A') (d : {fdist A * B}) (E : {set A}) (F : {set B}):
  injective f ->
  \Pr_d [E | F] = \Pr_(fdistmap (fun x => (f x.1, x.2)) d) [f @: E | F].
Proof.
move=> injf; rewrite /jcPr; congr (_ / _).
- rewrite (@Pr_fdistmap _ _ (fun x => (f x.1, x.2))) /=; last by move=> [? ?] [? ?] /= [/injf -> ->].
  congr (Pr _ _); apply/setP => -[a b]; rewrite !inE /=.
  apply/imsetP/andP.
  - case=> -[a' b']; rewrite inE /= => /andP[a'E b'F] [->{a} ->{b}]; split => //.
    apply/imsetP; by exists a'.
  - by case=> /imsetP[a' a'E] ->{a} bF; exists (a', b) => //; rewrite inE /= a'E.
by rewrite /fdist_snd !fdistmap_comp.
Qed.
Arguments Pr_fdistmap_l [A] [A'] [B] [f] [d] [E] [F] _.

(* TODO: move? *)
Lemma Pr_jcPr_unit (A : finType) (E : {set A}) (P : {fdist A}) :
  Pr P E = \Pr_(fdistmap (fun a => (a, tt)) P) [E | setT].
Proof.
rewrite /jcPr (Pr_set1 _ tt).
rewrite (_ : _`2 = fdist1 tt) ?fdist1xx ?divR1; last first.
  rewrite /fdist_snd fdistmap_comp; apply/fdist_ext; case.
  by rewrite fdistmapE fdist1xx (eq_bigl xpredT) // FDist.f1.
rewrite /Pr big_setX /=; apply eq_bigr => a _; rewrite (big_set1 _ tt) /=.
rewrite fdistmapE (big_pred1 a) // => a0; rewrite inE /=.
by apply/eqP/eqP => [[] -> | ->].
Qed.

Section jfdist_cond0.
Variables (A B : finType) (PQ : {fdist A * B}) (a : A).
Hypothesis Ha : PQ`1 a != 0.

Let f := [ffun b => \Pr_(fdistX PQ) [[set b] | [set a]]].

Let f0 b : 0 <= f b. Proof. rewrite ffunE; exact: jcPr_ge0. Qed.

Let f1 : \sum_(b in B) f b = 1.
Proof.
under eq_bigr do rewrite ffunE.
by rewrite /jcPr -big_distrl /= PrX_snd mulRV // Pr_set1 fdistX2.
Qed.

Definition jfdist_cond0 : {fdist B} := locked (FDist.make f0 f1).

Lemma jfdist_cond0E b : jfdist_cond0 b = \Pr_(fdistX PQ) [[set b] | [set a]].
Proof. by rewrite /jfdist_cond0; unlock; rewrite ffunE. Qed.

End jfdist_cond0.
Arguments jfdist_cond0 {A} {B} _ _ _.

Section jfdist_cond.
Variables (A B : finType) (PQ : {fdist A * B}) (a : A).

Let Ha := PQ`1 a != 0.

Let sizeB : #|B| = #|B|.-1.+1.
Proof.
case HB: #|B| => //.
move: (fdist_card_neq0 PQ); by rewrite card_prod HB muln0 ltnn.
Qed.

Definition jfdist_cond :=
  match boolP Ha with
  | AltTrue H => jfdist_cond0 PQ _ H
  | AltFalse _ => fdist_uniform sizeB
  end.

Lemma jfdist_condE (H : Ha) b : jfdist_cond b = \Pr_(fdistX PQ) [[set b] | [set a]].
Proof.
rewrite /jfdist_cond; destruct boolP.
  by rewrite jfdist_cond0E.
by rewrite H in i.
Qed.

Lemma jfdist_cond_dflt (H : ~~ Ha) : jfdist_cond = fdist_uniform sizeB.
Proof.
by rewrite /jfdist_cond; destruct boolP => //; rewrite i in H.
Qed.

End jfdist_cond.

Notation "P `(| a ')'" := (jfdist_cond P a).

Lemma cPr_1 (U : finType) (P : fdist U) (A B : finType)
  (X : {RV P -> A}) (Y : {RV P -> B}) a : `Pr[X = a] != 0 ->
  \sum_(b <- fin_img Y) `Pr[ Y = b | X = a ] = 1.
Proof.
rewrite -pr_eq_set1 pr_inE' Pr_set1 -{1}(fst_RV2 _ Y) => Xa0.
set Q := `d_[% X, Y] `(| a ).
rewrite -(FDist.f1 Q) [in RHS](bigID (mem (fin_img Y))) /=.
rewrite [X in _ = _ + X](eq_bigr (fun=> 0)); last first.
  move=> b bY.
  rewrite /Q jfdist_condE // /jcPr /Pr !(big_setX,big_set1) /= fdistXE fdistX2 fst_RV2.
  rewrite -!pr_eqE' !pr_eqE.
  rewrite /Pr big1 ?div0R // => u.
  rewrite inE => /eqP[Yub ?].
  exfalso.
  move/negP : bY; apply.
  by rewrite mem_undup; apply/mapP; exists u => //; rewrite mem_enum.
rewrite big_const iter_addR mulR0 addR0.
rewrite big_uniq; last by rewrite /fin_img undup_uniq.
apply eq_bigr => b; rewrite mem_undup => /mapP[u _ bWu].
rewrite /Q jfdist_condE // jfdist_RV2.
by rewrite jcPrE -cpr_inE' cpr_eq_set1.
Qed.

Section condjfdist_prop.

Variables (A B : finType) (P : {fdist A * B}).

Lemma jcPr_1 a : P`1 a != 0 ->
  \sum_(b in B) \Pr_(fdistX P)[ [set b] | [set a] ] = 1.
Proof.
move=> Xa0; rewrite -(FDist.f1 (P `(| a ))).
apply eq_bigr => b _.
by rewrite jfdist_condE.
Qed.

End condjfdist_prop.

Section jfdist_prod.
Variables (A B : finType).

Record jfdist_prod_type := mkjfdist_prod_type {
  jfdist_prod_type1 : fdist A ;
  jfdist_prod_type2 :> A -> fdist B }.

Let t := jfdist_prod_type.
Let P := jfdist_prod_type1.
Let W := jfdist_prod_type2.

Definition jfdist_prod (x : t) : {fdist A * B} := fdist_prod (P x) (W x).

Definition make_joint (P : fdist A) (W : A -> fdist B) : {fdist A * B} :=
  jfdist_prod (mkjfdist_prod_type P W).

Lemma jfdist_prod_cond (x : t) : forall a (a0 : (jfdist_prod x)`1 a != 0),
  x a = (jfdist_prod x) `(| a ).
Proof.
move=> a a0; apply/fdist_ext => b.
rewrite jfdist_condE // /jcPr setX1 !Pr_set1 /P fdistXE fdistX2 fdist_prod1.
rewrite fdist_prodE /= /Rdiv mulRAC mulRV ?mul1R //.
by move: a0; rewrite fdist_prod1.
Qed.

Lemma jfdist_prodE (x : t) a b : (P x) a <> 0 ->
  x a b = \Pr_(fdistX (jfdist_prod x))[[set b]|[set a]].
Proof.
move=> Pxa.
rewrite /jcPr setX1 fdistX2 2!Pr_set1 /jfdist_prod fdistXE fdist_prod1.
by rewrite fdist_prodE /= /Rdiv mulRAC mulRV ?mul1R //; exact/eqP.
Qed.

Definition jfdist_split (PQ : {fdist A * B}) :=
  mkjfdist_prod_type (PQ`1) (fun x => PQ `(| x )).

Lemma jfdist_prodK : cancel jfdist_split jfdist_prod.
Proof.
move=> PQ.
rewrite /jfdist_prod /split /=.
apply/fdist_ext => ab.
rewrite fdist_prodE.
case /boolP: (PQ`1 ab.1 == 0) => Ha.
  rewrite (eqP Ha) mul0R.
  symmetry.
  apply (dominatesE (Prod_dominates_Joint PQ)).
  by rewrite fdist_prodE (eqP Ha) mul0R.
rewrite jfdist_condE // -fdistX2 mulRC.
rewrite -(Pr_set1 _ ab.1) -jproduct_rule setX1 Pr_set1 fdistXE.
by destruct ab.
Qed.

End jfdist_prod.

Definition jfdist_prod_coercion (A B : finType) (x : jfdist_prod_type A B) := jfdist_prod_type2 x.
Coercion jfdist_prod_coercion : jfdist_prod_type >-> Funclass.
