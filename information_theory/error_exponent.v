(* infotheo: information theory and error-correcting codes in Coq               *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later              *)
From mathcomp Require Import all_ssreflect ssralg fingroup finalg matrix.
Require Import Reals Lra.
From mathcomp Require Import Rstruct.
Require Import ssrR Reals_ext Ranalysis_ext logb ln_facts Rbigop fdist entropy.
Require Import channel_code channel divergence conditional_divergence.
Require Import variation_dist pinsker.

(******************************************************************************)
(*                         Error exponent bound                               *)
(*                                                                            *)
(* Lemmas:                                                                    *)
(*   out_entropy_dist_ub == Distance from the output entropy of one channel   *)
(*                          to another                                        *)
(* joint_entropy_dist_ub == Distance from the joint entropy of one channel    *)
(*                          to another                                        *)
(*      mut_info_dist_ub == Distance from the mutual information of one       *)
(*                          channel to another                                *)
(*  error_exponent_bound == intermediate step in the proof of the converse of *)
(*                          the channel coding theorem                        *)
(*                                                                            *)
(* For details, see Reynald Affeldt, Manabu Hagiwara, and Jonas Sénizergues.  *)
(* Formalization of Shannon's theorems. Journal of Automated Reasoning,       *)
(* 53(1):63--103, 2014                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope divergence_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.
Local Open Scope channel_scope.
Local Open Scope reals_ext_scope.
Local Open Scope R_scope.

Section mutinfo_distance_bound.

Variables (A B : finType) (V W : `Ch(A, B)) (P : fdist A).
Hypothesis V_dom_by_W : P |- V << W.
Hypothesis cdiv_ub : D(V || W | P) <= (exp(-2)) ^ 2 * / 2.

Let cdiv_bounds : 0 <= sqrt (2 * D(V || W | P)) <= exp (-2).
Proof.
split; first exact: sqrt_pos.
apply pow2_Rle_inv; [ exact: sqrt_pos | exact/ltRW/exp_pos | ].
rewrite [in X in X <= _]/= mulR1 sqrt_sqrt; last first.
  apply mulR_ge0; [lra | exact: cdiv_ge0].
apply/leRP; rewrite -(leR_pmul2r' (/ 2)); last exact/ltRP/invR_gt0.
rewrite -mulRA mulRCA mulRV ?mulR1; [exact/leRP | exact/eqP/gtR_eqF].
Qed.

Local Open Scope variation_distance_scope.

Lemma out_entropy_dist_ub : `| `H(P `o V) - `H(P `o W) | <=
  / ln 2 * #|B|%:R * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite -addR_opp -mulRN -mulRDr normRM gtR0_norm; last exact/invR_gt0/ln2_gt0.
rewrite -mulRA; apply leR_pmul2l; first exact/invR_gt0/ln2_gt0.
rewrite oppRK big_morph_oppR -big_split /=.
apply: leR_trans; first exact: leR_sumR_Rabs.
rewrite -iter_addR -big_const.
apply leR_sumR => b _; rewrite addRC.
apply Rabs_xlnx => //.
rewrite 2!OutFDist.dE -addR_opp big_morph_oppR -big_split /=.
apply: leR_trans; first exact: leR_sumR_Rabs.
apply (@leR_trans (d(`J(P , V), `J(P , W)))).
- rewrite /var_dist /=.
  apply (@leR_trans (\sum_(a : A) \sum_(b : B) `| (`J(P, V)) (a, b) - (`J(P, W)) (a, b) |)); last first.
    apply Req_le; rewrite pair_bigA /=; apply eq_bigr; by case.
  apply: leR_sumR => a _.
  rewrite (bigD1 b) //= distRC -[X in X <= _]addR0.
  rewrite 2!JointFDistChan.dE /= !(mulRC (P a)) addR_opp.
  by apply/leR_add2l/sumR_ge0 => ? _; exact/normR_ge0.
- rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/joint_dominates.
Qed.

Lemma joint_entropy_dist_ub : `| `H(P , V) - `H(P , W) | <=
  / ln 2 * #|A|%:R * #|B|%:R * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite 2!xlnx_entropy.
rewrite -addR_opp -mulRN -mulRDr normRM gtR0_norm; last exact/invR_gt0/ln2_gt0.
rewrite -2!mulRA; apply leR_pmul2l; first exact/invR_gt0/ln2_gt0.
rewrite oppRK big_morph_oppR -big_split /=.
apply: leR_trans; first exact: leR_sumR_Rabs.
rewrite -2!iter_addR -2!big_const pair_bigA /=.
apply: leR_sumR; case => a b _; rewrite addRC /=.
apply Rabs_xlnx => //.
apply (@leR_trans (d(`J(P , V) , `J(P , W)))).
- rewrite /var_dist /R_dist (bigD1 (a, b)) //= distRC.
  rewrite -[X in X <= _]addR0.
  by apply/leR_add2l/sumR_ge0 => ? _; exact/normR_ge0.
- rewrite cdiv_is_div_joint_dist => //.
  exact/Pinsker_inequality_weak/joint_dominates.
Qed.

Lemma mut_info_dist_ub : `| `I(P, V) - `I(P, W) | <=
  / ln 2 * (#|B|%:R + #|A|%:R * #|B|%:R) * - xlnx (sqrt (2 * D(V || W | P))).
Proof.
rewrite /MutualInfoChan.mut_info.
rewrite (_ : _ - _ = `H(P `o V) - `H(P `o W) + (`H(P, W) - `H(P, V))); last by field.
apply: leR_trans; first exact: Rabs_triang.
rewrite -mulRA mulRDl mulRDr.
apply leR_add.
- by rewrite mulRA; apply out_entropy_dist_ub.
- by rewrite distRC 2!mulRA; apply joint_entropy_dist_ub.
Qed.

End mutinfo_distance_bound.

Section error_exponent_lower_bound.

Variables A B : finType.
Hypothesis Bnot0 : (0 < #|B|)%nat.
Variable W : `Ch(A, B).
Variable minRate : R.
Hypothesis minRate_cap : minRate > capacity W.
Hypothesis set_of_I_has_ubound : classical_sets.has_ubound (fun y => exists P, `I(P, W) = y).

Lemma error_exponent_bound : exists Delta, 0 < Delta /\
  forall P : fdist A, forall V : `Ch(A, B),
    P |- V << W ->
    Delta <= D(V || W | P) +  +| minRate - `I(P, V) |.
Proof.
set gamma := / (#|B|%:R + #|A|%:R * #|B|%:R) * (ln 2 * ((minRate - capacity W) / 2)).
have : min(exp (-2), gamma) > 0.
  apply Rmin_Rgt_r; split; apply Rlt_gt; first exact: exp_pos.
  apply mulR_gt0.
  - apply/invR_gt0/addR_gt0wl; [exact/ltR0n | apply/mulR_ge0; exact/leR0n].
  - apply mulR_gt0 => //; apply mulR_gt0; [by rewrite subR_gt0 | exact: invR_gt0].
move/(continue_xlnx 0) => [] /= mu [mu_gt0 mu_cond].
set x := min(mu / 2, exp (-2)).
have x_gt0 : 0 < x.
  apply Rmin_pos; last exact: exp_pos.
  apply mulR_gt0 => //; exact: invR_gt0.
have /mu_cond : D_x no_cond 0 x /\ R_dist x 0 < mu.
  split.
  - split => //; exact/ltR_eqF.
  - rewrite /R_dist subR0 gtR0_norm // /x.
    apply (@leR_ltR_trans (mu * / 2)); first exact/geR_minl.
    rewrite ltR_pdivr_mulr //; lra.
rewrite /R_dist {2}/xlnx ltRR' subR0 ltR0_norm; last first.
  apply xlnx_neg; split => //; rewrite /x.
  exact: leR_ltR_trans (geR_minr _ _) ltRinve21.
move=> Hx.
set Delta := min((minRate - capacity W) / 2, x ^ 2 / 2).
exists Delta; split.
  apply Rmin_case.
  - apply mulR_gt0; [exact/subR_gt0 | exact/invR_gt0].
  - apply mulR_gt0; [exact: expR_gt0 | exact: invR_gt0].
move=> P V v_dom_by_w.
case/boolP : (Delta <b= D(V || W | P)) => [/leRP| /leRP/ltRNge] Hcase.
  apply (@leR_trans (D(V || W | P))) => //.
  rewrite -{1}(addR0 (D(V || W | P))); exact/leR_add2l/leR_maxl.
suff HminRate : (minRate - capacity W) / 2 <= minRate - (`I(P, V)).
  clear -Hcase v_dom_by_w HminRate.
  apply (@leR_trans +| minRate - `I(P, V) |); last first.
    rewrite -[X in X <= _]add0R; exact/leR_add2r/cdiv_ge0.
  apply: leR_trans; last exact: leR_maxr.
  apply: (leR_trans _ HminRate); exact: geR_minl.
have : `I(P, V) <= capacity W + / ln 2 * (#|B|%:R + #|A|%:R * #|B|%:R) *
                               (- xlnx (sqrt (2 * D(V || W | P)))).
  apply (@leR_trans (`I(P, W) + / ln 2 * (#|B|%:R + #|A|%:R * #|B|%:R) *
                               - xlnx (sqrt (2 * D(V || W | P))))); last first.
    apply/leR_add2r/Rstruct.RleP/Rstruct.real_sup_ub; last by exists P.
    split; first by exists (`I(P, W)), P.
    case: set_of_I_has_ubound => y Hy.
    by exists y => _ [Q _ <-]; apply Hy; exists Q.
  rewrite addRC -leR_subl_addr.
  apply (@leR_trans `| `I(P, V) + - `I(P, W) |); first exact: Rle_abs.
  suff : D(V || W | P) <= exp (-2) ^ 2 * / 2 by apply mut_info_dist_ub.
  clear -Hcase x_gt0.
  apply/ltRW/(ltR_leR_trans Hcase).
  apply (@leR_trans (x ^ 2 * / 2)); first exact: geR_minr.
  apply leR_wpmul2r; first exact/ltRW/invR_gt0.
  apply pow_incr; split; [exact: ltRW | exact: geR_minr].
rewrite -[X in _ <= X]oppRK => /leR_oppr/(@leR_add2l minRate).
move/(leR_trans _); apply.
suff x_gamma : - xlnx (sqrt (2 * (D(V || W | P)))) <= gamma.
  rewrite oppRD addRA addRC -leR_subl_addr.
  rewrite [X in X <= _](_ : _ = - ((minRate + - capacity W) / 2)); last by field.
  rewrite leR_oppr oppRK -mulRA mulRC.
  rewrite leR_pdivr_mulr // mulRC -leR_pdivl_mulr; last first.
    apply addR_gt0wl; first exact/ltR0n.
    rewrite -natRM; exact/leR0n.
  by rewrite [in X in _ <= X]mulRC /Rdiv (mulRC _ (/ (_ + _))).
suff x_D : xlnx x <= xlnx (sqrt (2 * (D(V || W | P)))).
  clear -Hx x_D.
  rewrite leR_oppl; apply (@leR_trans (xlnx x)) => //.
  rewrite leR_oppl; apply/ltRW/(ltR_leR_trans Hx).
  rewrite /gamma; exact: geR_minr.
apply/ltRW/Rgt_lt.
have ? : sqrt (2 * D(V || W | P)) < x.
  apply pow2_Rlt_inv; [exact: sqrt_pos | exact: ltRW | ].
  rewrite [in X in X < _]/= mulR1 sqrt_sqrt; last first.
    apply mulR_ge0; [exact/ltRW | exact/cdiv_ge0].
  rewrite mulRC -ltR_pdivl_mulr //; exact/(ltR_leR_trans Hcase)/geR_minr.
apply xlnx_sdecreasing_0_Rinv_e => //.
- split; first exact/sqrt_pos.
  apply: (@leR_trans x _ _ (ltRW _)) => //.
  rewrite /x; apply (@leR_trans (exp (-2))); first exact: geR_minr.
  apply/ltRW/exp_increasing; lra.
- split; first exact: ltRW.
  apply (@leR_trans (exp (-2))); first exact: geR_minr.
  by apply/ltRW/exp_increasing; lra.
Qed.

End error_exponent_lower_bound.
