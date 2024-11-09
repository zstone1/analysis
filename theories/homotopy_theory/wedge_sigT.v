(* mathcomp analysis (c) 2024 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra finmap generic_quotient.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import cardinality mathcomp_extra fsbigop.
From mathcomp Require Import reals signed topology separation_axioms.
Require Import EqdepFacts.

(**md**************************************************************************)
(* # wedge sum for sigT                                                       *)
(* A foundational construction for homotopy theory. It glues a dependent sum  *)
(* at a single point. It's classicaly used in the proof that every free group *)
(* is a fundamental group of some space. We also will use it as part of our   *)
(* construction of paths and path concatenation.                              *)
(* ```                                                                        *)
(*    wedge_rel p0 x y == x and y are equal, or they are (p0 i) and           *)
(*                        (p0 j) for some i and j                             *)
(*            wedge p0 == the quotient of {i : X i} along `wedge_rel p0`      *)
(*            wedgei i == the lifting of elements of (X i) into the wedge     *)
(*           pwedge p0 == the wedge of ptopologicalTypes at their designated  *)
(*                        point                                               *)
(* ```                                                                        *)
(* The type `wedge p0` is endowed with the structures of:                     *)
(* - topology via `quotient_topology`                                         *)
(* - quotient                                                                 *)
(*                                                                            *)
(* The type `pwedge` is endowed with the structures of:                       *)
(* - topology via `quotient_topology`                                         *)
(* - quotient                                                                 *)
(* - pointed                                                                  *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope quotient_scope.

Section wedge.
Context {I : choiceType} (X : I -> topologicalType) (p0 : forall i, X i).
Implicit Types i : I.

Let wedge_rel' (a b : {i & X i}) :=
  (a == b) || ((projT2 a == p0 _) && (projT2 b == p0 _)).

Local Lemma wedge_rel_refl : reflexive wedge_rel'.
Proof. by move=> ?; rewrite /wedge_rel' eqxx. Qed.

Local Lemma wedge_rel_sym : symmetric wedge_rel'.
Proof.
by move=> a b; apply/is_true_inj/propext; rewrite /wedge_rel'; split;
  rewrite (eq_sym b) andbC.
Qed.

Local Lemma wedge_rel_trans : transitive wedge_rel'.
Proof.
move=> a b c /predU1P[-> //|] + /predU1P[<- //|]; rewrite /wedge_rel'.
by move=> /andP[/eqP -> /eqP <-] /andP[_ /eqP <-]; rewrite !eqxx orbC.
Qed.

Definition wedge_rel := EquivRel _ wedge_rel_refl wedge_rel_sym wedge_rel_trans.
Global Opaque wedge_rel.

Definition wedge := {eq_quot wedge_rel}.
Definition wedgei (i : I) : X i -> wedge := \pi_wedge \o existT X i.

HB.instance Definition _ := Topological.copy wedge (quotient_topology wedge).
HB.instance Definition _ := Quotient.on wedge.
Global Opaque wedge.

Lemma wedgei_continuous i : continuous (@wedgei i).
Proof. by move=> ?; apply: continuous_comp => //; exact: pi_continuous. Qed.

HB.instance Definition _ i :=
  @isContinuous.Build _ _ (@wedgei i) (@wedgei_continuous i).

Lemma wedgei_nbhs i (x : X i) :
  closed [set p0 i] -> x != p0 _ -> (@wedgei i) @ x = nbhs (@wedgei _ x).
Proof.
move=> clx0 xNx0; rewrite eqEsubset; split => U; first last.
  by move=> ?; exact: wedgei_continuous.
rewrite ?nbhsE /= => -[V [oV Vx VU]].
exists (@wedgei i @` (V `&` ~` [set p0 i])); first last.
  by move=> ? /= [l] [Vl lx] <-; exact: VU.
split; last by exists x => //; split => //=; exact/eqP.
rewrite /open /= /quotient_open /wedgei /=.
suff -> : \pi_wedge @^-1` (@wedgei i @` (V `&` ~`[set p0 i])) =
          existT X i @` (V `&` ~` [set p0 i]).
  by apply: existT_open_map; apply: openI => //; exact: closed_openC.
rewrite eqEsubset; split => t /= [l [Vl] lNx0]; last by move=> <-; exists l.
by case/eqmodP/predU1P => [<-|/andP [/eqP]//]; exists l.
Qed.

Lemma wedge_openP (U : set wedge) :
  open U <-> forall i, open (@wedgei i @^-1` U).
Proof.
split=> [oU i|oiU].
  by apply: open_comp => // x _; exact: wedgei_continuous.
have : open (\bigcup_i (@wedgei i @` (@wedgei i @^-1` U))).
  apply/sigT_openP => i; move: (oiU i); congr open.
  rewrite eqEsubset; split => x /=.
    by move=> Ux; exists i => //; exists x.
  case=> j _ /= [] y Uy /eqmodP /predU1P[R|].
    have E : j = i by move: R; exact: eq_sigT_fst.
    rewrite -E in x R *; move: Uy; congr (U (_ _)).
    exact: existT_inj R.
  case/andP => /eqP/= + /eqP ->; move: Uy => /[swap] ->; congr (_ _).
  by apply/eqmodP/orP; right; rewrite !eqxx.
congr open; rewrite eqEsubset; split => /= z.
  by case=> i _ /= [x] Ux <-.
move=> Uz; exists (projT1 (repr z)) => //=.
by exists (projT2 (repr z)); rewrite /wedgei /= -?sigT_eta ?reprK.
Qed.

Lemma wedge_pointE i j : existT _ i (p0 i)  = existT _ j (p0 j) %[mod wedge].
Proof. by apply/eqmodP; apply/orP; right; rewrite ?eqxx. Qed.

Lemma wedge_point_nbhs i0 :
  nbhs (wedgei (p0 i0)) = \bigcap_i (@wedgei i @ p0 i).
Proof.
rewrite eqEsubset; split => //= U /=; rewrite ?nbhs_simpl.
  case=> V [/= oV Vp] VU j _; apply: wedgei_continuous.
  apply: (filterS VU); first exact: (@nbhs_filter wedge).
  apply: open_nbhs_nbhs; split => //; move: Vp; congr (_ _).
  by rewrite /wedgei /=; exact: wedge_pointE.
move=> Uj; have V_ : forall i, {V : set (X i) |
    [/\ open V, V (p0 i) & V `<=` @wedgei i @^-1` U]}.
  move=> j; apply: cid; have /Uj : [set: I] j by [].
  by rewrite nbhsE /= => -[B [? ? ?]]; exists B.
pose W := \bigcup_i (@wedgei i) @` (projT1 (V_ i)).
exists W; split.
- apply/wedge_openP => i; rewrite /W; have [+ Vpj _] := projT2 (V_ i).
  congr(_ _); rewrite eqEsubset; split => z; first by move=> Viz; exists i.
  case => j _ /= [] w /= svw /eqmodP /predU1P[[E]| ].
    by rewrite E in w svw * => R; rewrite -(existT_inj R).
  by case/andP => /eqP /= _ /eqP ->.
- by exists i0 => //=; exists (p0 i0) => //; have [_ + _] := projT2 (V_ i0).
- by move=> ? [j _ [x ? <-]]; have [_ _] := projT2 (V_ j); exact.
Qed.

Variant wedge_nbhs_spec (z : wedge) : wedge -> set_system wedge -> Type :=
  | WedgeIsPoint i0 :
      wedge_nbhs_spec z (wedgei (p0 i0)) (\bigcap_i ((@wedgei i) @ p0 i))
  | WedgeNotPoint (i : I) (x : X i) of (x != p0 i):
      wedge_nbhs_spec z (wedgei x) (@wedgei i @ x).

Lemma wedge_nbhs_specP (z : wedge) : (forall i, closed [set p0 i]) ->
  wedge_nbhs_spec z z (nbhs z).
Proof.
move=> clP; rewrite -[z](@reprK _ wedge); case: (repr z) => i x.
have [->|xpi] := eqVneq x (p0 i).
  by rewrite wedge_point_nbhs => /=; exact: WedgeIsPoint.
by rewrite /= -wedgei_nbhs //; exact: WedgeNotPoint.
Qed.

Lemma wedgeTE : \bigcup_i (@wedgei i) @` setT = [set: wedge].
Proof.
rewrite -subTset => z _; rewrite -[z]reprK; exists (projT1 (repr z)) => //.
by exists (projT2 (repr z)) => //; rewrite reprK /wedgei /= -sigT_eta reprK.
Qed.

Lemma wedge_compact : finite_set [set: I] -> (forall i, compact [set: X i]) ->
  compact [set: wedge].
Proof.
move=> fsetI cptX; rewrite -wedgeTE -fsbig_setU //; apply: big_ind.
- exact: compact0.
- by move=> ? ? ? ?; exact: compactU.
move=> i _; apply: continuous_compact; last exact: cptX.
exact/continuous_subspaceT/wedgei_continuous.
Qed.

Lemma wedge_connected : (forall i, connected [set: X i]) ->
  connected [set: wedge].
Proof.
move=> ctdX; rewrite -wedgeTE.
have [I0|/set0P[i0 Ii0]] := eqVneq [set: I] set0.
  rewrite [X in connected X](_ : _ = set0); first exact: connected0.
  by rewrite I0 bigcup_set0.
apply: bigcup_connected.
  exists (@wedgei i0 (p0 _)) => i Ii; exists (p0 i) => //.
  by apply/eqmodP/orP; right; rewrite !eqxx.
move=> i ? /=; apply: connected_continuous_connected => //.
exact/continuous_subspaceT/wedgei_continuous.
Qed.

End wedge.

Section pwedge.
Context {I : pointedType} (X : I -> ptopologicalType).

Definition pwedge := wedge (fun i => @point (X i)).

Let pwedge_point : pwedge := wedgei _ (@point (X (@point I))).

HB.instance Definition _ := Topological.on pwedge.
HB.instance Definition _ := Quotient.on pwedge.
HB.instance Definition _ := isPointed.Build pwedge pwedge_point.

End pwedge.
