From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import boolp classical_sets functions.
From mathcomp Require Import archimedean.
From mathcomp Require Import cardinality set_interval Rstruct realfun.
From mathcomp Require Import ereal reals signed topology prodnormedzmodule function_spaces.
From mathcomp Require Import normedtype.

Import numFieldTopology.Exports.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Definition I {R : realType} : set R^o := [set` `[(0:R),1]].

HB.mixin Record isReparam (R : realType) (f : R -> R)
    of @SurjFun R R `[0,1] `[0,1] f := {
    param_cts : {within `[0,1], continuous (f : R^o -> R^o)};
    param_homo : {in `[0,1] &, {homo f: x y / (x <= y)}};
}.

#[short(type="reparamType")]
HB.structure Definition Reparam (R : realType) := {
    f of isReparam R f & @SurjFun R R I I f
}.

HB.mixin Record isStrictReparam (R : realType) (f : R -> R)
    of @Reparam R f := {
    param_mono : {in `[0,1] &, {mono f: x y / (x <= y)}};
}.

#[short(type="strictReparamType")]
HB.structure Definition StructReparam (R : realType) := {
    f of isStrictReparam R f & Reparam R f
}.



HB.factory Record ReparamEndpoints (R : realType) (f : R -> R) of 
    isFun R R `[0,1] `[0,1] f := {
        param_cts' : {within `[0,1], continuous (f : R^o -> R^o)};
        param_homo' : {in `[0,1] &, {homo f: x y / (x <= y)}};
        param0 : f 0 = 0;
        param1 : f 1 = 1;
    }.
HB.builders Context (R : realType) (f : R -> R) of ReparamEndpoints R f.

Local Lemma param_surj : set_surj `[0,1] `[0,1] f.
Proof.
have := @segment_continuous_surjective R 0 1 f.
rewrite ?param0 ?param1.
have -> : (@minr R 0 1 = 0) by rewrite /minr ltr01.
have -> : (@maxr R 0 1 = 1) by rewrite /maxr ltr01.
by apply => //; exact: param_cts'.
Qed.

HB.instance Definition _ : OCanV _ _ `[0,1] `[0,1] f := param_surj.
HB.instance Definition _ : isReparam R f := isReparam.Build R f
  param_cts' param_homo'.

HB.end.

HB.factory Record ReparamEndpointsStrict (R : realType) (f : R -> R) of 
    isFun R R `[0,1] `[0,1] f := {
        param_cts'' : {within `[0,1], continuous (f : R^o -> R^o)};
        param_inj : {in `[0, 1] &, injective f};
        param0' : f 0 = 0;
        param1' : f 1 = 1;
    }.

HB.builders Context (R : realType) (f : R -> R) of ReparamEndpointsStrict R f.

  Local Lemma strict_param_mono : {in `[0,1] &, {mono f: x y / (x <= y)}}.
  Proof. 
  move=> /= p q Ip Iq; have -> // := segment_continuous_inj_le _ param_cts''.
  - by rewrite param0' param1'.
  - by move=> i j ? ?; apply: param_inj; rewrite set_itvE; apply/mem_set => //.
  - by move: Ip; rewrite set_itvE => /set_mem /= => //.
  - by move: Iq; rewrite set_itvE => /set_mem /= => //.
  Qed.
  
  Local Lemma strict_param_homo : {in `[0,1] &, {homo f: x y / (x <= y)}}.
  Proof. by move=> p q Ip Iq; rewrite strict_param_mono. Qed.
  
  HB.instance Definition _ : ReparamEndpoints R f := ReparamEndpoints.Build (R : realType) (f : R -> R)
    param_cts'' strict_param_homo param0' param1'.
  
  HB.instance Definition _ : isStrictReparam R f := isStrictReparam.Build (R : realType) (f : R -> R)
      strict_param_mono.
HB.end.
Section reparams.
Context {R : realType}.

Lemma I0 : `[0,1] (0:R).
Proof. by apply/andP;split=> //; rewrite /Order.le /=. Qed.
Hint Resolve I0 : core.

Lemma I0mem : (0:R) \in `[0,1].
Proof. exact/mem_set. Qed.
Hint Resolve I0mem : core.

Lemma I1 : `[0,1] (1:R).
Proof. by apply/andP;split=> //; rewrite /Order.le /=. Qed.
Hint Resolve I1 : core.

Lemma I1mem : (1:R) \in `[0,1].
Proof. exact/mem_set. Qed.
Hint Resolve I1mem : core.

Lemma reparam0 (f : reparamType R) : f 0 = 0. 
Proof.
have /(_ 0) [//|x Ix fx0] := @surj R R _ _ f.
apply/le_anti/andP; split.
  rewrite -[q in _ <= q]fx0; apply/param_homo => //; first exact/mem_set.
  by move: Ix; rewrite set_itvE => /andP [].
by have /andP[]  := @funS R R `[0,1] `[0,1] f 0 I0.
Qed.

Lemma reparam1 (f : reparamType R) : f 1 = 1. 
Proof.
have /(_ 1) [//|x Ix fx1] := @surj R R _ _ f.
apply/le_anti/andP; split.
  by have /andP[]  := @funS R R `[0,1] `[0,1] f 1 I1.
rewrite -[q in q <= _]fx1; apply/param_homo => //; first exact/mem_set.
by move: Ix; rewrite set_itvE => /andP [].
Qed.

Local Lemma reparam_compose (f g: reparamType R) : isReparam R (f \o g).
Proof.
split. 
  move=> x; apply: (@continuous_comp (subspace `[(0:R),1]) (subspace _) _ g f).
    exact/subspaceT_continuous/param_cts.
  exact: param_cts.
(move=> x y xI yI xy; apply: param_homo; last by apply: param_homo);
  by apply/mem_set; apply: funS; apply/set_mem.
Qed.

HB.instance Definition _ f g := reparam_compose f g.

Definition pstop_itv {X : Type} (p : R -> X) (x:R) U := 
  [/\ is_interval U, U `<=` `[0,1], U x & p @` U = [set p x]].
Definition pstop {X : Type} (p : R -> X) (x : R) : set (subspace `[0,1]) := 
  \bigcup_(U in pstop_itv p x) U.

Lemma pstop01 {X : Type} (p : R -> X) x : (pstop p x) `<=` `[0,1].
Proof. by move=> z [? [_ /(_ z)] + _ _] => /[apply]. Qed.

Lemma is_interval_pstop {X : Type} (p : R -> X) x : is_interval (pstop p x).
Proof. 
apply/connected_intervalP; apply bigcup_connected; first by exists x => U [].
by move=> U [/connected_intervalP].
Qed.

Lemma pstop_refl {X : Type} (p : R -> X) x : `[0,1] x -> pstop p x x.
Proof.
move=> x01; (exists `[x,x]; last by rewrite set_itvE); split.
- apply/connected_intervalP; rewrite set_itvE; exact: connected1.
- by rewrite set_itv1 set_itvcc => z ->.
- by rewrite set_itv1. 
- by rewrite set_itv1 image_set1.
Qed.

Lemma pstop_const {X : Type} (p : R -> X) x : `[0,1] x -> p @` (pstop p x) = [set p x].
Proof. 
move=> x01; rewrite eqEsubset; split.
  by move=> ?; case => z + <-; case => r [_ _ ? <-] ?; exists z.
move=> ? ->; exists x => //; exact: pstop_refl.
Qed.

Lemma pstop_closed {X : topologicalType} (p : R -> X) x : 
  {within `[0,1], continuous p} -> closed (pstop p x).
Proof. 
move=> ctsP; rewrite -closed_setIS; last exact: interval_closed.
rewrite setIidl; last exact: pstop01.
rewrite (iffLR (@is_intervalP R (pstop p x)) (is_interval_pstop p x)).
have : p (inf (pstop p x)) = p x.
  Search inf.
apply: interval_closed; rewrite ?asboolT //.
Qed.

Definition stopfree {X : Type} (f : R -> X) := 
   is_subset1 (f @` `[0,1]) \/
   forall (x:R), `[0,1] x -> pstop f x = [set x].
  