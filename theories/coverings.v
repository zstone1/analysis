(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)

From mathcomp Require Import all_ssreflect ssrfun ssrbool ssrnat eqtype choice div.
From mathcomp Require Import seq fintype bigop order ssralg ssrnum finmap matrix.
Require Import boolp reals ereal cardinality.
Require Import classical_sets posnum topology.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def  Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Definition SubspaceDep {X : topologicalType} (A : set X) := {x : X | x \in A} .

Program Definition subspaceDep_pointedType 
    {X : topologicalType} (A : set X) {z} {i : infer (A z)} :=
  (PointedType (SubspaceDep A) z).
Next Obligation.  rewrite in_setE; exact: Infer.  Qed.
Arguments subspaceDep_pointedType {X} (A) {z} {i}.

Definition inclusion
    {X : topologicalType} (A : set X) {z} {i : infer (A z)} (a : subspaceDep_pointedType A) : X :=
  (@proj1_sig X (fun y => y \in A)) a.
Arguments inclusion {X} (A) {z} {i}.

Definition subspaceDep_topologicalType 
    {X : topologicalType} (A : set X) {z} {i : infer (A z)} :=
  @weak_topologicalType  _ X (inclusion A).
Arguments subspaceDep_topologicalType {X} (A) {z} {i}.

Notation "{  'SubspaceDep' A  }" := (@subspaceDep_topologicalType _ A _ _).

Notation "{  'SubspaceDep' A 'over' z  }" := (@subspaceDep_topologicalType _ A z _).

Notation "{  'SubspaceDep' A 'with' Az  }" := (@subspaceDep_topologicalType _ A _ Az).

Section SubspaceDep .
Context  {X : topologicalType} (A : set X) {z} {i : infer (A z)}.
Let j := (@inclusion X A z i) : {SubspaceDep A} -> X.

Lemma inclusion_injective: @injective X {SubspaceDep A} j.
Proof.  move=> [x ?] [y ?] /=; exact: exist_congr. Qed.

Hint Resolve inclusion_injective : core.

Lemma inclusion_continuous: continuous j.
Proof. exact: weak_continuous. Qed.

Lemma inclusion_in ( a : {SubspaceDep A}) : A (j a).
Proof.  by rewrite -in_setE; case: a => ? ? /=. Qed.

Lemma inclusion_preimage ( B : set X): 
  (j @^-1` B) = [set y | B (j y)]. 
Proof. by rewrite eqEsubset; split. Qed.

Lemma inclusion_preimage_image ( B : set X): 
  j @` (j @^-1` B) = A `&` B.
Proof.
rewrite inclusion_preimage eqEsubset; split.
- by move=> p [[p' /= + + <-]]; rewrite in_setE; split.
- by move=> p [Ap Bp]; rewrite -in_setE in Ap; exists (exist _ p Ap).
Qed.

Lemma subspace_open (U : set {SubspaceDep A}):
  open U <-> (exists (V : set X), open V /\ j @` U = A `&` V).
Proof.
split.
- rewrite /open /= /wopen /= => [[ V oV <- ]]; exists V; split => //. 
  exact: inclusion_preimage_image.
- case=> V [] oV UAV; exists V => //; rewrite inclusion_preimage.
  move: UAV; rewrite -inclusion_preimage_image eqEsubset /= => [[L R]].
  rewrite eqEsubset; split => a.
  + by move=> Vja; rewrite -(image_inj (f:=j)) //; apply: R; exists a.
  + by move=> Ua; rewrite -(image_inj (f:=j)) //; apply: L; exists a.
Qed.
  
Lemma subspace_open_nbhs (a : {SubspaceDep A}):
  j @ open_nbhs a `=>` open_nbhs (j a).
Proof. 
  move=> U; rewrite open_nbhsE => [[]] oW nbhsU. 
  split; first (apply: open_comp => // ? ?; exact: inclusion_continuous).
  rewrite inclusion_preimage /=; exact: nbhs_singleton.
Qed.

Lemma subspace_within ( F: set(set({SubspaceDep A}))) (a : {SubspaceDep A}):
  Filter F ->
  F --> a <-> (within A (j @ F)) --> (j a).
Proof. 
move=> FF; split.
- move=> Fa; apply: cvg_trans; first exact: cvg_within. 
  apply: cvg_trans; last exact: inclusion_continuous.
  by apply: cvg_app.
- move=> AjF W /=; rewrite (nbhsE a) => [[U []]]; rewrite open_nbhsE.
  case => /subspace_open [V [] oV jU] nbhsU ; rewrite nbhs_simpl => UW.
  have nbhsV: (nbhs (j a) V). 
    rewrite openE in oV; apply oV.
    apply: ( _ : A `&` V `<=` V); first by move=> ?[].
    by rewrite -jU; exists a => //; exact: nbhs_singleton.
  apply: (filterS UW).
  move: (AjF V nbhsV) => /=; rewrite nbhs_simpl. 
  rewrite /within; near_simpl; apply: filter_app; near=> y.
  move=>/(_ (inclusion_in y)) VY; move: jU.
  rewrite eqEsubset => [[] _ /(_ (j y)) /=].
  case; first (split => //; exact: inclusion_in).
  by move=> ? ? /inclusion_injective <-.
Grab Existential Variables. end_near. Qed.

End SubspaceDep.

Definition Subspace {X : Type} (A : set X) := X.

Section Subspace.
Context {X : topologicalType} (A : set X).

Definition subspace_nbhs (x : Subspace A) : set (set (Subspace A)) :=
  if (x \in A) then within A (nbhs x) else globally [set x].

Lemma subspace_nbhs_filter (x : Subspace A) : ProperFilter (subspace_nbhs x).
Proof.
rewrite /subspace_nbhs; case Ax: (x \in A). 
- by apply: within_nbhs_proper; apply: subset_closure; rewrite -in_setE //=.
- exact: globally_properfilter.
Qed.

Definition subspace_PointedType := PointedType (Subspace A) point. 

Canonical subspace_filteredType := 
  @Filtered.Pack (Subspace A) (Subspace A) (Filtered.Class
    (Pointed.class subspace_PointedType)
    (subspace_nbhs)).

Program Definition subspace_topologicalMixin : Topological.mixin_of (subspace_nbhs)  := 
  @topologyOfFilterMixin (Subspace A) (subspace_nbhs) (subspace_nbhs_filter) _ _.
Next Obligation.
move: H; rewrite /subspace_nbhs; case Ap: (p \in A).
- by move => /nbhs_singleton; apply; rewrite -in_setE.
- by apply.
Qed.
Next Obligation.
move: H; rewrite /subspace_nbhs; case Ap: (p \in A).
- move => /nbhs_interior wA0; apply: (filterS _ wA0) => y A0y. 
  by case Ay: (y \in A) => //=; by rewrite -in_setE Ay.
- by move=> ? x ->; rewrite Ap.
Qed.

Definition subspace_topologicalType {X : topologicalType} (A : set X) :=
  TopologicalType _ (subspace_topologicalMixin).

Lemma subspace_cvg_inP (F : set (set X)) (x : X): 
  Filter F -> A x -> 
  (within A F --> x) <-> (F --> (x : Subspace A)) .
Proof.
move=> FF Ax; split.
- move=> AFx W /=; rewrite /nbhs /=. 
  

Definition homeomorphism {X Y : topologicalType} (A: set X) (B : set Y) f :=
  {in A &, injective f} /\
  f @` A = B /\
  forall (F : set (set X)) x,
    Filter F -> A x ->
    ((within A F --> x) <-> (within B (f@F) --> f x))
.

Lemma fmap_id {X : Type} (F : set (set X)) :
  id@ F = F.
Proof. by rewrite eqEsubset; split => z /=. Qed.


Definition homeomorphism_id {X: topologicalType} (A : set X) :
  homeomorphism A A id.
Proof.
(split; first by move=> ? ?); split.
- rewrite eqEsubset; split => //= ? /=. 
  + by case=> ? ? <-.
  + by move=> ?; eauto. 
- by move=> ? ? ? ?; rewrite fmap_id.
Qed. 

Definition homeomorphic {X Y : topologicalType} (A: set X) (B : set Y) :=
  exists f, homeomorphism A B f.

Definition FiberBundle { X E F : topologicalType} (pi : E -> X) :=
  pi @` setT = setT /\
  forall x, exists (U: set X), open_nbhs x U /\
    exists phi: E -> X * F, 
      homeomorphism (pi@^-1` U) ([set xf | U (fst xf)]) phi /\
      (forall z, fst (phi (z)) = pi z)
      .

Lemma fiber_bundle_global {X F : topologicalType} : 
  @FiberBundle X [topologicalType of (X * F)%type] F (fst).
Proof.
split.
  by rewrite eqEsubset; split => // x _; exists (x,point).
move=> x; exists setT; split; first exact: open_nbhsT.
exists id; split => //=.
exact: homeomorphism_id.
Qed.

Definition covering_space {X E }


  

  

