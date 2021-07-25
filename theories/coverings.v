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

Section WithinExtras.

Context {X : topologicalType} (A : set X).

Lemma within_interior (x : X) : A^° x -> nbhs x = within A (nbhs x).
Proof.
move=> Aox; rewrite eqEsubset; split.
- move => W nbhsW.
  exact: cvg_within.
- rewrite ?nbhsE => W /= => [[B [+ BsubW ]]].
  rewrite open_nbhsE => [[oB nbhsB]].
  exists (B `&` A^°); split.
  + rewrite open_nbhsE; split.
    * by apply: openI => //; exact: open_interior.
    * apply: filterI => //.
      by move:(open_interior A); rewrite openE; apply.
  + move=> t /= [] /BsubW + /interior_subset; apply.
Qed.

Lemma within_subset (B : set X) F: 
  Filter F -> A `<=` B -> within A F `=>` within B F.
Proof.
  move=> FF AsubB W; rewrite /within; apply: filter_app; rewrite nbhs_simpl.
  by apply: filterE => ? + ?; apply; exact: AsubB.
Qed.

Lemma withinE F: 
  Filter F ->
  within A F = [set U | (exists V, F V /\ A `&` U = A `&` V)].
Proof.
move=> FF; rewrite eqEsubset; split.
- move=> U Wu; exists ([set x | A x -> U x]); split => //.
  rewrite eqEsubset; split => t [L R]; split => //; exact: R.
- move=> U [V [FV AU]]; rewrite /within /prop_near1 nbhs_simpl; near=> w => Aw.
  suff : (A `&` U) w by case. 
  rewrite AU; split => //; exact: (near FV).
Grab Existential Variables. end_near. Qed.

End WithinExtras.

Definition Subspace {X : Type} (A : set X) := X.

Section Subspace.
Context {X : topologicalType} (A : set X).

Definition subspace_nbhs (x : Subspace A) : set (set (Subspace A)) :=
  if (x \in A) then within A (nbhs x) else globally [set x].

Lemma subspace_nbhs_in (x : X) : 
  A x -> subspace_nbhs x = within A (nbhs x).
Proof.
by rewrite -in_setE /subspace_nbhs; case Ax: (x \in A) => //=.
Qed. 

Lemma subspace_nbhs_out (x : X) : 
  ~ A x -> subspace_nbhs x = globally [set x].
Proof.
rewrite /subspace_nbhs; case Ax: (x \in A) => //= Q.
by contradict Q; rewrite -in_setE.
Qed. 

Ltac split_subspace x := 
  case (pselect(A x)) => ?; [rewrite subspace_nbhs_in | rewrite subspace_nbhs_out] => //=.

Lemma subspace_nbhs_filter (x : Subspace A) : ProperFilter (subspace_nbhs x).
Proof.
split_subspace x.
- by apply: within_nbhs_proper; apply: subset_closure.
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
move: H; split_subspace p. 
- by move => /nbhs_singleton; apply.
- by apply.
Qed.
Next Obligation.
move: H; rewrite /subspace_nbhs; case Ap: (p \in A).
- move => /nbhs_interior wA0; apply: (filterS _ wA0) => y A0y. 
  by case Ay: (y \in A) => //=; by rewrite -in_setE Ay.
- by move=> ? x ->; rewrite Ap.
Qed.

Canonical subspace_topologicalType :=
  TopologicalType (Subspace A) (subspace_topologicalMixin).

Lemma subspace_cvgP (F : set (set X)) (x : X): 
  Filter F -> A x -> 
  (F --> (x : Subspace A)) <-> (F --> within A (nbhs x)).
Proof.
move => ??; rewrite /cvg_to/filter_of /= /nbhs /= subspace_nbhs_in //.
Qed.

Lemma subspace_continuousP { Y : topologicalType} (f : X -> Y): 
  continuous (f : Subspace A -> Y) <-> 
  (forall x, A x ->  f @ (within A (nbhs x)) --> f x) .
Proof.
split.
- move=> ctsf x Ax W /=; rewrite nbhs_simpl.
  by rewrite -subspace_nbhs_in //; apply ctsf.
- move=> wA x; case (pselect (A x)) => Ax.
  + apply: cvg_trans; last exact: (wA _ Ax).
    by apply: cvg_app; rewrite subspace_nbhs_in //.
  + rewrite /fmap /= /nbhs /= subspace_nbhs_out //= => P /=.
    by rewrite nbhs_simpl /= => /nbhs_singleton ? ? ->.
Qed.

Lemma subspace_interior (x : X) : A^° x -> nbhs x = (nbhs (x : Subspace A)).
Proof.
move=> Ax; move:(Ax) => /within_interior ->. 
by rewrite {2}/nbhs /= subspace_nbhs_in //; exact: interior_subset.
Qed.

Lemma subspace_nbhsP (U : set X) (x : X) : 
  A x ->
  nbhs (x : Subspace A) (U) <->
  (exists V, nbhs (x : X) (V) /\ A `&` U = A `&` V).
Proof.
by move=> Ax; rewrite {1}/nbhs /= subspace_nbhs_in // withinE /=; split.
Qed.

Lemma subspace_open_out (x : Subspace A) : 
  ~ A x -> open [set x].
Proof.
move=> Ax; have : nbhs x [set x] by rewrite /nbhs /= subspace_nbhs_out.
rewrite nbhsE => [[U [[]]]] oU Ux Usub; suff : U = [set x] by move=> <-.
by rewrite eqEsubset; split => // t ->.
Qed.

Lemma subspace_openT : open ( A : set (Subspace A)).
Proof.
  move=> x Ax; rewrite subspace_nbhs_in //; apply withinT, nbhs_filter.
Qed.

Lemma subspace_closedT : closed ( A : set (Subspace A)).
move=> t cAt; case At: (t \in A); first by rewrite -in_setE. 
contradict cAt; rewrite /closure /=; apply/existsNP.
exists [set t]; rewrite not_implyE; split.
- rewrite /nbhs/= subspace_nbhs_out // => nAt.
  by rewrite -in_setE At in nAt.
- apply/set0P/negP/negPn/eqP; rewrite -subset0 => w [+ tw]; rewrite tw.
  by rewrite -in_setE At.
Qed.

Lemma subspace_hausdorff : 
  hausdorff X -> hausdorff [topologicalType of (Subspace A)].
Proof.
  rewrite open_hausdorff.
  move=> hsdfX.

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


  

  

