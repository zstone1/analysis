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
  within A F = [set U | (exists V, F V /\ U `&` A = V `&` A)].
Proof.
move=> FF; rewrite eqEsubset; split.
- move=> U Wu; exists ([set x | A x -> U x]); split => //.
  rewrite eqEsubset; split => t [L R]; split => //; exact: L.
- move=> U [V [FV AU]]; rewrite /within /prop_near1 nbhs_simpl; near=> w => Aw.
  suff : (U `&` A) w by case. 
  rewrite AU; split => //; exact: (near FV).
Grab Existential Variables. end_near. Qed.

Lemma fmap_within_eq {Y : topologicalType} (F: set(set X)) (f g : X -> Y) : 
  Filter F ->
  {in A, f =1 g} -> f @ within A F --> g @ within A F.
Proof.
move=> FF feq U /=; near_simpl; apply: filter_app.
rewrite ?nbhs_simpl; near_simpl; near=> w; rewrite (feq w) // in_setE.
exact: (near (withinT A FF ) w).
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

Lemma subspace_continuous_eq { Y : topologicalType} (f g : (Subspace A) -> Y):
  {in A, f =1 g} -> continuous f -> continuous g.
Proof.
rewrite ?subspace_continuousP=> feq L x Ax.
rewrite -(feq x); last by rewrite in_setE.
by apply: cvg_trans _ (L x Ax); apply: fmap_within_eq=> ? ?; rewrite feq.
Qed.

Lemma subspace_interior (x : X) : A^° x -> nbhs x = (nbhs (x : Subspace A)).
Proof.
move=> Ax; move:(Ax) => /within_interior ->. 
by rewrite {2}/nbhs /= subspace_nbhs_in //; exact: interior_subset.
Qed.

Lemma subspace_nbhsP (U : set X) (x : X) : 
  A x ->
  nbhs (x : Subspace A) (U) <->
  (exists V, nbhs (x : X) (V) /\ U `&` A = V `&` A).
Proof.
by move=> Ax; rewrite {1}/nbhs /= subspace_nbhs_in // withinE /=; split.
Qed.

Definition inclusion ( x : Subspace A) : X := x.

Lemma inclusion_continuous: continuous inclusion.
Proof.
by apply subspace_continuousP => x Ax; apply: cvg_within.
Qed.

Section SubspaceOpen.

Lemma subspace_open_out (x : Subspace A) : 
  ~ A x -> open [set x].
Proof.
move=> Ax; have : nbhs x [set x] by rewrite /nbhs /= subspace_nbhs_out.
rewrite nbhsE => [[U [[]]]] oU Ux Usub; suff : U = [set x] by move=> <-.
by rewrite eqEsubset; split => // t ->.
Qed.

Lemma subspace_open_outU (U : set (Subspace A)): 
  U `<=` ~` A -> open U.
Proof.
move=> Usub; rewrite (_ : U = \bigcup_(i in U) [set i]).
- by apply: open_bigU=> ? ?; apply: subspace_open_out; exact: Usub.
- rewrite eqEsubset; split => x.
  + by move=> Ux; exists x => //.
  + by case=> i ? ->.
Qed.

Lemma subspace_openT : open ( A : set (Subspace A)).
Proof.
  move=> x Ax; rewrite subspace_nbhs_in //; apply withinT, nbhs_filter.
Qed.

Lemma subspace_open_in_A (U : set (Subspace A)) : open U <-> open (U `&` A).
Proof.
split.
- by move=> oU; apply: openI => //; apply: subspace_openT.
- move=> oUA; rewrite (_ : U = (U `&` A) `|` (U `&` ~`A)).
    by apply: openU => //; apply: subspace_open_outU => ? [].
  by rewrite -setIUr setUCr setIT.
Qed.

Lemma subspace_closedT : closed (A : set (Subspace A)).
Proof.
rewrite (_ : A = ~`( ~` (A))); last by rewrite setCK.
by apply: closedC; apply/ subspace_open_in_A; rewrite setICl; exact: open0.
Qed.

Lemma subspace_open ( U : set X) : 
  open (U : set (Subspace A)) <-> 
  exists V, (open (V : set X)) /\ V `&` A = U `&` A.
Proof.
split.
- move=> /subspace_open_in_A oUA.
  have oxF: (forall (x:X), (U `&` A) x -> exists V, (open_nbhs (x : X) V) /\ 
    ((V `&` A) `<=` (U `&` A))). 
  {
    move=> x UAx.
    move: (oUA _ UAx); rewrite subspace_nbhs_in; last by case UAx.
    rewrite withinE /= => [[V [nbhsV UV]]].
    rewrite -setIA setIid in UV.
    exists V^°; split; first rewrite open_nbhsE; first split => //.
    - exact: open_interior.
    - exact: nbhs_interior.
    - by rewrite UV=> t [/interior_subset] ??; split.
  }
  set f := fun x => 
    match (pselect ((U `&` A) x)) with 
    | left e => projT1 (cid (oxF x e))
    | right _ => set0
    end.
  set V := \bigcup_(x in (U `&` A)) (f x); exists V; split.
  + apply: open_bigU => i UAi; rewrite /f.
    case pselect => //= e; case (cid _) =>/= W.
    rewrite open_nbhsE; tauto.
  + rewrite eqEsubset; split.
    * move=> t [[u]] UAu; rewrite /f /=; case pselect => //= ?.
      by case (cid _) => //= W [] _ + ? ?; apply; split.
    * move=> t UAt; split => //; last by case: UAt.
      exists t => //.
    * rewrite /f /=; case pselect => //= ?.
      by case (cid _) => /= W; rewrite /open_nbhs; tauto.
- case=> V [oV UV]; apply/subspace_open_in_A; rewrite -UV.
  move=> x [Vx Ax]; rewrite subspace_nbhs_in //.
  rewrite withinE /=; exists V; split.
  + by move: oV; rewrite openE /interior; apply.
  + by rewrite -setIA setIid.
Qed.

Lemma subspace_open_whole (U : set X) : 
  open ( U : set X)  -> open (U : set (Subspace A)).
Proof.  by move=> oU; apply/subspace_open; exists U; tauto. Qed.

Lemma subspace_hausdorff : 
  hausdorff X -> hausdorff [topologicalType of (Subspace A)].
Proof.
rewrite ?open_hausdorff => + x y xNy => /(_ x y xNy). 
move=> [[P Q]] /= [Px Qx] /= [/subspace_open_whole oP /subspace_open_whole oQ].
by move=> sdjPQ; exists (P,Q).
Qed.

End SubspaceOpen.
End Subspace.

Section SubspaceUniform.
Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.
Context {X : uniformType} (A : set X).

Definition subspace_ent := 
  filter_from (@entourage X)
  (fun E => [set xy | (xy.1 = xy.2) \/ (A xy.1 /\ A xy.2 /\ E xy)]).

Program Definition subspace_uniformMixin :=
  @Uniform.Mixin 
    (Subspace A) 
    (fun x => subspace_nbhs x) 
    (subspace_ent)
    _ _ _ _ _.

Next Obligation.
apply: filter_from_filter; first by (exists setT; exact: filterT).
move=> P Q entP entQ; exists (P `&` Q); first exact: filterI.
move=> [x y] /=; case; first (by move=> ->; split=> /=; left).
by move=> [Ax [Ay [Pxy Qxy]]]; split=> /=; right; tauto.
Qed.

Next Obligation.
by move=> [x y]/= ->; case: H => V entV; apply; left.
Qed.

Next Obligation.
case: H => V entV Vsub; exists (V^-1)%classic; first exact: entourage_inv.
move=> [x y] /= G; apply: Vsub; case G; first by (move=> <-; left).
move=> [? [? Vxy]]; right; repeat split => //.
Qed.

Next Obligation.
case: H => E entE Esub. 
exists  [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ split_ent E xy].
- by exists (split_ent E).
- move=> [x y] [z /= Ez zE] /=; case: Ez; case: zE.
  + by move=> -> ->; apply Esub; left.
  + move=> [ ? []] ? G xy; subst; apply Esub; right; repeat split => //=.
    apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  + move=> -> [ ? []] ? G; apply Esub; right; repeat split => //=.
    apply: entourage_split => //=; first exact: G; exact: entourage_refl.
  + move=> []? []? ?[]?[]??; apply Esub; right; repeat split => //=.
    by apply: subset_split_ent => //; exists z.
Qed.

Next Obligation.
pose  EA := [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2].
have entEA : subspace_ent EA. {
   exists setT; first exact: filterT.
   by move=> [??] /= [ ->|[?] [?]];[left|right].
}
rewrite funeq2E=> x U; case (pselect (A x))=> Ax; rewrite propeqE; split.
- rewrite subspace_nbhs_in // withinE /= .
  case => V nbhsV; move:(nbhsV)=> [/nbhsP [E entE Esub] UV]. 
  exists [set xy | xy.1 = xy.2 \/ A xy.1 /\ A xy.2 /\ E xy]. 
    by exists E => //= [[??]] /= [->| [?[]]//]; exact: entourage_refl.
  move=> y /= [<-|].
  + suff : (U `&` A) x by case.
    by rewrite UV; split => //; apply: (@nbhs_singleton X); tauto.
  + case=> _ [Ay Ey]; suff : (U `&` A) y by case.
    by rewrite UV; split => //; apply: Esub.
- rewrite subspace_nbhs_in // => [[]] W [E eentE subW] subU. 
  near=> w; apply: subU; apply: subW; right; repeat split => //=.
    by exact: (near (withinT A (@nbhs_filter X x) )).
  near: w.
  by apply/nbhsP; exists E => // y /= Ey.  
- rewrite subspace_nbhs_out //= => Ux; exists EA => //.
  by move=> y /= [|[]] //= <-; apply: Ux.
- rewrite subspace_nbhs_out // => [[W [W' entW' subW] subU]] ? ->. 
  by apply: subU; apply: subW; left.
Grab Existential Variables. end_near. Qed.
    
Canonical subspace_uniformType :=
  UniformType (Subspace A) subspace_uniformMixin.
End SubspaceUniform.

