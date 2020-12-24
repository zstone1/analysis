(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype choice.
From mathcomp Require Import seq fintype bigop order ssralg ssrint ssrnum finmap.
From mathcomp Require Import matrix interval zmodp.
Require Import boolp ereal reals.
Require Import classical_sets posnum nngnum topology prodnormedzmodule.

(******************************************************************************)
(* This file extends the topological hierarchy with norm-related notions.     *)
(*                                                                            *)
(* ball_ N == balls defined by the norm/absolute value N                      *)
(*                                                                            *)
(* * Normed Topological Abelian groups:                                       *)
(*  pseudoMetricNormedZmodType R  == interface type for a normed topological  *)
(*                                   Abelian group equipped with a norm       *)
(*  PseudoMetricNormedZmodule.Mixin nb == builds the mixin for a normed       *)
(*                                   topological Abelian group from the       *)
(*                                   compatibility between the norm and       *)
(*                                   balls; the carrier type must have a      *)
(*                                   normed Zmodule over a numDomainType.     *)
(*                                                                            *)
(* * Normed modules :                                                         *)
(*                normedModType K == interface type for a normed module       *)
(*                                   structure over the numDomainType K.      *)
(*           NormedModMixin normZ == builds the mixin for a normed module     *)
(*                                   from the property of the linearity of    *)
(*                                   the norm; the carrier type must have a   *)
(*                                   pseudoMetricNormedZmodType structure     *)
(*            NormedModType K T m == packs the mixin m to build a             *)
(*                                   normedModType K; T must have canonical   *)
(*                                   pseudoMetricNormedZmodType K and         *)
(*                                   pseudoMetricType structures.             *)
(*  [normedModType K of T for cT] == T-clone of the normedModType K structure *)
(*                                   cT.                                      *)
(*         [normedModType K of T] == clone of a canonical normedModType K     *)
(*                                   structure on T.                          *)
(*                           `|x| == the norm of x (notation from ssrnum).    *)
(*                      ball_norm == balls defined by the norm.               *)
(*                      nbhs_norm == neighborhoods defined by the norm.       *)
(*                                                                            *)
(* * Domination notations:                                                    *)
(*              dominated_by h k f F == `|f| <= k * `|h|, near F              *)
(*                    bounded_on f F == f is bounded near F                   *)
(*            [bounded f x | x in A] == f is bounded on A, ie F := globally A *)
(*   [locally [bounded f x | x in A] == f is locally bounded on A             *)
(*                       bounded_set == set of bounded sets.                  *)
(*                                   := [set A | [bounded x | x in A]]        *)
(*                       bounded_fun == set of bounded functions.             *)
(*                                   := [set f | [bounded f x | x in setT]]   *)
(*                  lipschitz_on f F == f is lipschitz near F                 *)
(*          [lipschitz f x | x in A] == f is lipschitz on A                   *)
(* [locally [lipschitz f x | x in A] == f is locally lipschitz on A           *)
(*               k.-lipschitz_on f F == f is k.-lipschitz near F              *)
(*                  k.-lipschitz_A f == f is k.-lipschitz on A                *)
(*        [locally k.-lipschitz_A f] == f is locally k.-lipschitz on A        *)
(*                                                                            *)
(*                     is_interval E == the set E is an interval              *)
(*                           Rhull E == the real interval hull of a set       *)
(*                                                                            *)
(* * Complete normed modules :                                                *)
(*        completeNormedModType K == interface type for a complete normed     *)
(*                                   module structure over a realFieldType    *)
(*                                   K.                                       *)
(* [completeNormedModType K of T] == clone of a canonical complete normed     *)
(*                                   module structure over K on T.            *)
(*                                                                            *)
(* * Filters :                                                                *)
(*          at_left x, at_right x == filters on real numbers for predicates   *)
(*                                   s.t. nbhs holds on the left/right of x   *)
(*                                                                            *)
(* --> We used these definitions to prove the intermediate value theorem and  *)
(*     the Heine-Borel theorem, which states that the compact sets of R^n are *)
(*     the closed and bounded sets.                                           *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope ring_scope.

Section add_to_mathcomp.

Lemma ltr_distW (R : realDomainType) (x y e : R) :
  `|x - y| < e -> y - e < x.
Proof. by rewrite ltr_distl => /andP[]. Qed.

Lemma ler_distW (R : realDomainType) (x y e : R):
  `|x - y| <= e -> y - e <= x.
Proof. by rewrite ler_distl => /andP[]. Qed.

End add_to_mathcomp.

Local Open Scope classical_set_scope.

Lemma nbhsN (R : numFieldType) (x : R^o) :
  nbhs (- x) = [set [set - y | y in A] | A in nbhs x].
Proof.
rewrite -!(@filter_from_ballE _ [pseudoMetricType R of R^o]).
rewrite predeqE => A; split=> [[e egt0 oppxe_A]|[B [e egt0 xe_B] <-]];
  last first.
  exists e => // y xe_y; exists (- y); last by rewrite opprK.
  apply/xe_B.
  by rewrite /ball /= opprK -normrN -mulN1r mulrDr !mulN1r.
exists [set - y | y in A]; last first.
  rewrite predeqE => y; split=> [[z [t At <- <-]]|Ay]; first by rewrite opprK.
  by exists (- y); [exists y|rewrite opprK].
exists e => // y xe_y; exists (- y); last by rewrite opprK.
by apply/oppxe_A; rewrite /ball /= distrC opprK addrC.
Qed.

Lemma openN (R : numFieldType) (A : set R^o) :
  open A -> open [set - x | x in A].
Proof.
move=> Aop; rewrite openE => _ [x /Aop x_A <-].
by rewrite /interior nbhsN; exists A.
Qed.

Lemma closedN (R : numFieldType) (A : set R^o) :
  closed A -> closed [set - x | x in A].
Proof.
move=> Acl x clNAx.
suff /Acl : closure A (- x) by exists (- x)=> //; rewrite opprK.
move=> B oppx_B; have : [set - x | x in A] `&` [set - x | x in B] !=set0.
  by apply: clNAx; rewrite -[x]opprK nbhsN; exists B.
move=> [y [[z Az oppzey] [t Bt opptey]]]; exists (- y).
by split; [rewrite -oppzey opprK|rewrite -opptey opprK].
Qed.

Module PseudoMetricNormedZmodule.
Section ClassDef.
Variable R : numDomainType.
Record mixin_of (T : normedZmodType R) (ent : set (set (T * T)))
    (m : PseudoMetric.mixin_of R ent) := Mixin {
  _ : PseudoMetric.ball m = ball_ (fun x => `| x |) }.

Record class_of (T : Type) := Class {
  base : Num.NormedZmodule.class_of R T;
  pointed_mixin : Pointed.point_of T ;
  nbhs_mixin : Filtered.nbhs_of T T ;
  topological_mixin : @Topological.mixin_of T nbhs_mixin ;
  uniform_mixin : @Uniform.mixin_of T nbhs_mixin ;
  pseudoMetric_mixin :
    @PseudoMetric.mixin_of R T (Uniform.entourage uniform_mixin) ;
  mixin : @mixin_of (Num.NormedZmodule.Pack _ base) _ pseudoMetric_mixin
}.
Local Coercion base : class_of >-> Num.NormedZmodule.class_of.
Definition base2 T c := @PseudoMetric.Class _ _
    (@Uniform.Class _
      (@Topological.Class _
        (Filtered.Class
         (Pointed.Class (@base T c) (pointed_mixin c))
         (nbhs_mixin c))
        (topological_mixin c))
      (uniform_mixin c))
    (pseudoMetric_mixin c).
Local Coercion base2 : class_of >-> PseudoMetric.class_of.
(* TODO: base3? *)

Structure type (phR : phant R) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phR : phant R) (T : Type) (cT : type phR).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phR T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).
Definition pack (b0 : Num.NormedZmodule.class_of R T) lm0 um0
  (m0 : @mixin_of (@Num.NormedZmodule.Pack R (Phant R) T b0) lm0 um0) :=
  fun bT (b : Num.NormedZmodule.class_of R T)
      & phant_id (@Num.NormedZmodule.class R (Phant R) bT) b =>
  fun uT (u : PseudoMetric.class_of R T) & phant_id (@PseudoMetric.class R uT) u =>
  fun (m : @mixin_of (Num.NormedZmodule.Pack _ b) _ u) & phant_id m m0 =>
  @Pack phR T (@Class T b u u u u u m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack R phR cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack xT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack R cT xclass.
Definition pointed_zmodType := @GRing.Zmodule.Pack pointedType xclass.
Definition filtered_zmodType := @GRing.Zmodule.Pack filteredType xclass.
Definition topological_zmodType := @GRing.Zmodule.Pack topologicalType xclass.
Definition uniform_zmodType := @GRing.Zmodule.Pack uniformType xclass.
Definition pseudoMetric_zmodType := @GRing.Zmodule.Pack pseudoMetricType xclass.
Definition pointed_normedZmodType := @Num.NormedZmodule.Pack R phR pointedType xclass.
Definition filtered_normedZmodType := @Num.NormedZmodule.Pack R phR filteredType xclass.
Definition topological_normedZmodType := @Num.NormedZmodule.Pack R phR topologicalType xclass.
Definition uniform_normedZmodType := @Num.NormedZmodule.Pack R phR uniformType xclass.
Definition pseudoMetric_normedZmodType := @Num.NormedZmodule.Pack R phR pseudoMetricType xclass.

End ClassDef.

(*Definition numDomain_normedDomainType (R : numDomainType) : type (Phant R) :=
  Pack (Phant R) (@Class R _ _ (NumDomain.normed_mixin (NumDomain.class R))).*)

Module Exports.
Coercion base : class_of >-> Num.NormedZmodule.class_of.
Coercion base2 : class_of >-> PseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Canonical pointed_zmodType.
Canonical filtered_zmodType.
Canonical topological_zmodType.
Canonical uniform_zmodType.
Canonical pseudoMetric_zmodType.
Canonical pointed_normedZmodType.
Canonical filtered_normedZmodType.
Canonical topological_normedZmodType.
Canonical uniform_normedZmodType.
Canonical pseudoMetric_normedZmodType.
Notation pseudoMetricNormedZmodType R := (type (Phant R)).
Notation PseudoMetricNormedZmodType R T m :=
  (@pack _ (Phant R) T _ _ _ m _ _ idfun _ _ idfun _ idfun).
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T 'for' cT ]" :=
  (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T  'for'  cT ]") :
  form_scope.
Notation "[ 'pseudoMetricNormedZmodType' R 'of' T ]" :=
  (@clone _ (Phant R) T _ _ idfun)
  (at level 0, format "[ 'pseudoMetricNormedZmodType'  R  'of'  T ]") : form_scope.
End Exports.

End PseudoMetricNormedZmodule.
Export PseudoMetricNormedZmodule.Exports.

Section pseudoMetricnormedzmodule_lemmas.
Context {K : numDomainType} {V : pseudoMetricNormedZmodType K}.

Local Notation ball_norm := (ball_ (@normr K V)).

Lemma ball_normE : ball_norm = ball.
Proof. by case: V => ? [? ? ? ? ? ? []]. Qed.

End pseudoMetricnormedzmodule_lemmas.

Section numFieldType_canonical_contd.
Variable R : numFieldType.
Lemma R_ball : @ball _ [pseudoMetricType R of R^o] = ball_ (fun x => `| x |).
Proof. by []. Qed.
Definition numFieldType_pseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin R_ball.
Canonical numFieldType_pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodType R R^o numFieldType_pseudoMetricNormedZmodMixin.
End numFieldType_canonical_contd.

(** locally *)

Section Nbhs'.
Context {R : numDomainType} {T : pseudoMetricType R}.

Lemma ex_ball_sig (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
    {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
rewrite forallNE notK => exNP.
pose D := [set d : R | d > 0 /\ ball x d `<=` ~` P].
have [|d_gt0] := @getPex _ D; last by exists (PosNum d_gt0).
by move: exNP => [e eP]; exists e%:num.
Qed.

Lemma nbhsC (x : T) (P : set T) :
  ~ (forall eps : {posnum R}, ~ (ball x eps%:num `<=` ~` P)) ->
  nbhs x (~` P).
Proof. by move=> /ex_ball_sig [e] ?; apply/nbhs_ballP; exists e%:num. Qed.

Lemma nbhsC_ball (x : T) (P : set T) :
  nbhs x (~` P) -> {d : {posnum R} | ball x d%:num `<=` ~` P}.
Proof.
move=> /nbhs_ballP xNP; apply: ex_ball_sig.
by have [_ /posnumP[e] eP /(_ _ eP)] := xNP.
Qed.

Lemma nbhs_ex (x : T) (P : T -> Prop) : nbhs x P ->
  {d : {posnum R} | forall y, ball x d%:num y -> P y}.
Proof.
move=> /nbhs_ballP xP.
pose D := [set d : R | d > 0 /\ forall y, ball x d y -> P y].
have [|d_gt0 dP] := @getPex _ D; last by exists (PosNum d_gt0).
by move: xP => [e bP]; exists (e : R).
Qed.

End Nbhs'.

Lemma ler_addgt0Pr (R : numFieldType) (x y : R) :
   reflect (forall e, e > 0 -> x <= y + e) (x <= y).
Proof.
apply/(iffP idP)=> [lexy _/posnumP[e] | lexye]; first by rewrite ler_paddr.
have [||ltyx]// := comparable_leP.
  rewrite (@comparabler_trans _ (y + 1))// /Order.comparable ?lexye//.
  by rewrite ler_addl ler01 orbT.
have /midf_lt [_] := ltyx; rewrite le_gtF//.
by rewrite -(@addrK _ y y) addrAC -addrA 2!mulrDl -splitr lexye// divr_gt0//
  subr_gt0.
Qed.

Lemma ler_addgt0Pl (R : numFieldType) (x y : R) :
  reflect (forall e, e > 0 -> x <= e + y) (x <= y).
Proof.
by apply/(equivP (ler_addgt0Pr x y)); split=> lexy e /lexy; rewrite addrC.
Qed.

Lemma in_segment_addgt0Pr (R : numFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(x - e), (z + e)]) (y \in `[x, z]).
Proof.
apply/(iffP idP)=> [xyz _/posnumP[e] | xyz_e].
  rewrite inE/=; apply/andP; split; last by rewrite ler_paddr // (itvP xyz).
  by rewrite ler_subl_addr ler_paddr // (itvP xyz).
rewrite inE/=; apply/andP.
by split; apply/ler_addgt0Pr => ? /xyz_e /andP /= []; rewrite ler_subl_addr.
Qed.

Lemma in_segment_addgt0Pl (R : numFieldType) (x y z : R) :
  reflect (forall e, e > 0 -> y \in `[(- e + x), (e + z)]) (y \in `[x, z]).
Proof.
apply/(equivP (in_segment_addgt0Pr x y z)).
by split=> zxy e /zxy; rewrite [z + _]addrC [_ + x]addrC.
Qed.

Lemma coord_continuous {K : numFieldType} m n i j :
  continuous (fun M : 'M[K^o]_(m.+1, n.+1) => M i j).
Proof.
move=> /= M s /= /(nbhs_ballP (M i j)) [e e0 es].
apply/nbhs_ballP; exists e => //= N MN; exact/es/MN.
Qed.

Global Instance Proper_nbhs'_realType (R : realType) (x : R^o) :
  ProperFilter (nbhs' x).
Proof. exact: Proper_nbhs'_numFieldType. Qed.

(** * Some Topology on [Rbar] *)

Definition pinfty_nbhs (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, M < x -> P x.
Arguments pinfty_nbhs R : clear implicits.
Definition ninfty_nbhs (R : numFieldType) : set (set R) :=
  fun P => exists M, M \is Num.real /\ forall x, x < M -> P x.
Arguments ninfty_nbhs R : clear implicits.

Notation "+oo" := (pinfty_nbhs _) : ring_scope.
Notation "-oo" := (ninfty_nbhs _) : ring_scope.

Section infty_nbhs_instances.
Context {R : numFieldType}.
Let R_topologicalType := [topologicalType of R^o].

Global Instance proper_pinfty_nbhs : ProperFilter (pinfty_nbhs R).
Proof.
apply Build_ProperFilter.
  by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
- by exists 0; rewrite real0.
- have [/eqP MP0|MP0] := boolP (MP == 0).
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      by exists 0; rewrite real0; split => // x x0; split;
      [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
    exists `|MQ|; rewrite realE normr_ge0; split => // x Hx; split.
      by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0.
    by apply gtMQ; rewrite (le_lt_trans _ Hx) // real_ler_normr // lexx.
  have [/eqP MQ0|MQ0] := boolP (MQ == 0).
    exists `|MP|; rewrite realE normr_ge0; split => // x MPx; split.
    by apply gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
    by apply gtMQ; rewrite (le_lt_trans _ MPx) // MQ0.
  have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
  have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
  exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
  rewrite realE /= posnum_ge0 /=; split => // x.
  rewrite posnum_max pos_lt_maxl /= => /andP[MPx MQx]; split.
  by apply/gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
  by apply/gtMQ; rewrite (le_lt_trans _ MQx) // real_ler_normr // lexx.
- by exists M; split => // ? /gtM /sPQ.
Defined.
Typeclasses Opaque proper_pinfty_nbhs.

Global Instance proper_ninfty_nbhs : ProperFilter (ninfty_nbhs R).
Proof.
apply Build_ProperFilter.
- move=> P [M [Mr ltMP]]; exists (M - 1).
  by apply: ltMP; rewrite gtr_addl oppr_lt0.
- split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
      exists (- `|MQ|); rewrite realN realE normr_ge0; split => // x xMQ; split.
        by apply ltMP; rewrite (lt_le_trans xMQ) // MP0 ler_oppl oppr0.
      apply ltMQ; rewrite (lt_le_trans xMQ) // ler_oppl -normrN.
     by rewrite real_ler_normr ?realN // lexx.
  + have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists (- `|MP|); rewrite realN realE normr_ge0; split => // x MPx; split.
        apply ltMP; rewrite (lt_le_trans MPx) // ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      by apply ltMQ; rewrite (lt_le_trans MPx) // MQ0 ler_oppl oppr0.
    have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
    have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
    exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num).
    rewrite realN realE /= posnum_ge0 /=; split => // x.
    rewrite ltr_oppr posnum_max pos_lt_maxl => /andP[].
    rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
      apply/ltMP; rewrite (lt_le_trans MPx) //= ler_oppl -normrN.
      by rewrite real_ler_normr ?realN // lexx.
    apply/ltMQ; rewrite (lt_le_trans MQx) //= ler_oppl -normrN.
    by rewrite real_ler_normr ?realN // lexx.
  + by exists M; split => // x /ltM /sPQ.
Defined.
Typeclasses Opaque proper_ninfty_nbhs.

(*Global Instance ereal_locally'_filter :
  forall x : {ereal R}, ProperFilter (ereal_locally' x).
Proof.
case=> [x||]; first exact: Proper_locally'_numFieldType.
- apply Build_ProperFilter.
    by move=> P [M [Mreal MP]]; exists (M + 1); apply MP; rewrite ltr_addl.
  split=> /= [|P Q [MP [MPr gtMP]] [MQ [MQr gtMQ]] |P Q sPQ [M [Mr gtM]]].
  + by exists 0; rewrite real0.
  + have [/eqP MP0|MP0] := boolP (MP == 0).
      have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        by exists 0; rewrite real0; split => // x x0; split;
        [apply/gtMP; rewrite MP0 | apply/gtMQ; rewrite MQ0].
      exists `|MQ|; rewrite realE normr_ge0; split => // x Hx; split.
        by apply gtMP; rewrite (le_lt_trans _ Hx) // MP0.
      by apply gtMQ; rewrite (le_lt_trans _ Hx) // real_ler_normr // lexx.
    have [/eqP MQ0|MQ0] := boolP (MQ == 0).
      exists `|MP|; rewrite realE normr_ge0; split => // x MPx; split.
      by apply gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
      by apply gtMQ; rewrite (le_lt_trans _ MPx) // MQ0.
    have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
    have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
    exists (Num.max (PosNum MP0) (PosNum MQ0))%:num.
    rewrite realE /= posnum_ge0 /=; split => // x.
    rewrite pos_lt_maxl /= => /andP[MPx MQx]; split.
    by apply/gtMP; rewrite (le_lt_trans _ MPx) // real_ler_normr // lexx.
    by apply/gtMQ; rewrite (le_lt_trans _ MQx) // real_ler_normr // lexx.
  + by exists M; split => // ? /gtM /sPQ.
- apply Build_ProperFilter.
  + move=> P [M [Mr ltMP]]; exists (M - 1).
    by apply: ltMP; rewrite gtr_addl oppr_lt0.
  + split=> /= [|P Q [MP [MPr ltMP]] [MQ [MQr ltMQ]] |P Q sPQ [M [Mr ltM]]].
    * by exists 0; rewrite real0.
    * have [/eqP MP0|MP0] := boolP (MP == 0).
        have [/eqP MQ0|MQ0] := boolP (MQ == 0).
          by exists 0; rewrite real0; split => // x x0; split;
          [apply/ltMP; rewrite MP0 | apply/ltMQ; rewrite MQ0].
        exists (- `|MQ|); rewrite realN realE normr_ge0; split => // x xMQ; split.
          by apply ltMP; rewrite (lt_le_trans xMQ) // MP0 ler_oppl oppr0.
        apply ltMQ; rewrite (lt_le_trans xMQ) // ler_oppl -normrN.
       by rewrite real_ler_normr ?realN // lexx.
    * have [/eqP MQ0|MQ0] := boolP (MQ == 0).
        exists (- `|MP|); rewrite realN realE normr_ge0; split => // x MPx; split.
          apply ltMP; rewrite (lt_le_trans MPx) // ler_oppl -normrN.
          by rewrite real_ler_normr ?realN // lexx.
        by apply ltMQ; rewrite (lt_le_trans MPx) // MQ0 ler_oppl oppr0.
      have {}MP0 : 0 < `|MP| by rewrite normr_gt0.
      have {}MQ0 : 0 < `|MQ| by rewrite normr_gt0.
      exists (- (Num.max (PosNum MP0) (PosNum MQ0))%:num).
      rewrite realN realE /= posnum_ge0 /=; split => // x.
      rewrite ltr_oppr pos_lt_maxl => /andP[].
      rewrite ltr_oppr => MPx; rewrite ltr_oppr => MQx; split.
        apply/ltMP; rewrite (lt_le_trans MPx) //= ler_oppl -normrN.
        by rewrite real_ler_normr ?realN // lexx.
      apply/ltMQ; rewrite (lt_le_trans MQx) //= ler_oppl -normrN.
      by rewrite real_ler_normr ?realN // lexx.
    * by exists M; split => // x /ltM /sPQ.
Qed.
Typeclasses Opaque ereal_locally'.*)

(*Global Instance ereal_locally_filter :
  forall x, ProperFilter (@ereal_locally R x).
Proof.
case=> [x||].
exact: ereal_locally_filter.
exact: (ereal_locally'_filter +oo).
exact: (ereal_locally'_filter -oo).
Qed.
Typeclasses Opaque ereal_locally.*)

Lemma near_pinfty_div2 (A : set R) :
  (\forall k \near +oo, A k) -> (\forall k \near +oo, A (k / 2)).
Proof.
move=> [M [Mreal AM]]; exists (M * 2); split.
  by rewrite realM // realE; apply/orP; left.
by move=> x; rewrite -ltr_pdivl_mulr //; apply: AM.
Qed.

Lemma nbhs_pinfty_gt (c : {posnum R}) : \forall x \near +oo, c%:num < x.
Proof. by exists c%:num; split => // ; rewrite realE posnum_ge0. Qed.

Lemma nbhs_pinfty_ge (c : {posnum R}) : \forall x \near +oo, c%:num <= x.
Proof. by exists c%:num; rewrite realE posnum_ge0; split => //; apply: ltW. Qed.

Lemma nbhs_pinfty_gt_real (c : R) : c \is Num.real ->
  \forall x \near +oo, c < x.
Proof. by exists c. Qed.

Lemma nbhs_pinfty_ge_real (c : R) : c \is Num.real ->
  \forall x \near +oo, c <= x.
Proof. by exists c; split => //; apply: ltW. Qed.

Lemma nbhs_minfty_lt (c : {posnum R}) : \forall x \near -oo, c%:num > x.
Proof. by exists c%:num; split => // ; rewrite realE posnum_ge0. Qed.

Lemma nbhs_minfty_le (c : {posnum R}) : \forall x \near -oo, c%:num >= x.
Proof.
by exists c%:num; rewrite realE posnum_ge0 /=; split => // x; apply: ltW.
Qed.

Lemma nbhs_minfty_lt_real (c : R) : c \is Num.real ->
  \forall x \near -oo, c > x.
Proof. by exists c. Qed.

Lemma nbhs_minfty_le_real (c : R) : c \is Num.real ->
  \forall x \near -oo, c >= x.
Proof. by exists c; split => // ?; apply: ltW. Qed.

End infty_nbhs_instances.

Hint Extern 0 (is_true (0 < _)) => match goal with
  H : ?x \is_near (nbhs +oo) |- _ =>
    solve[near: x; exists 0 => _/posnumP[x] //] end : core.

(** ** Modules with a norm *)

Module NormedModule.

Record mixin_of (K : numDomainType)
  (V : pseudoMetricNormedZmodType K) (scale : K -> V -> V) := Mixin {
  _ : forall (l : K) (x : V), `| scale l x | = `| l | * `| x |;
}.

Section ClassDef.

Variable K : numDomainType.

Record class_of (T : Type) := Class {
  base : PseudoMetricNormedZmodule.class_of K T ;
  lmodmixin : GRing.Lmodule.mixin_of K (GRing.Zmodule.Pack base) ;
  mixin : @mixin_of K (PseudoMetricNormedZmodule.Pack (Phant K) base)
                      (GRing.Lmodule.scale lmodmixin)
}.
Local Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.
Local Coercion base2 T (c : class_of T) : GRing.Lmodule.class_of K T :=
  @GRing.Lmodule.Class K T (base c) (lmodmixin c).
Local Coercion mixin : class_of >-> mixin_of.

Structure type (phK : phant K) :=
  Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (T : Type) (cT : type phK).

Definition class := let: Pack _ c := cT return class_of cT in c.
Definition clone c of phant_id class c := @Pack phK T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 l0
                (m0 : @mixin_of K (@PseudoMetricNormedZmodule.Pack K (Phant K) T b0)
                                (GRing.Lmodule.scale l0)) :=
  fun bT b & phant_id (@PseudoMetricNormedZmodule.class K (Phant K) bT) b =>
  fun l & phant_id l0 l =>
  fun m & phant_id m0 m => Pack phK (@Class T b l m).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType := @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition pointed_lmodType := @GRing.Lmodule.Pack K phK pointedType xclass.
Definition filtered_lmodType := @GRing.Lmodule.Pack K phK filteredType xclass.
Definition topological_lmodType := @GRing.Lmodule.Pack K phK topologicalType xclass.
Definition uniform_lmodType := @GRing.Lmodule.Pack K phK uniformType xclass.
Definition pseudoMetric_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricType xclass.
Definition normedZmod_lmodType := @GRing.Lmodule.Pack K phK normedZmodType xclass.
Definition pseudoMetricNormedZmod_lmodType := @GRing.Lmodule.Pack K phK pseudoMetricNormedZmodType xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> PseudoMetricNormedZmodule.class_of.
Coercion base2 : class_of >-> GRing.Lmodule.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Canonical pointed_lmodType.
Canonical filtered_lmodType.
Canonical topological_lmodType.
Canonical uniform_lmodType.
Canonical pseudoMetric_lmodType.
Canonical normedZmod_lmodType.
Canonical pseudoMetricNormedZmod_lmodType.
Notation normedModType K := (type (Phant K)).
Notation NormedModType K T m := (@pack _ (Phant K) T _ _ m _ _ idfun _ idfun _ idfun).
Notation NormedModMixin := Mixin.
Notation "[ 'normedModType' K 'of' T 'for' cT ]" := (@clone _ (Phant K) T cT _ idfun)
  (at level 0, format "[ 'normedModType'  K  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'normedModType' K 'of' T ]" := (@clone _ (Phant K) T _ _ id)
  (at level 0, format "[ 'normedModType'  K  'of'  T ]") : form_scope.
End Exports.

End NormedModule.

Export NormedModule.Exports.

Lemma R_normZ (R : numDomainType) (l : R) (x : R^o) :
  `| l *: x | = `| l | * `| x |.
Proof. by rewrite normrM. Qed.

Definition numFieldType_NormedModMixin (R : numFieldType) :=
  NormedModMixin (@R_normZ R).
Canonical numFieldType_normedModType (R : numFieldType) :=
  NormedModType R R^o (numFieldType_NormedModMixin R).

Section NormedModule_numDomainType.
Variables (R : numDomainType) (V : normedModType R).

Lemma normmZ l (x : V) : `| l *: x | = `| l | * `| x |.
Proof. by case: V x => V0 [a b [c]] //= v; rewrite c. Qed.

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma nbhs_le_nbhs_norm (x : V) : nbhs x `=>` nbhs_norm x.
Proof.
move=> P [_ /posnumP[e] subP]; apply/nbhs_ballP.
by eexists; last (move=> y Py; apply/subP; apply/Py).
Qed.

Lemma nbhs_norm_le_nbhs x : nbhs_norm x `=>` nbhs x.
Proof.
move=> P /nbhs_ballP [_ /posnumP[e] Pxe].
by exists e%:num => // y; apply/Pxe.
Qed.

Lemma nbhs_nbhs_norm : nbhs_norm = nbhs.
Proof. by rewrite funeqE => x; rewrite -filter_from_ballE. Qed.

Lemma nbhs_normP x P : nbhs x P <-> nbhs_norm x P.
Proof. by rewrite nbhs_nbhs_norm. Qed.

Lemma filter_from_norm_nbhs x :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) = nbhs x.
Proof. by rewrite -nbhs_nbhs_norm ball_normE. Qed.

Lemma nbhs_normE (x : V) (P : set V) :
  nbhs_norm x P = \near x, P x.
Proof. by rewrite nbhs_nbhs_norm near_simpl. Qed.

Lemma filter_from_normE (x : V) (P : set V) :
  @filter_from R _ [set x : R | 0 < x] (ball_norm x) P = \near x, P x.
Proof. by rewrite filter_from_norm_nbhs. Qed.

Lemma near_nbhs_norm (x : V) (P : set V) :
  (\forall x \near nbhs_norm x, P x) = \near x, P x.
Proof. exact: nbhs_normE. Qed.

Lemma nbhs_norm_ball_norm x (e : {posnum R}) :
  nbhs_norm x (ball_norm x e%:num).
Proof. by rewrite ball_normE; exists e%:num. Qed.

Lemma nbhs_ball_norm (x : V) (eps : {posnum R}) : nbhs x (ball_norm x eps%:num).
Proof. rewrite -nbhs_nbhs_norm; apply: nbhs_norm_ball_norm. Qed.

Lemma ball_norm_dec x y (e : R) : {ball_norm x e y} + {~ ball_norm x e y}.
Proof. exact: pselect. Qed.

Lemma ball_norm_sym x y (e : R) : ball_norm x e y -> ball_norm y e x.
Proof. by rewrite /ball_norm/= -opprB normrN. Qed.

Lemma ball_norm_le x (e1 e2 : R) :
  e1 <= e2 -> ball_norm x e1 `<=` ball_norm x e2.
Proof. by move=> e1e2 y /lt_le_trans; apply. Qed.

Let nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).

Lemma cvg_distP {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y <-> forall eps, 0 < eps -> \forall y' \near F, `|y - y'| < eps.
Proof. by rewrite -filter_fromP /= !nbhs_simpl. Qed.

Lemma cvg_dist {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> forall eps, eps > 0 -> \forall y' \near F, `|y - y'| < eps.
Proof. by move=> /cvg_distP. Qed.

Lemma nbhs_norm_ball x (eps : {posnum R}) : nbhs_norm x (ball x eps%:num).
Proof. rewrite nbhs_nbhs_norm; by apply: nbhsx_ballx. Qed.

End NormedModule_numDomainType.
Hint Resolve normr_ge0 : core.
Arguments cvg_dist {_ _ F FF}.

Lemma pinfty_ex_gt {R : numFieldType} (m : R) (A : set R) : m \is Num.real ->
  (\forall k \near +oo, A k) -> exists2 M, m < M & A M.
Proof.
by move=> m_real Agt; near (pinfty_nbhs R) => M;
   exists M; near: M => //; exists m.
Grab Existential Variables. all: end_near. Qed.

Lemma pinfty_ex_gt0 {R : numFieldType} (A : set R) :
  (\forall k \near +oo, A k) -> exists2 M, M > 0 & A M.
Proof. by apply: pinfty_ex_gt; rewrite real0. Qed.

Definition self_sub (K : numDomainType) (V W : normedModType K)
  (f : V -> W) (x : V * V) : W := f x.1 - f x.2.
Arguments self_sub {K V W} f x /.

Definition fun1 {T : Type} {K : numFieldType} :
  T -> [normedModType K of K^o] := fun=> 1.
Arguments fun1 {T K} x /.

Definition dominated_by {T : Type} {K : numDomainType} {V W : normedModType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| <= k * `|h x|].

Definition strictly_dominated_by {T : Type} {K : numDomainType} {V W : normedModType K}
  (h : T -> V) (k : K) (f : T -> W) (F : set (set T)) :=
  F [set x | `|f x| < k * `|h x|].

Lemma sub_dominatedl (T : Type) (K : numFieldType) (V W : normedModType K)
   (h : T -> V) (k : K) (F G : set (set T)) : F `=>` G ->
  (@dominated_by T K V W h k)^~ G `<=` (dominated_by h k)^~ F.
Proof. by move=> FG f; exact: FG. Qed.

Lemma sub_dominatedr (T : Type) (K : numFieldType) (V : normedModType K)
    (h : T -> V) (k : K) (f g : T -> V) (F : set (set T)) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->
   dominated_by h k g F -> dominated_by h k f F.
Proof. by move=> le_fg; apply: filterS2 le_fg => x; apply: le_trans. Qed.

Lemma dominated_by1 {T : Type} {K : numFieldType} {V : normedModType K} :
  @dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| <= k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma strictly_dominated_by1 {T : Type} {K : numFieldType} {V : normedModType K} :
  @strictly_dominated_by T K _ V fun1 = fun k f F => F [set x | `|f x| < k].
Proof.
rewrite funeq3E => k f F.
by congr F; rewrite funeqE => x/=; rewrite normr1 mulr1.
Qed.

Lemma ex_dom_bound {T : Type} {K : numFieldType} {V W : normedModType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F}:
  (\forall M \near +oo, dominated_by h M f F) <->
  exists M, dominated_by h M f F.
Proof.
rewrite /dominated_by; split => [/pinfty_ex_gt0[M M_gt0]|[M]] FM.
  by exists M.
have [] := pselect (exists x, (h x != 0) && (`|f x| <= M * `|h x|)); last first.
  rewrite -forallNE; move=> Nex; exists 0; rewrite real0; split => //.
  move=> k k_gt0; apply: filterS FM => x /= f_le_Mh.
  have /negP := Nex x; rewrite negb_and negbK f_le_Mh orbF => /eqP h_eq0.
  by rewrite h_eq0 normr0 !mulr0 in f_le_Mh *.
case => x0 /andP[hx0_neq0] /(le_trans (normr_ge0 _)) /ger0_real.
rewrite realrM // ?normr_eq0// => M_real.
exists M; split => // k Mk; apply: filterS FM => x /le_trans/= ->//.
by rewrite ler_wpmul2r// ltW.
Qed.

Lemma ex_strict_dom_bound {T : Type} {K : numFieldType} {V W : normedModType K}
    (h : T -> V) (f : T -> W) (F : set (set T)) {PF : ProperFilter F} :
  (\forall x \near F, h x != 0) ->
  (\forall M \near +oo, dominated_by h M f F) <->
   exists M, strictly_dominated_by h M f F.
Proof.
move=> hN0; rewrite ex_dom_bound /dominated_by /strictly_dominated_by.
split => -[] M FM; last by exists M; apply: filterS FM => x /ltW.
exists (M + 1); apply: filterS2 hN0 FM => x hN0 /le_lt_trans/= ->//.
by rewrite ltr_pmul2r ?normr_gt0// ltr_addl.
Qed.

Definition bounded_on {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) :=
  \forall M \near +oo, F [set x | `|f x| <= M].

Lemma boundedE {T : Type} {K : numFieldType} {V : normedModType K} :
  @bounded_on T K V = fun f F => \forall M \near +oo, dominated_by fun1 M f F.
Proof. by rewrite dominated_by1. Qed.

Lemma sub_boundedr (T : Type) (K : numFieldType) (V : normedModType K)
     (F G : set (set T)) : F `=>` G ->
  (@bounded_on T K V)^~ G `<=` bounded_on^~ F.
Proof. by move=> FG f; rewrite /bounded_on; apply: filterS => M; apply: FG. Qed.

Lemma sub_boundedl (T : Type) (K : numFieldType) (V : normedModType K)
     (f g : T -> V) (F : set (set T)) (FF : Filter F) :
   (\forall x \near F, `|f x| <= `|g x|) ->  bounded_on g F -> bounded_on f F.
Proof.
move=> le_fg; rewrite /bounded_on; apply: filterS => M.
by apply: filterS2 le_fg => x; apply: le_trans.
Qed.

Lemma ex_bound {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_on f F <-> exists M, F [set x | `|f x| <= M].
Proof. by rewrite boundedE ex_dom_bound dominated_by1. Qed.

Lemma ex_strict_bound {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : ProperFilter F}:
  bounded_on f F <-> exists M, F [set x | `|f x| < M].
Proof.
rewrite boundedE ex_strict_dom_bound ?strictly_dominated_by1//.
by near=> x; rewrite oner_eq0.
Grab Existential Variables. all: end_near. Qed.

Lemma ex_strict_bound_gt0 {T : Type} {K : numFieldType} {V : normedModType K}
  (f : T -> V) (F : set (set T)) {PF : Filter F}:
  bounded_on f F -> exists2 M, M > 0 & F [set x | `|f x| < M].
Proof.
move=> /pinfty_ex_gt0[M M_gt0 FM]; exists (M + 1); rewrite ?addr_gt0//.
by apply: filterS FM => x /le_lt_trans/= ->//; rewrite ltr_addl.
Qed.

Notation "[ 'bounded' E | x 'in' A ]" := (bounded_on (fun x => E) (globally A))
  (at level 0, x ident, format "[ 'bounded'  E  |  x  'in'  A ]").
Notation bounded_set := [set A | [bounded x | x in A]].
Notation bounded_fun := [set f | [bounded f x | x in setT]].

Lemma bounded_locally (T : topologicalType)
    (R : numFieldType) (V : normedModType R) (A : set T) (f : T -> V) :
  [bounded f x | x in A] -> [locally [bounded f x | x in A]].
Proof. by move=> /sub_boundedr AB x Ax; apply: AB; apply: within_nbhsW. Qed.

Notation "k .-lipschitz_on f" := (dominated_by (self_sub id) k (self_sub f))
  (at level 2, format "k .-lipschitz_on  f") : type_scope.

Definition sub_klipschitz (K : numFieldType) (V W : normedModType K) (k : K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> k.-lipschitz_on f G -> k.-lipschitz_on f F.
Proof. exact. Qed.

Definition lipschitz_on (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F : set (set (V * V))) :=
  \forall M \near +oo, M.-lipschitz_on f F.

Definition sub_lipschitz (K : numFieldType) (V W : normedModType K)
           (f : V -> W) (F G : set (set (V * V))) :
  F `=>` G -> lipschitz_on f G -> lipschitz_on f F.
Proof. by move=> FG; rewrite /lipschitz_on; apply: filterS => M; apply: FG. Qed.

Lemma klipschitzW (K : numFieldType) (V W : normedModType K) (k : K)
      (f : V -> W) (F : set (set (V * V))) {PF : ProperFilter F} :
  k.-lipschitz_on f F -> lipschitz_on f F.
Proof. by move=> f_lip; apply/ex_dom_bound; exists k. Qed.

Notation "k .-lipschitz_ A f" :=
  (k.-lipschitz_on f (globally (A `*` A)))
  (at level 2, A at level 0, format "k .-lipschitz_ A  f").
Notation "k .-lipschitz f" := (k.-lipschitz_setT f)
  (at level 2, format "k .-lipschitz  f") : type_scope.
Notation "[ 'lipschitz' E | x 'in' A ]" :=
  (lipschitz_on (fun x => E) (globally (A `*` A)))
  (at level 0, x ident, format "[ 'lipschitz'  E  |  x  'in'  A ]").
Notation lipschitz f := [lipschitz f x | x in setT].

Lemma klipschitz_locally (R : numFieldType) (V W : normedModType R)
   (k : R) (f : V -> W) (A : set V) :
  k.-lipschitz_A f -> [locally k.-lipschitz_A f].
Proof.
by move=> bndf x Ax; apply: sub_klipschitz bndf; apply: within_nbhsW.
Qed.

Lemma lipschitz_locally (R : numFieldType) (V W : normedModType R)
    (A : set V) (f : V -> W) :
  [lipschitz f x | x in A] -> [locally [lipschitz f x | x in A]].
Proof.
by move=> bndf x Ax; apply: sub_lipschitz bndf; apply: within_nbhsW.
Qed.

Lemma lipschitz_id (R : numFieldType) (V : normedModType R) : 1.-lipschitz (@id V).
Proof. by move=> [/= x y] _; rewrite mul1r. Qed.
Arguments lipschitz_id {R V}.

Section NormedModule_numFieldType.
Variables (R : numFieldType) (V : normedModType R).
Implicit Types (x y z : V).

Local Notation ball_norm := (ball_ (@normr R V)).

Local Notation nbhs_norm := (@nbhs_ball _ V).

Lemma norm_hausdorff : hausdorff V.
Proof.
rewrite ball_hausdorff => a b ab.
have ab2 : 0 < `|a - b| / 2 by apply divr_gt0 => //; rewrite normr_gt0 subr_eq0.
set r := PosNum ab2; exists (r, r) => /=.
apply/negPn/negP => /set0P[c] []; rewrite -ball_normE /ball_ => acr bcr.
have r22 : r%:num * 2 = r%:num + r%:num by rewrite (_ : 2 = 1 + 1) // mulrDr mulr1.
move: (ltr_add acr bcr); rewrite -r22 (distrC b c).
move/(le_lt_trans (ler_dist_add c a b)).
by rewrite -mulrA mulVr ?mulr1 ?ltxx // unitfE.
Qed.
Hint Extern 0 (hausdorff _) => solve[apply: norm_hausdorff] : core.

(* TODO: check if the following lemma are indeed useless *)
(*       i.e. where the generic lemma is applied, *)
(*            check that norm_hausdorff is not used in a hard way *)

Lemma norm_closeE x y : close x y = (x = y). Proof. exact: closeE. Qed.
Lemma norm_close_eq x y : close x y -> x = y. Proof. exact: close_eq. Qed.

Lemma norm_cvg_unique {F} {FF : ProperFilter F} : is_subset1 [set x : V | F --> x].
Proof. exact: cvg_unique. Qed.

Lemma norm_cvg_eq x y : x --> y -> x = y. Proof. exact: cvg_eq. Qed.
Lemma norm_lim_id x : lim x = x. Proof. exact: lim_id. Qed.

Lemma norm_cvg_lim {F} {FF : ProperFilter F} (l : V) : F --> l -> lim F = l.
Proof. exact: cvg_lim. Qed.

Lemma norm_lim_near_cst U {F} {FF : ProperFilter F} (l : V) (f : U -> V) :
   (\forall x \near F, f x = l) -> lim (f @ F) = l.
Proof. exact: lim_near_cst. Qed.

Lemma norm_lim_cst U {F} {FF : ProperFilter F} (k : V) :
   lim ((fun _ : U => k) @ F) = k.
Proof. exact: lim_cst. Qed.

Lemma norm_cvgi_unique {U : Type} {F} {FF : ProperFilter F} (f : U -> set V) :
  {near F, is_fun f} -> is_subset1 [set x : V | f `@ F --> x].
Proof. exact: cvgi_unique. Qed.

Lemma norm_cvgi_map_lim {U} {F} {FF : ProperFilter F} (f : U -> V -> Prop) (l : V) :
  F (fun x : U => is_subset1 (f x)) ->
  f `@ F --> l -> lim (f `@ F) = l.
Proof. exact: cvgi_map_lim. Qed.

Lemma distm_lt_split (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_split _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitr (z x y : V) (e : R) :
  `|z - x| < e / 2 -> `|z - y| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitr _ _ z x y e; rewrite -ball_normE. Qed.

Lemma distm_lt_splitl (z x y : V) (e : R) :
  `|x - z| < e / 2 -> `|y - z| < e / 2 -> `|x - y| < e.
Proof. by have := @ball_splitl _ _ z x y e; rewrite -ball_normE. Qed.

Lemma normm_leW (x : V) (e : R) : e > 0 -> `|x| <= e / 2 -> `|x| < e.
Proof.
move=> /posnumP[{}e] /le_lt_trans ->//.
by rewrite [X in _ < X]splitr ltr_spaddl.
Qed.

Lemma normm_lt_split (x y : V) (e : R) :
  `|x| < e / 2 -> `|y| < e / 2 -> `|x + y| < e.
Proof.
by move=> xlt ylt; rewrite -[y]opprK (@distm_lt_split 0) ?subr0 ?opprK ?add0r.
Qed.

Lemma cvg_distW {F : set (set V)} {FF : Filter F} (y : V) :
  (forall eps, 0 < eps -> \forall y' \near F, `|y - y'| <= eps) ->
  F --> y.
Proof.
move=> cv; apply/cvg_distP => _/posnumP[e]; near=> x.
by apply: normm_leW => //; near: x; apply: cv.
Grab Existential Variables. all: end_near. Qed.

Lemma cvg_bounded {F : set (set V)} {FF : Filter F} (y : V) :
  F --> y -> bounded_on id F.
Proof.
move=> /cvg_dist Fy; exists `|y|; rewrite normr_real; split => //= M.
rewrite -subr_gt0 => /Fy; apply: filterS => y' yy'; apply: ltW.
by rewrite -(@ltr_add2r _ (- `|y|)) (le_lt_trans (ler_sub_dist _ _))// distrC.
Qed.

End NormedModule_numFieldType.
Arguments cvg_bounded {_ _ F FF}.
Hint Extern 0 (hausdorff _) => solve[apply: norm_hausdorff] : core.

Module Export NbhsNorm.
Definition nbhs_simpl := (nbhs_simpl,@nbhs_nbhs_norm,@filter_from_norm_nbhs).
End NbhsNorm.

Section hausdorff.

Lemma Rhausdorff (R : realFieldType) : hausdorff [topologicalType of R^o].
Proof.
move=> x y clxy; apply/eqP; rewrite eq_le.
apply/(@in_segment_addgt0Pr _ x _ x) => _ /posnumP[e].
rewrite inE -ler_distl; set he := (e%:num / 2)%:pos.
have [z []] := clxy _ _ (nbhsx_ballx x he) (nbhsx_ballx y he).
move=> zx_he yz_he.
rewrite -(subrKA z) (le_trans (ler_norm_add _ _) _)// ltW //.
by rewrite (splitr e%:num) (distrC z); apply: ltr_add.
Qed.

End hausdorff.

Module Export NearNorm.
Definition near_simpl := (@near_simpl, @nbhs_normE, @filter_from_normE,
  @near_nbhs_norm).
Ltac near_simpl := rewrite ?near_simpl.
End NearNorm.

Lemma continuous_cvg_dist {R : numFieldType}
  (V W : normedModType R) (f : V -> W) x l :
  continuous f -> x --> l -> forall e : {posnum R}, `|f l - f x| < e%:num.
Proof.
move=> cf xl e.
move/cvg_dist: (cf l) => /(_ _ (posnum_gt0 e)).
rewrite nearE /= => /nbhs_ballP [i i0]; apply.
have /@cvg_dist : Filter [filter of x] by apply: filter_on_Filter.
move/(_ _ xl _ i0).
rewrite nearE /= => /nbhs_ballP [j j0].
by move/(_ _ (ballxx _ j0)); rewrite -ball_normE.
Qed.

Module BigmaxBigminr.
Section bigmax_bigmin.
Variable (R : realDomainType).

Lemma bigmaxr_mkcond I r (P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i =
     \big[maxr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite unlock; elim: r x => //= i r ihr x.
case P; rewrite ihr // max_r //; elim: r {ihr} => //= j r ihr.
by rewrite le_maxr ihr orbT.
Qed.

Lemma bigminr_maxr I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i = - \big[maxr/- x]_(i <- r | P i) - F i.
Proof.
by elim/big_rec2: _ => [|i y _ _ ->]; rewrite ?oppr_max opprK.
Qed.

Lemma bigminr_mkcond I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i =
     \big[minr/x]_(i <- r) (if P i then F i else x).
Proof.
rewrite !bigminr_maxr bigmaxr_mkcond; congr (- _).
by apply: eq_bigr => i _; case P.
Qed.

Lemma bigmaxr_split I r (P : pred I) (F1 F2 : I -> R) x :
  \big[maxr/x]_(i <- r | P i) (maxr (F1 i) (F2 i)) =
  maxr (\big[maxr/x]_(i <- r | P i) F1 i) (\big[maxr/x]_(i <- r | P i) F2 i).
Proof.
elim/big_rec3: _ => [|i y z _ _ ->]; rewrite ?maxxx //.
by rewrite maxCA -!maxA maxCA.
Qed.

Lemma bigminr_split I r (P : pred I) (F1 F2 : I -> R) x :
  \big[minr/x]_(i <- r | P i) (minr (F1 i) (F2 i)) =
  minr (\big[minr/x]_(i <- r | P i) F1 i) (\big[minr/x]_(i <- r | P i) F2 i).
Proof.
rewrite !bigminr_maxr -oppr_max -bigmaxr_split; congr (- _).
by apply: eq_bigr => i _; rewrite oppr_min.
Qed.

Lemma bigmaxr_idl I r (P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i = maxr x (\big[maxr/x]_(i <- r | P i) F i).
Proof.
rewrite -big_filter; elim: [seq i <- r | P i] => [|i l ihl].
  by rewrite big_nil maxxx.
by rewrite big_cons maxCA -ihl.
Qed.

Lemma bigminr_idl I r (P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i = minr x (\big[minr/x]_(i <- r | P i) F i).
Proof. by rewrite !bigminr_maxr {1}bigmaxr_idl oppr_max opprK. Qed.

Lemma bigmaxrID I r (a P : pred I) (F : I -> R) x :
  \big[maxr/x]_(i <- r | P i) F i =
  maxr (\big[maxr/x]_(i <- r | P i && a i) F i)
    (\big[maxr/x]_(i <- r | P i && ~~ a i) F i).
Proof.
rewrite -!(big_filter _ (fun _ => _ && _)) !filter_andb !big_filter.
rewrite ![in RHS](bigmaxr_mkcond _ _ F) !big_filter -bigmaxr_split.
have eqmax : forall i, P i ->
  maxr (if a i then F i else x) (if ~~ a i then F i else x) = maxr (F i) x.
  by move=> i _; case: (a i) => //=; rewrite maxC.
rewrite [RHS](eq_bigr _ eqmax) -!(big_filter _ P).
elim: [seq j <- r | P j] => [|j l ihl]; first by rewrite !big_nil.
by rewrite !big_cons -maxA -bigmaxr_idl ihl.
Qed.

Lemma bigminrID I r (a P : pred I) (F : I -> R) x :
  \big[minr/x]_(i <- r | P i) F i =
  minr (\big[minr/x]_(i <- r | P i && a i) F i)
    (\big[minr/x]_(i <- r | P i && ~~ a i) F i).
Proof. by rewrite !bigminr_maxr -oppr_max -bigmaxrID. Qed.

Lemma bigmaxr_seq1 I (i : I) (F : I -> R) x :
  \big[maxr/x]_(j <- [:: i]) F j = maxr (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigminr_seq1 I (i : I) (F : I -> R) x :
  \big[minr/x]_(j <- [:: i]) F j = minr (F i) x.
Proof. by rewrite big_cons big_nil. Qed.

Lemma bigmaxr_pred1_eq (I : finType) (i : I) (F : I -> R) x :
  \big[maxr/x]_(j | j == i) F j = maxr (F i) x.
Proof.
have [e1 <- _ [e_enum _]] := big_enumP (pred1 i).
by rewrite (perm_small_eq _ e_enum) enum1 ?bigmaxr_seq1.
Qed.

Lemma bigminr_pred1_eq (I : finType) (i : I) (F : I -> R) x :
  \big[minr/x]_(j | j == i) F j = minr (F i) x.
Proof. by rewrite bigminr_maxr bigmaxr_pred1_eq oppr_max !opprK. Qed.

Lemma bigmaxr_pred1 (I : finType) i (P : pred I) (F : I -> R) x :
  P =1 pred1 i -> \big[maxr/x]_(j | P j) F j = maxr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigmaxr_pred1_eq. Qed.

Lemma bigminr_pred1 (I : finType) i (P : pred I) (F : I -> R) x :
  P =1 pred1 i -> \big[minr/x]_(j | P j) F j = minr (F i) x.
Proof. by move/(eq_bigl _ _)->; apply: bigminr_pred1_eq. Qed.

Lemma bigmaxrD1 (I : finType) j (P : pred I) (F : I -> R) x :
  P j -> \big[maxr/x]_(i | P i) F i
    = maxr (F j) (\big[maxr/x]_(i | P i && (i != j)) F i).
Proof.
move=> Pj; rewrite (bigmaxrID _ (pred1 j)) [in RHS]bigmaxr_idl maxA.
by congr maxr; apply: bigmaxr_pred1 => i; rewrite /= andbC; case: eqP => //->.
Qed.

Lemma bigminrD1 (I : finType) j (P : pred I) (F : I -> R) x :
  P j -> \big[minr/x]_(i | P i) F i
    = minr (F j) (\big[minr/x]_(i | P i && (i != j)) F i).
Proof.
by move=> Pj; rewrite !bigminr_maxr (bigmaxrD1 _ _ Pj) oppr_max opprK.
Qed.

Lemma ler_bigmaxr_cond (I : finType) (P : pred I) (F : I -> R) x i0 :
  P i0 -> F i0 <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0; rewrite (bigmaxrD1 _ _ Pi0) le_maxr lexx. Qed.

Lemma bigminr_ler_cond (I : finType) (P : pred I) (F : I -> R) x i0 :
  P i0 -> \big[minr/x]_(i | P i) F i <= F i0.
Proof. by move=> Pi0; rewrite (bigminrD1 _ _ Pi0) le_minl lexx. Qed.

Lemma ler_bigmaxr (I : finType) (F : I -> R) (i0 : I) x :
  F i0 <= \big[maxr/x]_i F i.
Proof. exact: ler_bigmaxr_cond. Qed.

Lemma bigminr_ler (I : finType) (F : I -> R) (i0 : I) x :
  \big[minr/x]_i F i <= F i0.
Proof. exact: bigminr_ler_cond. Qed.

Lemma bigmaxr_lerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x <= m /\ forall i, P i -> F i <= m)
    (\big[maxr/x]_(i | P i) F i <= m).
Proof.
apply: (iffP idP) => [|[lexm leFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite le_maxl =>->.
rewrite bigmaxr_idl le_maxl => /andP[-> leFm]; split=> // i Pi.
by apply: le_trans leFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigminr_gerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m <= x /\ forall i, P i -> m <= F i)
    (m <= \big[minr/x]_(i | P i) F i).
Proof.
rewrite bigminr_maxr ler_oppr; apply: (iffP idP).
  by move=> /bigmaxr_lerP [? lemF]; split=> [|??]; rewrite -ler_opp2 ?lemF.
by move=> [? lemF]; apply/bigmaxr_lerP; split=> [|??]; rewrite ler_opp2 ?lemF.
Qed.

Lemma bigmaxr_sup (I : finType) i0 (P : pred I) m (F : I -> R) x :
  P i0 -> m <= F i0 -> m <= \big[maxr/x]_(i | P i) F i.
Proof. by move=> Pi0 ?; apply: le_trans (ler_bigmaxr_cond _ _ Pi0). Qed.

Lemma bigminr_inf (I : finType) i0 (P : pred I) m (F : I -> R) x :
  P i0 -> F i0 <= m -> \big[minr/x]_(i | P i) F i <= m.
Proof. by move=> Pi0 ?; apply: le_trans (bigminr_ler_cond _ _ Pi0) _. Qed.

Lemma bigmaxr_ltrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x < m /\ forall i, P i -> F i < m)
    (\big[maxr/x]_(i | P i) F i < m).
Proof.
apply: (iffP idP) => [|[ltxm ltFm]]; last first.
  by elim/big_ind: _ => // ??; rewrite lt_maxl =>->.
rewrite bigmaxr_idl lt_maxl => /andP[-> ltFm]; split=> // i Pi.
by apply: le_lt_trans ltFm; apply: ler_bigmaxr_cond.
Qed.

Lemma bigminr_gtrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m < x /\ forall i, P i -> m < F i)
    (m < \big[minr/x]_(i | P i) F i).
Proof.
rewrite bigminr_maxr ltr_oppr; apply: (iffP idP).
  by move=> /bigmaxr_ltrP [? ltmF]; split=> [|??]; rewrite -ltr_opp2 ?ltmF.
by move=> [? ltmF]; apply/bigmaxr_ltrP; split=> [|??]; rewrite ltr_opp2 ?ltmF.
Qed.

Lemma bigmaxr_gerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m <= x \/ exists2 i, P i & m <= F i)
  (m <= \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[lemx|[i Pi lemFi]]]; last 2 first.
- by rewrite bigmaxr_idl le_maxr lemx.
- by rewrite (bigmaxrD1 _ _ Pi) le_maxr lemFi.
rewrite leNgt => /bigmaxr_ltrP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -leNgt; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -leNgt; right; exists i.
Qed.

Lemma bigminr_lerP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x <= m \/ exists2 i, P i & F i <= m)
  (\big[minr/x]_(i | P i) F i <= m).
Proof.
rewrite bigminr_maxr ler_oppl; apply: (iffP idP).
  by move=> /bigmaxr_gerP [?|[i ??]]; [left|right; exists i => //];
    rewrite -ler_opp2.
by move=> [?|[i ??]]; apply/bigmaxr_gerP; [left|right; exists i => //];
  rewrite ler_opp2.
Qed.

Lemma bigmaxr_gtrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (m < x \/ exists2 i, P i & m < F i)
  (m < \big[maxr/x]_(i | P i) F i).
Proof.
apply: (iffP idP) => [|[ltmx|[i Pi ltmFi]]]; last 2 first.
- by rewrite bigmaxr_idl lt_maxr ltmx.
- by rewrite (bigmaxrD1 _ _ Pi) lt_maxr ltmFi.
rewrite ltNge => /bigmaxr_lerP /asboolPn.
rewrite asbool_and negb_and => /orP [/asboolPn/negP|/existsp_asboolPn [i]].
  by rewrite -ltNge; left.
by move=> /asboolPn/imply_asboolPn [Pi /negP]; rewrite -ltNge; right; exists i.
Qed.

Lemma bigminr_ltrP (I : finType) (P : pred I) m (F : I -> R) x :
  reflect (x < m \/ exists2 i, P i & F i < m)
  (\big[minr/x]_(i | P i) F i < m).
Proof.
rewrite bigminr_maxr ltr_oppl; apply: (iffP idP).
  by move=> /bigmaxr_gtrP [?|[i ??]]; [left|right; exists i => //];
    rewrite -ltr_opp2.
by move=> [?|[i ??]]; apply/bigmaxr_gtrP; [left|right; exists i => //];
  rewrite ltr_opp2.
Qed.

Lemma bigmaxr_eq_arg (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> x <= F i) ->
  \big[maxr/x]_(i | P i) F i = F [arg max_(i > i0 | P i) F i]%O.
Proof.
move=> Pi0; case: arg_maxP => //= i Pi PF PxF.
apply/eqP; rewrite eq_le ler_bigmaxr_cond // andbT.
by apply/bigmaxr_lerP; split => //; exact: PxF.
Qed.

Lemma bigminr_eq_arg (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> F i <= x) ->
  \big[minr/x]_(i | P i) F i = F [arg min_(i < i0 | P i) F i]%O.
Proof.
move=> Pi0; case: arg_minP => //= i Pi PF PFx.
apply/eqP; rewrite eq_le bigminr_ler_cond //=.
by apply/bigminr_gerP; split => //; exact: PFx.
Qed.

Lemma eq_bigmaxr (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> x <= F i) ->
  {i0 | i0 \in I & \big[maxr/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigmaxr_eq_arg Pi0) //; eexists. Qed.

Lemma eq_bigminr (I : finType) i0 (P : pred I) (F : I -> R) x :
  P i0 -> (forall i, P i -> F i <= x) ->
  {i0 | i0 \in I & \big[minr/x]_(i | P i) F i = F i0}.
Proof. by move=> Pi0 Hx; rewrite (bigminr_eq_arg Pi0) //; eexists. Qed.

End bigmax_bigmin.
Module Exports.
Arguments bigmaxr_mkcond {R I r}.
Arguments bigmaxrID {R I r}.
Arguments bigmaxr_pred1 {R I} i {P F}.
Arguments bigmaxrD1 {R I} j {P F}.
Arguments ler_bigmaxr_cond {R I P F}.
Arguments ler_bigmaxr {R I F}.
Arguments bigmaxr_sup {R I} i0 {P m F}.
Arguments bigminr_mkcond {R I r}.
Arguments bigminrID {R I r}.
Arguments bigminr_pred1 {R I} i {P F}.
Arguments bigminrD1 {R I} j {P F}.
Arguments bigminr_ler_cond {R I P F}.
Arguments bigminr_ler {R I F}.
Arguments bigminr_inf {R I} i0 {P m F}.
Arguments bigmaxr_eq_arg {R I} i0 {P F}.
Arguments bigminr_eq_arg {R I} i0 {P F}.
Arguments eq_bigmaxr {R I} i0 {P F}.
Arguments eq_bigminr {R I} i0 {P F}.
End Exports.
End BigmaxBigminr.
Export BigmaxBigminr.Exports.

(** ** Matrices *)

Section mx_norm.
Variables (K : numDomainType) (m n : nat).
Implicit Types x y : 'M[K]_(m, n).

Definition mx_norm x : K := (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:nngnum.

Lemma mx_normE x : mx_norm x = (\big[maxr/0%:nng]_i `|x i.1 i.2|%:nng)%:nngnum.
Proof. by []. Qed.

Lemma ler_mx_norm_add x y : mx_norm (x + y) <= mx_norm x + mx_norm y.
Proof.
rewrite nng_le; apply/BigmaxrNonneg.bigmaxr_lerP; split.
  exact: addr_ge0.
move=> ij _; rewrite mxE; apply: le_trans (ler_norm_add _ _) _.
rewrite ler_add // -nng_abs_le //= -nng_le /= normr_id nng_le;
  exact/BigmaxrNonneg.ler_bigmaxr.
Qed.

Lemma mx_norm_eq0 x : mx_norm x = 0 -> x = 0.
Proof.
move/eqP; rewrite eq_le => /andP [/BigmaxrNonneg.bigmaxr_lerP [_ x0] _].
apply/matrixP => i j; rewrite mxE; apply/eqP.
by rewrite -nng_abs_eq0 eq_le (x0 (i,j)) // andTb -nng_le /= normr_ge0.
Qed.

Lemma mx_norm0 : mx_norm 0 = 0.
Proof.
rewrite /mx_norm (eq_bigr (fun=> 0%:nng)) /=.
  by elim/big_ind : _ => // a b /val_inj ->{a} /val_inj ->{b}; rewrite maxxx.
by move=> i _; apply val_inj => /=; rewrite mxE normr0.
Qed.

Lemma mx_norm_neq0 x : mx_norm x != 0 -> exists i, mx_norm x = `|x i.1 i.2|.
Proof.
rewrite /mx_norm.
elim/big_ind : _ => [|a b Ha Hb H|/= i _ _]; [by rewrite eqxx| |by exists i].
case: (leP a b) => ab.
+ suff /Hb[i xi] : b != 0%:nng by exists i.
  by apply: contra H => b0; rewrite max_r.
+ suff /Ha[i xi] : a != 0%:nng by exists i.
  by apply: contra H => a0; rewrite max_l // ltW.
Qed.

Lemma mx_norm_natmul x k : mx_norm (x *+ k) = (mx_norm x) *+ k.
Proof.
rewrite [in RHS]/mx_norm; elim: k => [|k ih]; first by rewrite !mulr0n mx_norm0.
rewrite !mulrS; apply/eqP; rewrite eq_le; apply/andP; split.
  by rewrite -ih; exact/ler_mx_norm_add.
have [/eqP/mx_norm_eq0->|x0] := boolP (mx_norm x == 0).
  by rewrite -/(mx_norm 0) -/(mx_norm 0) !(mul0rn,addr0,mx_norm0).
rewrite -/(mx_norm x) -nng_abs_le; last by rewrite addr_ge0 // mulrn_wge0.
apply/BigmaxrNonneg.bigmaxr_gerP; right => /=.
have [i Hi] := mx_norm_neq0 x0.
exists i => //; rewrite Hi -!mulrS -normrMn mulmxnE.
rewrite le_eqVlt; apply/orP; left; apply/eqP/val_inj => /=; by rewrite normr_id.
Qed.

Lemma mx_normN x : mx_norm (- x) = mx_norm x.
Proof.
congr (_%:nngnum).
by apply eq_bigr => /= ? _; apply/eqP; rewrite mxE -nng_eq //= normrN.
Qed.

End mx_norm.

Lemma mx_normrE (K : realDomainType) (m n : nat) (x : 'M[K]_(m, n)) :
  mx_norm x = \big[maxr/0]_ij `|x ij.1 ij.2|.
Proof.
rewrite /mx_norm; apply/esym.
elim/big_ind2 : _ => //= a a' b b' ->{a'} ->{b'}.
case: (leP a b) => ab; by [rewrite max_r | rewrite max_l // ltW].
Qed.

Definition matrix_normedZmodMixin (K : numDomainType) (m n : nat) :=
  @Num.NormedMixin _ _ _ (@mx_norm K m.+1 n.+1) (@ler_mx_norm_add _ _ _)
    (@mx_norm_eq0 _ _ _) (@mx_norm_natmul _ _ _) (@mx_normN _ _ _).

Canonical matrix_normedZmodType (K : numDomainType) (m n : nat) :=
  NormedZmodType K 'M[K]_(m.+1, n.+1) (matrix_normedZmodMixin K m n).

Section matrix_NormedModule.
Variables (K : numFieldType) (m n : nat).

Lemma mx_norm_ball :
  @ball _ [pseudoMetricType K of 'M[K^o]_(m.+1, n.+1)] = ball_ (fun x => `| x |).
Proof.
rewrite /= /normr /= predeq3E => x e y; split.
- move=> xe_y; rewrite /ball_/= mx_normE.
  (* TODO:  lemma : ball x e y -> 0 < e *)
  have lee0 : ( 0 < e) by rewrite (le_lt_trans _ (xe_y ord0 ord0)) //.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  rewrite nng_lt; apply/BigmaxrNonneg.bigmaxr_ltrP.
- split; [rewrite -nng_lt //= | move=> ??; rewrite !mxE; exact: xe_y].
  rewrite /ball_/= mx_normE => H.
  have lee0 : (0 < e) by rewrite (le_lt_trans _ H) // nonnegnum_ge0.
  move : H.
  have -> : e = (Nonneg.NngNum _ (ltW lee0))%:nngnum by [].
  move => /BigmaxrNonneg.bigmaxr_ltrP => -[e0 xey] i j.
  move: (xey (i, j)); rewrite !mxE; exact.
Qed.

Definition matrix_PseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin mx_norm_ball.
Canonical matrix_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K 'M[K^o]_(m.+1, n.+1) matrix_PseudoMetricNormedZmodMixin.

Lemma mx_normZ (l : K) (x : 'M[K]_(m.+1, n.+1)) : `| l *: x | = `| l | * `| x |.
Proof.
rewrite {1 3}/normr /= !mx_normE
 (eq_bigr (fun i => (`|l| * `|x i.1 i.2|)%:nng)); last first.
  by move=> i _; rewrite mxE //=; apply/eqP; rewrite -nng_eq /= normrM.
elim/big_ind2 : _ => // [|a b c d bE dE]; first by rewrite mulr0.
rewrite nonneg_maxr; congr (maxr _ _)%:nngnum; exact/val_inj.
Qed.

Definition matrix_NormedModMixin := NormedModMixin mx_normZ.
Canonical matrix_normedModType :=
  NormedModType K 'M[K^o]_(m.+1, n.+1) matrix_NormedModMixin.

End matrix_NormedModule.

(** ** Pairs *)

Section prod_PseudoMetricNormedZmodule.
Context {K : numDomainType} {U V : pseudoMetricNormedZmodType K}.

Lemma ball_prod_normE : ball = ball_ (fun x => `| x : U * V |).
Proof.
rewrite funeq2E => - [xu xv] e; rewrite predeqE => - [yu yv].
rewrite /ball /= /prod_ball -!ball_normE /ball_ /=.
by rewrite comparable_lt_maxl// ?real_comparable//; split=> /andP.
Qed.

Lemma prod_norm_ball : @ball _ [pseudoMetricType K of U * V] = ball_ (fun x => `|x|).
Proof. by rewrite /= - ball_prod_normE. Qed.

Definition prod_pseudoMetricNormedZmodMixin :=
  PseudoMetricNormedZmodule.Mixin prod_norm_ball.
Canonical prod_pseudoMetricNormedZmodType :=
  PseudoMetricNormedZmodType K (U * V) prod_pseudoMetricNormedZmodMixin.

End prod_PseudoMetricNormedZmodule.

Section prod_NormedModule.
Context {K : numDomainType} {U V : normedModType K}.

Lemma prod_norm_scale (l : K) (x : U * V) : `| l *: x | = `|l| * `| x |.
Proof. by rewrite prod_normE /= !normmZ maxr_pmulr. Qed.

Definition prod_NormedModMixin := NormedModMixin prod_norm_scale.
Canonical prod_normedModType :=
  NormedModType K (U * V) prod_NormedModMixin.

End prod_NormedModule.

Section example_of_sharing.
Variables (K : numDomainType).

Example matrix_triangke m n (M N : 'M[K]_(m.+1, n.+1)) :
  `|M + N| <= `|M| + `|N|.
Proof. apply ler_norm_add. Qed.

Example pair_triangle (x y : K * K) : `|x + y| <= `|x| + `|y|.
Proof. apply ler_norm_add. Qed.

End example_of_sharing.

Section prod_NormedModule_lemmas.

Context {T : Type} {K : numDomainType} {U V : normedModType K}.

Lemma cvg_dist2P {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) <->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `| (y, z) - (y', z') | < eps.
Proof. exact: cvg_distP. Qed.

(* Lemma cvg_dist_supP {F : set (set U)} {G : set (set V)} *)
(*   {FF : Filter F} {FG : Filter G} (y : U) (z : V): *)
(*   (F, G) --> (y, z) <-> *)
(*   forall eps : {posnum R}, {near F & G, forall y' z', *)
(*           (`|[y - y']| < eps) /\ (`|[z - z']| < eps) }. *)
(* Proof. *)
(* rewrite cvg_ballP; split => [] P eps. *)
(* - have [[A B] /=[FA GB] ABP] := P eps; exists (A, B) => -//[a b] [/= Aa Bb]. *)
(*   apply/andP; rewrite -ltr_maxl. *)
(*   have /= := (@sub_ball_norm_rev _ _ (_, _)). *)

Lemma cvg_dist2 {F : set (set U)} {G : set (set V)}
  {FF : Filter F} {FG : Filter G} (y : U) (z : V):
  (F, G) --> (y, z) ->
  forall eps, 0 < eps ->
   \forall y' \near F & z' \near G, `|(y, z) - (y', z')| < eps.
Proof. by rewrite cvg_distP. Qed.

End prod_NormedModule_lemmas.
Arguments cvg_dist2 {_ _ _ F G FF FG}.

(** Rings with absolute values are normed modules *)

(*Definition AbsRing_NormedModMixin (K : absRingType) :=
  @NormedModule.Mixin K _ _ _ (abs : K^o -> R) ler_abs_add absrM (ball_absE K)
  absr0_eq0.
Canonical AbsRing_NormedModType (K : absRingType) :=
  NormedModType K K^o (AbsRing_NormedModMixin _).*)

(** Normed vector spaces have some continuous functions *)

(* kludge *)
Global Instance filter_nbhs (K' : numFieldType) (k : K'^o) :
  Filter (nbhs k).
Proof.
exact: (@nbhs_filter [topologicalType of K'^o]).
Qed.

Section NVS_continuity_normedModType.
Context {K : numFieldType} {V : normedModType K}.
Local Notation "'+oo'" := (pinfty_nbhs K).

Lemma add_continuous : continuous (fun z : V * V => z.1 + z.2).
Proof.
move=> [/=x y]; apply/cvg_distP=> _/posnumP[e].
rewrite !near_simpl /=; near=> a b => /=; rewrite opprD addrACA.
by rewrite normm_lt_split //; [near: a|near: b]; apply: cvg_dist.
Grab Existential Variables. all: end_near. Qed.

Lemma natmul_continuous n : continuous (fun x : V => x *+ n).
Proof.
case: n => [|n] x; first exact: cvg_cst.
apply/cvg_distP=> _/posnumP[e]; rewrite !near_simpl /=; near=> a.
rewrite -mulrnBl normrMn -mulr_natr -ltr_pdivl_mulr//.
by near: a; apply: cvg_dist.
Grab Existential Variables. all: end_near. Qed.

Lemma scale_continuous : continuous (fun z : K^o * V => z.1 *: z.2).
Proof.
move=> [k x]; apply/cvg_distP=> _/posnumP[e].
rewrite !near_simpl /=; near +oo => M.
have M_gt0 : M > 0 by near: M; apply: nbhs_pinfty_gt_real; rewrite real0.
near=> l z => /=.
rewrite (@distm_lt_split _ _ (k *: z)) // -?(scalerBr, scalerBl) normmZ.
  suff: (`|k| + 1) * `|x - z| < e%:num / 2.
    by apply: le_lt_trans; rewrite ler_pmul// ler_addl.
  rewrite -ltr_pdivl_mull // ?(lt_le_trans ltr01) ?ler_addr //; near: z.
  by apply: cvg_dist; rewrite // mulr_gt0 // ?invr_gt0 ltr_paddl.
have zM : `|z| <= M by near: z; near: M; apply:cvg_bounded; apply: cvg_refl.
rewrite (le_lt_trans (ler_pmul _ _ (lexx _) zM)) // ?ltW // -ltr_pdivl_mulr//.
by near: l; apply: (cvg_dist (_ : K^o)); rewrite // mulr_gt0// invr_gt0.
Grab Existential Variables. all: end_near. Qed.

Arguments scale_continuous _ _ : clear implicits.

Lemma scaler_continuous k : continuous (fun x : V => k *: x).
Proof.
by move=> x; apply: (cvg_comp2 (cvg_cst _) cvg_id (scale_continuous (_, _))).
Qed.

Lemma scalel_continuous (x : V) : continuous (fun k : K^o => k *: x).
Proof.
by move=> k; apply: (cvg_comp2 cvg_id (cvg_cst _) (scale_continuous (_, _))).
Qed.

Lemma opp_continuous : continuous (@GRing.opp V).
Proof.
move=> x; rewrite -scaleN1r => P /scaler_continuous /=.
by rewrite !nbhs_nearE near_map; apply: filterS => x'; rewrite scaleN1r.
Qed.

(** Continuity of norm *)

Lemma norm_continuous : continuous ((@normr _ V) : V -> K^o).
Proof.
move=> x; apply/(@cvg_distP _ [normedModType K of K^o]) => _/posnumP[e] /=.
rewrite !near_simpl; apply/nbhs_normP; exists e%:num => // y Hy.
by rewrite -ball_normE in Hy; apply/(le_lt_trans (ler_dist_dist _ _)).
Qed.

End NVS_continuity_normedModType.

Lemma cvg_dist0 {U} {K : numFieldType} {V : normedModType K}
  {F : set (set U)} {FF : Filter F} (f : U -> V) :
  (fun x => `|f x|) @ F --> (0 : K^o)
  -> f @ F --> (0 : V).
Proof.
move=> /(cvg_dist (_ : K^o)) fx0; apply/cvg_distP => _/posnumP[e].
rewrite near_simpl; have := fx0 _ [gt0 of e%:num]; rewrite near_simpl.
by apply: filterS => x; rewrite !sub0r !normrN [ `|_| ]ger0_norm.
Qed.

Section NVS_continuity_mul.

Context {K : numFieldType}.

Lemma mul_continuous : continuous (fun z : K^o * K^o => z.1 * z.2).
Proof. exact: scale_continuous. Qed.

Lemma inv_continuous x : x != 0 -> {for x, continuous (GRing.inv : K^o -> K^o)}.
Proof.
move=> x_neq0 /=; apply/cvg_distP => _/posnumP[e]; rewrite !nearE/=; near=> y.
have y_gt : `|y| > `|x| / 2.
  have /(le_lt_trans (ler_sub_dist _ _)) : `|x - y| < `|x| / 2.
    by near: y; apply: cvg_dist; rewrite // divr_gt0// normr_gt0//.
  by rewrite ltr_subl_addr -ltr_subl_addl {1}[ `|x| ]splitr addrK.
have y_neq0 : y != 0.
  by rewrite -normr_eq0 gt_eqF// (le_lt_trans _ y_gt) ?divr_ge0.
rewrite /= -div1r -[y^-1]div1r -mulNr addf_div// mul1r mulN1r normrM normfV.
rewrite ltr_pdivr_mulr ?normr_gt0 ?mulf_neq0//.
apply: (@lt_le_trans _ _ (e%:num * (`|x| * (`|x| / 2)))).
  by rewrite distrC; near: y; apply: cvg_dist; rewrite ?mulr_gt0// ?normr_gt0.
by rewrite normrM !ler_wpmul2l// ltW.
Grab Existential Variables. all: end_near. Qed.

End NVS_continuity_mul.

Section cvg_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> V) (s : T -> K^o) (k : K^o) (x : T) (a b : V).

Lemma cvgN f a : f @ F --> a -> (- f) @ F --> - a.
Proof. by move=> ?; apply: continuous_cvg => //; exact: opp_continuous. Qed.

Lemma is_cvgN f : cvg (f @ F) -> cvg (- f @ F).
Proof. by move=> /cvgN /cvgP. Qed.

Lemma is_cvgNE f : cvg ((- f) @ F) = cvg (f @ F).
Proof. by rewrite propeqE; split=> /cvgN; rewrite ?opprK => /cvgP. Qed.

Lemma cvgMn f n a : f @ F --> a -> ((@GRing.natmul _)^~n \o f) @ F --> a *+ n.
Proof. by move=> ?;  apply: continuous_cvg => //; exact: natmul_continuous. Qed.

Lemma is_cvgMn f n : cvg (f @ F) -> cvg (((@GRing.natmul _)^~n \o f) @ F).
Proof. by move=> /cvgMn /cvgP. Qed.

Lemma cvgD f g a b : f @ F --> a -> g @ F --> b -> (f + g) @ F --> a + b.
Proof. by move=> ? ?; apply: continuous2_cvg => //; exact: add_continuous. Qed.

Lemma is_cvgD f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f + g @ F).
Proof. by have := cvgP _ (cvgD _ _); apply. Qed.

Lemma cvgB f g a b : f @ F --> a -> g @ F --> b -> (f - g) @ F --> a - b.
Proof. by move=> ? ?; apply: cvgD => //; apply: cvgN. Qed.

Lemma is_cvgB f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f - g @ F).
Proof. by have := cvgP _ (cvgB _ _); apply. Qed.

Lemma is_cvgDlE f g : cvg (g @ F) -> cvg ((f + g) @ F) = cvg (f @ F).
Proof.
move=> g_cvg; rewrite propeqE; split; last by move=> /is_cvgD; apply.
by move=> /is_cvgB /(_ g_cvg); rewrite addrK.
Qed.

Lemma is_cvgDrE f g : cvg (f @ F) -> cvg ((f + g) @ F) = cvg (g @ F).
Proof. by rewrite addrC; apply: is_cvgDlE. Qed.

Lemma cvgZ s f k a : s @ F --> k -> f @ F --> a ->
                     s x *: f x @[x --> F] --> k *: a.
Proof. move=> ? ?; apply: continuous2_cvg => //; exact: scale_continuous. Qed.

Lemma is_cvgZ s f : cvg (s @ F) ->
  cvg (f @ F) -> cvg ((fun x => s x *: f x) @ F).
Proof. by have := cvgP _ (cvgZ _ _); apply. Qed.

Lemma cvgZl s k a : s @ F --> k -> s x *: a @[x --> F] --> k *: a.
Proof. by move=> ?; apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZl s a : cvg (s @ F) -> cvg ((fun x => s x *: a) @ F).
Proof. by have := cvgP _ (cvgZl  _); apply. Qed.

Lemma cvgZr k f a : f @ F --> a -> k \*: f @ F --> k *: a.
Proof. apply: cvgZ => //; exact: cvg_cst. Qed.

Lemma is_cvgZr k f : cvg (f @ F) -> cvg (k *: f  @ F).
Proof. by have := cvgP _ (cvgZr  _); apply. Qed.

Lemma is_cvgZrE k f : k != 0 -> cvg (k *: f @ F) = cvg (f @ F).
Proof.
move=> k_neq0; rewrite propeqE; split => [/(@cvgZr k^-1)|/(@cvgZr k)/cvgP//].
by under [_ \*: _]funext => x /= do rewrite scalerK//; apply: cvgP.
Qed.

Lemma cvg_norm f a : f @ F --> a -> `|f x| @[x --> F] --> (`|a| : K^o).
Proof. exact: (continuous_cvg _ (@norm_continuous _ _ _)). Qed.

Lemma is_cvg_norm f : cvg (f @ F) -> cvg ((Num.norm \o f : T -> K^o) @ F).
Proof. by have := cvgP _ (cvg_norm _); apply. Qed.

End cvg_composition.

Section cvg_composition_field.

Context {K : numFieldType}  {T : topologicalType}.
Context (F : set (set T)) {FF : Filter F}.
Implicit Types (f g : T -> K^o) (a b : K^o).

Lemma cvgM f g a b : f @ F --> a -> g @ F --> b -> (f * g) @ F --> a * b.
Proof. exact: cvgZ. Qed.

Lemma cvgMl f a b : f @ F --> a -> (f x * b) @[x --> F] --> a * b.
Proof. exact: cvgZl. Qed.

Lemma cvgMr g a b : g @ F --> b -> (a * g x) @[x --> F] --> a * b.
Proof. exact: cvgZr. Qed.

Lemma is_cvgM f g : cvg (f @ F) -> cvg (g @ F) -> cvg (f * g @ F).
Proof. exact: is_cvgZ. Qed.

Lemma is_cvgMr g a (f := fun=> a) : cvg (g @ F) -> cvg (f * g @ F).
Proof. exact: is_cvgZr. Qed.

Lemma is_cvgMrE g a (f := fun=> a) : a != 0 -> cvg (f * g @ F) = cvg (g @ F).
Proof. exact: is_cvgZrE. Qed.

Lemma is_cvgMl f a (g := fun=> a) : cvg (f @ F) -> cvg (f * g @ F).
Proof. by move=> f_cvg; rewrite mulrC; apply: is_cvgMr. Qed.

Lemma is_cvgMlE f a (g := fun=> a) : a != 0 -> cvg (f * g @ F) = cvg (f @ F).
Proof. by move=> a_neq0; rewrite mulrC is_cvgMrE. Qed.

Lemma cvgV f a : a != 0 -> f @ F --> a -> (f x)^-1 @[x --> F] --> a^-1.
Proof.
by move=> k_neq0 f_cvg; apply: continuous_cvg => //; apply: inv_continuous.
Qed.

Lemma is_cvgV f : lim (f @ F) != 0 -> cvg (f @ F) -> cvg ((fun x => (f x)^-1) @ F).
Proof. by move=> /cvgV cvf /cvf /cvgP. Qed.

End cvg_composition_field.

Section limit_composition.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> V) (s : T -> K^o) (k : K^o) (x : T) (a : V).

Lemma limN f : cvg (f @ F) -> lim (- f @ F) = - lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgN. Qed.

Lemma limD f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f + g @ F) = lim (f @ F) + lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgD. Qed.

Lemma limB f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f - g @ F) = lim (f @ F) - lim (g @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgB. Qed.

Lemma limZ s f : cvg (s @ F) -> cvg (f @ F) ->
   lim ((fun x => s x *: f x) @ F) = lim (s @ F) *: lim (f @ F).
Proof. by move=> ? ?; apply: cvg_lim => //; apply: cvgZ. Qed.

Lemma limZl s a : cvg (s @ F) ->
   lim ((fun x => s x *: a) @ F) = lim (s @ F) *: a.
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZl. Qed.

Lemma limZr k f : cvg (f @ F) -> lim (k *: f @ F) = k *: lim (f @ F).
Proof. by move=> ?; apply: cvg_lim => //; apply: cvgZr. Qed.

Lemma lim_norm f : cvg (f @ F) -> lim ((fun x => `|f x| : K^o) @ F) = `|lim (f @ F)|.
Proof. by move=> ?; apply: (@cvg_lim [topologicalType of K^o]) => //; apply: cvg_norm. Qed.

End limit_composition.

Section limit_composition_field.

Context {K : numFieldType}  {T : topologicalType}.
Context (F : set (set T)) {FF : ProperFilter F}.
Implicit Types (f g : T -> K^o).

Lemma limM f g : cvg (f @ F) -> cvg (g @ F) ->
   lim (f * g @ F) = lim (f @ F) * lim (g @ F).
Proof.
by move=> ? ?; apply: (@cvg_lim [topologicalType of K^o]) => //; apply: cvgM.
Qed.

Lemma limV f : cvg (f @ F) -> lim (f @ F) != 0 -> lim ((fun x => (f x)^-1) @ F) = (lim (f @ F))^-1.
Proof.
by move=> ? ?; apply: (@cvg_lim [topologicalType of K^o]) => //; apply: cvgV.
Qed.

End limit_composition_field.

Section local_continuity.

Context {K : numFieldType} {V : normedModType K} {T : topologicalType}.
Implicit Types (f g : T -> V) (s t : T -> K^o) (x : T) (k : K^o) (a : V).

Lemma continuousN (f : T -> V) x :
  {for x, continuous f} -> {for x, continuous (fun x => - f x)}.
Proof. by move=> ?; apply: cvgN. Qed.

Lemma continuousD f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f + g)}.
Proof. by move=> f_cont g_cont; apply: cvgD. Qed.

Lemma continuousB f g x :
  {for x, continuous f} -> {for x, continuous g} ->
  {for x, continuous (f - g)}.
Proof. by move=> f_cont g_cont; apply: cvgB. Qed.

Lemma continuousZ s f x :
  {for x, continuous s} -> {for x, continuous f} ->
  {for x, continuous (fun x => s x *: f x)}.
Proof. by move=> ? ?; apply: cvgZ. Qed.

Lemma continuousZr f k x :
  {for x, continuous f} -> {for x, continuous (k \*: f)}.
Proof. by move=> ?; apply: cvgZr. Qed.

Lemma continuousZl s a x :
  {for x, continuous s} -> {for x, continuous (fun z => s z *: a)}.
Proof. by move=> ?; apply: cvgZl. Qed.

Lemma continuousM s t x :
  {for x, continuous s} -> {for x, continuous t} ->
  {for x, continuous (s * t)}.
Proof. by move=> f_cont g_cont; apply: cvgM. Qed.

Lemma continuousV s x : s x != 0 ->
  {for x, continuous s} -> {for x, continuous (fun x => (s x)^-1)}.
Proof. by move=> ?; apply: cvgV. Qed.

End local_continuity.

(** ** Complete Normed Modules *)

Module CompleteNormedModule.

Section ClassDef.

Variable K : numFieldType.

Record class_of (T : Type) := Class {
  base : NormedModule.class_of K T ;
  mixin : Complete.axiom (PseudoMetric.Pack base)
}.
Local Coercion base : class_of >-> NormedModule.class_of.
Definition base2 T (cT : class_of T) : CompletePseudoMetric.class_of K T :=
  @CompletePseudoMetric.Class _ _ (@base T cT) (@mixin T cT).
Local Coercion base2 : class_of >-> CompletePseudoMetric.class_of.

Structure type (phK : phant K) := Pack { sort; _ : class_of sort }.
Local Coercion sort : type >-> Sortclass.

Variables (phK : phant K) (cT : type phK) (T : Type).

Definition class := let: Pack _ c := cT return class_of cT in c.

Definition pack :=
  fun bT (b : NormedModule.class_of K T) & phant_id (@NormedModule.class K phK bT) b =>
  fun mT m & phant_id (@Complete.class mT) (@Complete.Class T b m) =>
    Pack phK (@Class T b m).
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition eqType := @Equality.Pack cT xclass.
Definition choiceType := @Choice.Pack cT xclass.
Definition zmodType := @GRing.Zmodule.Pack cT xclass.
Definition normedZmodType := @Num.NormedZmodule.Pack K phK cT xclass.
Definition lmodType := @GRing.Lmodule.Pack K phK cT xclass.
Definition pointedType := @Pointed.Pack cT xclass.
Definition filteredType := @Filtered.Pack cT cT xclass.
Definition topologicalType := @Topological.Pack cT xclass.
Definition uniformType := @Uniform.Pack cT xclass.
Definition pseudoMetricType := @PseudoMetric.Pack K cT xclass.
Definition pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK cT xclass.
Definition normedModType := @NormedModule.Pack K phK cT xclass.
Definition completeType := @Complete.Pack cT xclass.
Definition completePseudoMetricType := @CompletePseudoMetric.Pack K cT xclass.
Definition complete_zmodType := @GRing.Zmodule.Pack completeType xclass.
Definition complete_lmodType := @GRing.Lmodule.Pack K phK completeType xclass.
Definition complete_normedZmodType := @Num.NormedZmodule.Pack K phK completeType xclass.
Definition complete_pseudoMetricNormedZmodType :=
  @PseudoMetricNormedZmodule.Pack K phK completeType xclass.
Definition complete_normedModType := @NormedModule.Pack K phK completeType xclass.
Definition completePseudoMetric_lmodType : GRing.Lmodule.type phK :=
  @GRing.Lmodule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_zmodType : GRing.Zmodule.type :=
  @GRing.Zmodule.Pack (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_normedModType : NormedModule.type phK :=
  @NormedModule.Pack K phK (CompletePseudoMetric.sort completePseudoMetricType)
  xclass.
Definition completePseudoMetric_normedZmodType : Num.NormedZmodule.type phK :=
  @Num.NormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass.
Definition completePseudoMetric_pseudoMetricNormedZmodType :
  PseudoMetricNormedZmodule.type phK :=
  @PseudoMetricNormedZmodule.Pack K phK
  (CompletePseudoMetric.sort completePseudoMetricType) xclass.
End ClassDef.

Module Exports.

Coercion base : class_of >-> NormedModule.class_of.
Coercion base2 : class_of >-> CompletePseudoMetric.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> GRing.Zmodule.type.
Canonical zmodType.
Coercion pseudoMetricNormedZmodType : type >-> PseudoMetricNormedZmodule.type.
Canonical pseudoMetricNormedZmodType.
Coercion normedZmodType : type >-> Num.NormedZmodule.type.
Canonical normedZmodType.
Coercion lmodType : type >-> GRing.Lmodule.type.
Canonical lmodType.
Coercion pointedType : type >-> Pointed.type.
Canonical pointedType.
Coercion filteredType : type >-> Filtered.type.
Canonical filteredType.
Coercion topologicalType : type >-> Topological.type.
Canonical topologicalType.
Coercion uniformType : type >-> Uniform.type.
Canonical uniformType.
Coercion pseudoMetricType : type >-> PseudoMetric.type.
Canonical pseudoMetricType.
Coercion normedModType : type >-> NormedModule.type.
Canonical normedModType.
Coercion completeType : type >-> Complete.type.
Canonical completeType.
Coercion completePseudoMetricType : type >-> CompletePseudoMetric.type.
Canonical completePseudoMetricType.
Canonical complete_zmodType.
Canonical complete_lmodType.
Canonical complete_normedZmodType.
Canonical complete_pseudoMetricNormedZmodType.
Canonical complete_normedModType.
Canonical completePseudoMetric_lmodType.
Canonical completePseudoMetric_zmodType.
Canonical completePseudoMetric_normedModType.
Canonical completePseudoMetric_normedZmodType.
Canonical completePseudoMetric_pseudoMetricNormedZmodType.
Notation completeNormedModType K := (type (Phant K)).
Notation "[ 'completeNormedModType' K 'of' T ]" := (@pack _ (Phant K) T _ _ idfun _ _ idfun)
  (at level 0, format "[ 'completeNormedModType'  K  'of'  T ]") : form_scope.
End Exports.

End CompleteNormedModule.

Export CompleteNormedModule.Exports.

(** * Extended Types *)

(** * The topology on real numbers *)

(* TODO: Remove R_complete_lim and use lim instead *)
(* Definition R_lim (F : (R -> Prop) -> Prop) : R := *)
(*   sup (fun x : R => `[<F (ball (x + 1) 1)>]). *)

(* move: (Lub_Rbar_correct (fun x : R => F (ball (x + 1) 1))). *)
(* move Hl : (Lub_Rbar _) => l{Hl}; move: l => [x| |] [Hx1 Hx2]. *)
(* - case: (HF (Num.min 2 eps%:num / 2)%:pos) => z Hz. *)
(*   have H1 : z - Num.min 2 eps%:num / 2 + 1 <= x + 1. *)
(*     rewrite ler_add //; apply/RleP/Hx1. *)
(*     apply: filterS Hz. *)
(*     rewrite /ball /= => u; rewrite /AbsRing_ball absrB ltr_distl. *)
(*     rewrite absrB ltr_distl. *)
(*     case/andP => {Hx1 Hx2 FF HF x F} Bu1 Bu2. *)
(*     have H : Num.min 2 eps%:num <= 2 by rewrite ler_minl lerr. *)
(*     rewrite addrK -addrA Bu1 /= (ltr_le_trans Bu2) //. *)
(*     rewrite -addrA ler_add // -addrA addrC ler_subr_addl. *)
(*     by rewrite ler_add // ler_pdivr_mulr // ?mul1r. *)
(*   have H2 : x + 1 <= z + Num.min 2 eps%:num / 2 + 1. *)
(*     rewrite ler_add //; apply/RleP/(Hx2 (Finite _)) => v Hv. *)
(*     apply: Rbar_not_lt_le => /RltP Hlt. *)
(*     apply: filter_not_empty. *)
(*     apply: filterS (filterI Hz Hv). *)
(*     rewrite /ball /= => w []; rewrite /AbsRing_ball //. *)
(*     rewrite absrB ltr_distl => /andP[_ Hw1]. *)
(*     rewrite absrB ltr_distl addrK => /andP[Hw2 _]. *)
(*     by move: (ltr_trans (ltr_trans Hw1 Hlt) Hw2); rewrite ltrr. *)
(*   apply: filterS Hz. *)
(*   rewrite /ball /= => u; rewrite /AbsRing_ball absrB absRE 2!ltr_distl. *)
(*   case/andP => {Hx1 Hx2 F FF HF} H H0. *)
(*   have H3 : Num.min 2 eps%:num <= eps by rewrite ler_minl lerr orbT. *)
(*   apply/andP; split. *)
(*   - move: H1; rewrite -ler_subr_addr addrK ler_subl_addr => H1. *)
(*     rewrite ltr_subl_addr // (ltr_le_trans H0) //. *)
(*     rewrite -ler_subr_addr (ler_trans H1) //. *)
(*     rewrite -ler_subr_addl -!addrA (addrC x) !addrA subrK. *)
(*     rewrite ler_subr_addr -mulrDl ler_pdivr_mulr //. *)
(*     by rewrite -mulr2n -mulr_natl mulrC ler_pmul. *)
(*   - move: H2; rewrite -ler_subr_addr addrK. *)
(*     move/ler_lt_trans; apply. *)
(*     move: H; rewrite // ltr_subl_addr => H. *)
(*     rewrite -ltr_subr_addr (ltr_le_trans H) //. *)
(*     rewrite addrC -ler_subr_addr -!addrA (addrC u) !addrA subrK. *)
(*     rewrite -ler_subl_addr opprK -mulrDl ler_pdivr_mulr // -mulr2n -mulr_natl. *)
(*     by rewrite mulrC ler_pmul. *)
(* - case (HF 1%:pos) => y Fy. *)
(*   case: (Hx2 (y + 1)) => x Fx. *)
(*   apply: Rbar_not_lt_le => Hlt. *)
(*   apply: filter_not_empty. *)
(*   apply: filterS (filterI Fy Fx) => z [Hz1 Hz2]. *)
(*   apply: Rbar_le_not_lt Hlt;  apply/RleP. *)
(*   rewrite -(ler_add2r (-(y - 1))) opprB !addrA -![in X in _ <= X]addrA. *)
(*   rewrite (addrC y) ![in X in _ <= X]addrA subrK. *)
(*   suff : `|x + 1 - y|%R <= 1 + 1 by rewrite ler_norml => /andP[]. *)
(*   rewrite ltrW // (@subr_trans _ z). *)
(*   by rewrite (ler_lt_trans (ler_norm_add _ _)) // ltr_add // distrC. *)
(* - case: (HF 1%:pos) => y Fy. *)
(*   case: (Hx1 (y - 1)); by rewrite addrAC addrK. *)
(* Qed. *)
(* Admitted. *)

Arguments cvg_distW {_ _ F FF}.

Lemma R_complete (R : realType) (F : set (set R^o)) : ProperFilter F -> cauchy F -> cvg F.
Proof.
move=> FF /cauchy_ballP F_cauchy; apply/cvg_ex.
pose D := \bigcap_(A in F) (down A).
have /cauchy_ballP /cauchyP /(_ 1) [//|x0 x01] := F_cauchy.
have D_has_sup : has_sup D; first split.
- exists (x0 - 1) => A FA.
  near F => x.
  apply/downP; exists x.
  by near: x.
  by rewrite ler_distW 1?distrC 1?ltW ?andbT //; near: x.
- exists (x0 + 1); apply/ubP => x /(_ _ x01) /downP [y].
  rewrite -[ball _ _ _]/(_ (_ < _)) ltr_distl ltr_subl_addr => /andP[/ltW].
  by move=> /(le_trans _) yx01 _ /yx01.
exists (sup D).
apply: (cvg_distW (_ : R^o)) => /= _ /posnumP[eps]; near=> x.
rewrite ler_distl; move/ubP: (sup_upper_bound D_has_sup) => -> //=.
  apply: sup_le_ub => //; first by case: D_has_sup.
  have Fxeps : F (ball_ [eta normr] x (eps)%:num).
    by near: x; apply: nearP_dep; apply: F_cauchy.
  apply/ubP => y /(_ _ Fxeps) /downP[z].
  rewrite /ball_/= ltr_distl ltr_subl_addr.
  by move=> /andP [/ltW /(le_trans _) le_xeps _ /le_xeps].
rewrite /D /= => A FA; near F => y.
apply/downP; exists y.
by near: y.
rewrite ler_subl_addl -ler_subl_addr ltW //.
suff: `|x - y| < eps%:num by rewrite ltr_norml => /andP[_].
by near: y; near: x; apply: nearP_dep; apply: F_cauchy.
Grab Existential Variables. all: end_near. Qed.

Canonical R_completeType (R : realType) := CompleteType R^o (@R_complete R).
(* Canonical R_NormedModule := [normedModType R of R^o]. *)

Canonical R_CompleteNormedModule (R : realType) := [completeNormedModType R of R^o].

Section at_left_right.
Variable R : numFieldType.

Definition at_left (x : R^o) := within (fun u => u < x) (nbhs x).
Definition at_right (x : R^o) := within (fun u : R => x < u) (nbhs x).
(* :TODO: We should have filter notation ^- and ^+ for these *)

Global Instance at_right_proper_filter (x : R^o) : ProperFilter (at_right x).
Proof.
apply: Build_ProperFilter' => -[_/posnumP[d] /(_ (x + d%:num / 2))].
apply; last (by rewrite ltr_addl); rewrite /=.
rewrite opprD !addrA subrr add0r normrN normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.

Global Instance at_left_proper_filter (x : R) : ProperFilter (at_left x).
Proof.
apply: Build_ProperFilter' => -[_ /posnumP[d] /(_ (x - d%:num / 2))].
apply; last (by rewrite ltr_subl_addl ltr_addr); rewrite /=.
rewrite opprD !addrA subrr add0r opprK normf_div !ger0_norm //.
by rewrite ltr_pdivr_mulr // ltr_pmulr // (_ : 1 = 1%:R) // ltr_nat.
Qed.
End at_left_right.

Typeclasses Opaque at_left at_right.


Section TODO_add_to_ssrnum.

Lemma maxr_real (K : realDomainType) (x y : K) :
  x \is Num.real -> y \is Num.real -> maxr x y \is Num.real.
Proof.
by rewrite !realE => /orP[|] x0 /orP[|] y0; rewrite le_maxr le_maxl x0 y0 !(orbT,orTb).
Qed.

Lemma bigmaxr_real (K : realDomainType) (R : choiceType) (x : K) (D : seq R) (f : R -> K):
  x \is Num.real ->
  (forall x, x \in D -> f x \is Num.real) ->
  \big[maxr/x]_(n <- D) f n \is Num.real.
Proof.
move=> ?; elim/big_ind : _ => // *; by [rewrite maxr_real | rewrite num_real].
Qed.

End TODO_add_to_ssrnum.

Section cvg_seq_bounded.
Context {K : numFieldType}.
Local Notation "'+oo'" := (@pinfty_nbhs K).

Lemma cvg_seq_bounded {V : normedModType K} (a : nat -> V) :
  cvg a -> bounded_fun a.
Proof.
move=> /cvg_bounded/ex_bound => -[/= Moo]; rewrite !near_simpl/=.
rewrite [(\near a, _ <= _)](near_map _ \oo) => -[N _ /(_ _) a_leM].
have Moo_real : Moo \is Num.real
  by rewrite ger0_real ?(le_trans _ (a_leM N _))/=.
rewrite /bounded_on /=; near=> M => n _.
have [nN|nN]/= := leqP N n.
  by apply: (le_trans (a_leM _ _)) => //; near: M; apply: nbhs_pinfty_ge_real.
move: n nN; suff /(_ (Ordinal _)) : forall n : 'I_N, `|a n| <= M by [].
by near: M; apply: filter_forall => i; apply: nbhs_pinfty_ge_real.
Grab Existential Variables. all: end_near. Qed.

End cvg_seq_bounded.

Lemma closure_sup (R : realType) (A : set R^o) : A !=set0 -> has_ubound A ->
  (closure A) (sup A).
Proof.
move=> A0 ?; have [|AsupA] := pselect (A (sup A)); first exact: subset_closure.
rewrite closure_limit_point; right => U /nbhs_ballP[_ /posnumP[e]] supAeU.
have [x [Ax /andP[sAex xsA]]] : exists x, A x /\ sup A - e%:num < x < sup A.
  apply: contrapT => /forallNP Ax.
  have /(sup_le_ub A0) : ubound A (sup A - e%:num).
    move=> y Ay; have /not_andP[//|/negP] := Ax y.
    rewrite negb_and -leNgt => /orP[//|sAy]; rewrite leNgt.
    apply: contra sAy => sAey; rewrite lt_neqAle sup_upper_bound // andbT.
    by apply/eqP; apply: contra_not AsupA => <-.
  by rewrite leNgt => /negP; apply; rewrite ltr_subl_addl ltr_addr.
exists x; split => //; first by rewrite lt_eqF.
apply supAeU; rewrite /ball /= ltr_distl (addrC x e%:num) -ltr_subl_addl sAex.
by rewrite andbT (le_lt_trans _ xsA) // ler_subl_addl ler_addr.
Qed.

Lemma near_infty_natSinv_lt (R : archiFieldType) (z : R) (e : {posnum R}) :
  \forall n \near \oo, n.+1%:R^-1 < e%:num.
Proof.
near=> n; rewrite -(@ltr_pmul2r _ n.+1%:R) // mulVr ?unitfE //.
rewrite -(@ltr_pmul2l _ e%:num^-1) // mulr1 mulrA mulVr ?unitfE // mul1r.
rewrite (lt_trans (archi_boundP _)) // ltr_nat.
by near: n; exists (Num.bound e%:num^-1).
Grab Existential Variables. all: end_near. Qed.

Lemma limit_pointP (T : archiFieldType) (A : set T^o) (x : T) :
  limit_point A x <-> exists a_ : nat -> T^o,
    [/\ a_ @` setT `<=` A, forall n, a_ n != x & a_ --> (x:T^o)].
Proof.
split=> [Ax|[a_ [aTA a_x] ax]]; last first.
  move=> U /ax[m _ a_U]; near \oo => n; exists (a_ n); split => //.
  by apply aTA; exists n.
  by apply a_U; near: n; exists m.
pose U := fun n : nat => [set z : T^o | `|x - z| < n.+1%:R^-1].
suff [a_ anx] : exists a_, forall n, a_ n != x /\ (U n `&` A) (a_ n).
  exists a_; split.
  - by move=> a [n _ <-]; have [? []] := anx n.
  - by move=> n; have [] := anx n.
  - apply/cvg_distP; first by exact: fmap_filter.
    move=> _/posnumP[e]; rewrite near_map; near=> n.
    have [? [] xann Aan] := anx n.
    by rewrite (lt_le_trans xann) // ltW //; near: n; exact: near_infty_natSinv_lt.
have @a_ : nat -> T^o.
  move=> n; have : nbhs (x : T^o) (U n).
    by apply/(nbhs_ballP (x:T^o) (U n)); rewrite nbhs_ballE; exists n.+1%:R^-1.
  by move/Ax/cid => [/= an [anx Aan Uan]]; exact: an.
by exists a_ => n; rewrite /a_ /= /ssr_have; case: cid => ? [].
Grab Existential Variables. all: end_near. Qed.

Section open_closed_sets_numField.
Variable R : numFieldType.
Implicit Types y : R.

Lemma closed_eq y : closed [set x : R^o | x = y].
Proof.
  by apply: compact_closed => //=; apply: compact1.
Qed.

Lemma open_neq y : open [set x : R^o | x != y].
Proof.
  suff ->: [set x | x != y] = (~`[set y]) by apply: openC; apply: closed_eq.
  rewrite eqEsubset; split => z /=; rewrite /set1 /setC /=.
  all: by move=>/eqP.
Qed.

Let Rtop := [topologicalType of R^o].

Lemma normr_closure {V : normedModType R} (D : set V) : 
  @closure Rtop ([eta normr] @` D) `<=` [set x : R^o | 0 <= x].
Proof.
  case emptyD: `[<D = set0>]. {
    move: emptyD => /asboolP -> /=. 
    by rewrite image_set0 closure0.
  }
  move: emptyD => /asboolP /eqP /set0P [d dD].
  move=> r /=; rewrite closureEcluster.
  rewrite (@cluster_cvgE Rtop (globally ([eta normr] @` D)) _).
    2: by apply: (globally_properfilter (a := `|d|)); exists d.
  case=> F ? [F_to_r DsubF].
  have normF: F `=>` [eta normr] @ F. {
    move => P /=; rewrite /nbhs /= => FnP.
    have: (F ([set a | P `|a|] `&` [eta normr] @` D)).
      apply: filterI => //=.
      by apply: DsubF.
    apply: filterS => x [/= nX [y nDy]] Q.
    suff <- : (`|x| = x) by [].
    apply: (eq_trans _ Q).
    rewrite -[RHS]normr_id; symmetry.
    by congr (`| _|).
  }
  have ?: (F --> (`|r| : R^o)). {
    apply: (cvg_trans normF); apply: continuous_cvg => //=.
    by apply: norm_continuous.
  }
  have ?: (`|r| = r). {
    by apply: (@close_eq Rtop) => //=; apply: (@cvg_close _ F).
  }
  by rewrite ger0_def; apply/eqP.
Qed.

Lemma closed_ge_0 : 
  closed [set x : R^o | 0 <= x].
Proof.
  suff W: (([eta normr] @` (@setT Rtop)) = [set x | 0 <= x] ).
    apply/ closure_id; rewrite eqEsubset; split.
    - by apply: subset_closure.
    - by rewrite -{1}W; apply: normr_closure.
  rewrite eqEsubset; split.
    - by move => x /= [y _ <-]; apply normr_ge0.
    - move=> x /=; rewrite ger0_def.
      by move=> /eqP <-; exists x.
Qed.

Lemma closed_ge y: closed [set x : R^o | y <= x].
Proof.
  have <-: ((fun x => x - y) @^-1` [set x | 0 <= x]  = [set x | y <= x] )
    by (rewrite eqEsubset; split => z /=; rewrite subr_ge0).
  apply: (@closed_comp Rtop Rtop) => /=.
  2: by apply closed_ge_0.
  move => ? ?; apply: continuousD => //=.
  by apply: cvg_cst.
Qed.

Lemma closed_le y: closed [set x : R^o | x <= y].
Proof.
  have <-: ((fun x => -x) @^-1` [set x | -y <= x]  = [set x | x <= y] ).
    by (rewrite eqEsubset; split => z /=; rewrite ler_oppr opprK).
  apply: (@closed_comp Rtop Rtop) => /=.
  2: by apply closed_ge.
  by move => ? ?; apply: continuousN => //=.
Qed.
    
End open_closed_sets_numField.

Section open_closed_sets_realField.
Variable R : realFieldType.
Implicit Types y : R.
Lemma open_lt y : open [set x : R^o | x < y].
Proof.
move=> x /=; rewrite -subr_gt0 => yDx_gt0; exists (y - x) => // z.
by rewrite /= distrC ltr_distl addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_lt : core.

Lemma open_gt y : open [set x : R^o | x > y].
Proof.
move=> x /=; rewrite -subr_gt0 => xDy_gt0; exists (x - y) => // z.
by rewrite /= distrC ltr_distl opprB addrCA subrr addr0 => /andP[].
Qed.
Hint Resolve open_gt : core.


(* TODO: move after rebase on mathcomp 1.12?  *)
Definition isBOpen (b : itv_bound R) :=
  if b is BOpen _ then true else false.

Definition isBClosed (b : itv_bound R) :=
  if b is BOpen_if false _ then true else false.

Lemma interval_open a b : ~~ isBClosed a -> ~~ isBClosed b ->
  open [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]//a|] [[]//b|] _ _.
- have -> : [set x | a < x < b] = [set x | a < x] `&` [set x | x < b].
    by rewrite predeqE => r; rewrite /mkset; split => [/andP[? ?] //|[-> ->]].
  by apply openI; [exact: open_gt | exact: open_lt].
- rewrite (_ : [set x | x \in _] = [set x : R^o | x > a]) //.
  by rewrite predeqE => r; split => //; rewrite /mkset ?(inE,lersifT,andbT).
- exact: open_lt.
- by rewrite (_ : mkset _ = setT); [exact: openT | rewrite predeqE].
Qed.

Lemma interval_closed a b : ~~ isBOpen a -> ~~ isBOpen b ->
  closed [set x : R^o | x \in Interval a b].
Proof.
move: a b => [[]//a|] [[]//b|] _ _.
- have -> : [set x | x \in `[a, b]] = [set x | x >= a] `&` [set x | x <= b].
    by rewrite predeqE => ?; rewrite /= inE; split=> [/andP [] | /= [->]].
  by apply closedI; [exact: closed_ge | exact: closed_le].
- rewrite (_ : mkset _ = [set x : R^o | x >= a]); first exact :closed_ge.
  by rewrite predeqE => r; split => //; rewrite /mkset ?(inE,lersifT,andbT).
- exact: closed_le.
- by rewrite (_ : mkset _ = setT); [exact: closedT|rewrite predeqE].
Qed.

End open_closed_sets_realField.

Hint Extern 0 (open _) => now apply: open_gt : core.
Hint Extern 0 (open _) => now apply: open_lt : core.
Hint Extern 0 (open _) => now apply: open_neq : core.
Hint Extern 0 (closed _) => now apply: closed_ge : core.
Hint Extern 0 (closed _) => now apply: closed_le : core.
Hint Extern 0 (closed _) => now apply: closed_eq : core.

Section closure_left_right_open.
Variable R : archiFieldType.
Implicit Types z : R.

Lemma closure_gt z : closure ([set x | z < x] : set R^o) = [set x | z <= x].
Proof.
rewrite predeqE => v; split.
  by rewrite closureE; apply; split => [|W /ltW //]; exact: closed_ge.
rewrite /mkset le_eqVlt => /orP[/eqP <-{v}|]; last first.
  by move=> ?; exact: subset_closure.
apply/subset_limit_point/limit_pointP; exists (fun n => z + n.+1%:R^-1); split.
- by move=> u [] m _ <-; rewrite ltr_addl.
- by move=> n; rewrite -subr_eq0 addrAC subrr add0r.
- apply/cvg_distP; first exact: fmap_filter.
  move=> _/posnumP[e]; rewrite near_map; near=> n.
  rewrite opprD addrA subrr add0r normrN ger0_norm //.
  by near: n; exact: near_infty_natSinv_lt.
Grab Existential Variables. all: end_near. Qed.

Lemma closure_lt z : closure ([set x : R^o | x < z]) = [set x | x <= z].
Proof.
rewrite predeqE => v; split.
  by rewrite closureE; apply; split => [|w /ltW //]; exact: closed_le.
rewrite /mkset le_eqVlt => /orP[/eqP <-{z}|]; last first.
  by move=> ?; exact: subset_closure.
apply/subset_limit_point/limit_pointP; exists (fun n => v - n.+1%:R^-1); split.
- by move=> u [] m _ <-; rewrite ltr_subl_addl ltr_addr.
- by move=> n; rewrite -subr_eq0 addrAC subrr add0r oppr_eq0.
- apply/cvg_distP; first exact: fmap_filter.
  move=> _/posnumP[e]; rewrite near_map; near=> n.
  rewrite opprD addrA subrr add0r opprK ger0_norm //.
  by near: n; exact: near_infty_natSinv_lt.
Grab Existential Variables. all: end_near. Qed.

End closure_left_right_open.

Section interval.
Variable R : numDomainType.

Definition is_interval (E : set R) :=
  forall x y, E x -> E y -> forall z, x < z < y -> E z.

Lemma is_intervalPle (E : set R) :
  is_interval E <-> forall x y, E x -> E y -> forall z, x <= z <= y -> E z.
Proof.
split=> iE x y Ex Ey z /andP[].
  rewrite le_eqVlt => /orP[/eqP <-//|xz]; rewrite le_eqVlt => /orP[/eqP ->//|?].
  by apply (iE _ _ Ex Ey); rewrite xz.
by move=> xz zy; apply (iE _ _ Ex Ey); rewrite (ltW xz) (ltW zy).
Qed.

Lemma interval_is_interval (i : interval R) : is_interval [set x | x \in i].
Proof.
move: i => [[[] i|] [[] j|]] //= x y; rewrite /mkset !(inE,lersifT,lersifF);
  move=> /andP[ax ?] /andP[? yb] z /andP[? ?]; rewrite !(inE,lersifT,lersifF).
by rewrite (lt_trans ax) // (lt_trans _ yb).
by rewrite (lt_trans ax) // (le_trans (ltW _) yb).
by rewrite (lt_trans ax).
by rewrite (le_trans ax (ltW _)) // (lt_trans _ yb).
by rewrite (le_trans ax (ltW _)) // (le_trans (ltW _) yb).
by rewrite (le_trans ax (ltW _)).
by rewrite (lt_trans _ yb).
by rewrite (le_trans (ltW _) yb).
Qed.

End interval.

Lemma right_bounded_interior (R : realType) (X : set R^o) :
  has_ubound X -> X^° `<=` [set r | r < sup X].
Proof.
move=> uX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP supXr|]; last first.
  by apply/negP; rewrite -leNgt sup_ub //; exact: interior_subset.
suff : ~ X^° (sup X) by rewrite supXr.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (sup X + f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprD addrA subrr.
  by rewrite sub0r normrN gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : sup X + f%:num <= sup X by apply sup_ub.
by apply/negP; rewrite -ltNge; rewrite ltr_addl.
Qed.

Lemma left_bounded_interior (R : realType) (X : set R^o) :
  has_lbound X -> X^° `<=` [set r | inf X < r].
Proof.
move=> lX r Xr; rewrite /mkset ltNge; apply/negP.
rewrite le_eqVlt => /orP[/eqP rinfX|]; last first.
  by apply/negP; rewrite -leNgt inf_lb //; exact: interior_subset.
suff : ~ X^° (inf X) by rewrite -rinfX.
case/nbhs_ballP => _/posnumP[e] supXeX.
have [f XsupXf] : exists f : {posnum R}, X (inf X - f%:num).
  exists (e%:num / 2)%:pos; apply supXeX; rewrite /ball /= opprB addrCA subrr.
  by rewrite addr0 gtr0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
have : inf X <= inf X - f%:num by apply inf_lb.
by apply/negP; rewrite -ltNge; rewrite ltr_subl_addr ltr_addl.
Qed.

(* TODO: move to reals.v? *)
Lemma inf_lb_strict (R : realType) (X : set R) : has_lbound X ->
  ~ X (inf X) -> X `<=` [set r | inf X < r].
Proof.
move=> lX XinfX r Xr; rewrite /mkset lt_neqAle inf_lb // andbT.
by apply/negP => /eqP infXr; move: XinfX; rewrite infXr.
Qed.

Lemma sup_ub_strict (R : realType) (X : set R) : has_ubound X ->
  ~ X (sup X) -> X `<=` [set r | r < sup X].
Proof.
move=> ubX XsupX r Xr; rewrite /mkset lt_neqAle sup_ub // andbT.
by apply/negP => /eqP supXr; move: XsupX; rewrite -supXr.
Qed.

Section interval_realType.
Variable R : realType.

Lemma interval_unbounded_setT (X : set R) : is_interval X ->
  ~ has_lbound X -> ~ has_ubound X -> X = setT.
Proof.
move=> iX lX uX; rewrite predeqE => x; split => // _.
move/has_lbPn : lX => /(_ x) [y Xy xy].
move/has_ubPn : uX => /(_ x) [z Xz xz].
by apply: (iX _ _ Xy Xz); rewrite xy xz.
Qed.

Lemma interval_left_unbounded_interior (X : set R^o) : is_interval X ->
  ~ has_lbound X -> has_ubound X -> X^° = [set r | r < sup X].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: right_bounded_interior.
rewrite -(open_subsetE _ (@open_lt _ _)) => r rsupX.
move/has_lbPn : lX => /(_ r)[y Xy yr].
have hsX : has_sup X by split => //; exists y.
have /(sup_adherent hsX)[e Xe] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => re; apply (iX _ _ Xy Xe); rewrite yr re.
Qed.

Lemma interval_right_unbounded_interior (X : set R^o) : is_interval X ->
  has_lbound X -> ~ has_ubound X -> X^° = [set r | inf X < r].
Proof.
move=> iX lX uX; rewrite eqEsubset; split; first exact: left_bounded_interior.
rewrite -(open_subsetE _ (@open_gt _ _)) => r infXr.
move/has_ubPn : uX => /(_ r)[y Xy yr].
have hiX : has_inf X by split => //; exists y.
have /(inf_adherent hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
by rewrite addrCA subrr addr0 => er; apply: (iX _ _ Xe Xy); rewrite yr er.
Qed.

Lemma interval_bounded_interior (X : set R^o) : is_interval X ->
  has_lbound X -> has_ubound X -> X^° = [set r | inf X < r < sup X].
Proof.
move=> iX bX aX; rewrite eqEsubset; split=> [r Xr|].
  apply/andP; split;
    [exact: left_bounded_interior|exact: right_bounded_interior].
rewrite -open_subsetE; last exact: (@interval_open _ (BOpen _) (BOpen _)).
move=> r /andP[iXr rsX].
have [/set0P X0|/negPn/eqP X0] := boolP (X != set0); last first.
  by move: (lt_trans iXr rsX); rewrite X0 inf_out ?sup_out ?ltxx // => - [[]].
have hiX : has_inf X by split.
have /(inf_adherent hiX)[e Xe] : 0 < r - inf X by rewrite subr_gt0.
rewrite addrCA subrr addr0 => er.
have hsX : has_sup X by split.
have /(sup_adherent hsX)[f Xf] : 0 < sup X - r by rewrite subr_gt0.
by rewrite opprB addrCA subrr addr0 => rf; apply: (iX _ _ Xe Xf); rewrite er rf.
Qed.

Definition Rhull (X : set R) : interval R := Interval
  (if `[< has_lbound X >] then BOpen_if (~~ `[< X (inf X) >]) (inf X)
                          else BInfty _)
  (if `[< has_ubound X >] then BOpen_if (~~ `[< X (sup X) >]) (sup X)
                          else BInfty _).

Lemma sub_Rhull (X : set R) : X `<=` [set x | x \in Rhull X].
Proof.
move=> x Xx/=; rewrite inE/=.
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
+ by case: asboolP => ?; case: asboolP => ? //=;
     rewrite !(lersifF, lersifT, sup_ub, inf_lb, sup_ub_strict, inf_lb_strict).
+ by case: asboolP => XinfX; rewrite !(lersifF, lersifT);
     [rewrite inf_lb | rewrite inf_lb_strict].
+ by case: asboolP => XsupX; rewrite !(lersifF, lersifT);
     [rewrite sup_ub | rewrite sup_ub_strict].
Qed.


Lemma is_intervalP (X : set R) : is_interval X <-> X = [set x | x \in Rhull X].
Proof.
split=> [iX|->]; last exact: interval_is_interval.
rewrite predeqE => x /=; split; [exact: sub_Rhull | rewrite inE/=].
case: (asboolP (has_lbound _)) => ?; case: (asboolP (has_ubound _)) => ? //=.
- case: asboolP => XinfX; case: asboolP => XsupX;
    rewrite !(lersifF, lersifT).
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx].
    rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[]; rewrite le_eqVlt => /orP[/eqP <- //|infXx supXx].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> /andP[infXx]; rewrite le_eqVlt => /orP[/eqP -> //|xsupX].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior // /mkset infXx.
  + move=> ?; apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_bounded_interior // /mkset infXx.
- case: asboolP => XinfX; rewrite !(lersifF, lersifT, andbT).
  + rewrite le_eqVlt => /orP[/eqP<-//|infXx].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_right_unbounded_interior.
  + move=> infXx; apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_right_unbounded_interior.
- case: asboolP => XsupX /=.
  + rewrite le_eqVlt => /orP[/eqP->//|xsupX].
    apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_left_unbounded_interior.
  + move=> xsupX; apply: (@interior_subset [topologicalType of R^o]).
    by rewrite interval_left_unbounded_interior.
- by move=> _; rewrite (interval_unbounded_setT iX).
Qed.

Lemma connected_intervalP (E : set R^o) : connected E <-> is_interval E.
Proof.
split => [cE x y Ex Ey z /andP[xz zy]|].
- apply: contrapT => Ez.
  pose Az := E `&` [set x | x < z]; pose Bz := E `&` [set x | z < x].
  apply/connectedPn : cE; exists (fun b => if b then Az else Bz); split.
  + by case; [exists x | exists y].
  + rewrite /Az /Bz -setIUr; apply/esym/setIidPl => u Eu.
    by apply/orP; rewrite -neq_lt; apply/negP; apply: contraPnot Eu => /eqP <-.
  + split; [|rewrite setIC].
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_gt => zu.
      by rewrite /Az setCI; right; apply/negP; rewrite -leNgt.
    + apply/disjoints_subset => /= u /closureI[_]; rewrite closure_lt => zu.
      by rewrite /Bz setCI; right; apply/negP; rewrite -leNgt.
- apply: contraPP => /connectedPn[A [A0 EU sepA]] intE.
  have [/= x A0x] := A0 false; have [/= y A1y] := A0 true.
  wlog xy : A A0 EU sepA x A0x y A1y / x < y.
    move=> /= wlog_hypo; have [xy|yx|{wlog_hypo}yx] := ltgtP x y.
    + exact: (wlog_hypo _ _ _ _ _ A0x _ A1y).
    + apply: (wlog_hypo (A \o negb) _ _ _ y _ x) => //=;
      by [rewrite setUC | rewrite separatedC].
    + move/separated_disjoint : sepA; rewrite predeqE => /(_ x)[] + _; apply.
      by split => //; rewrite yx.
  pose z := sup (A false `&` [set z | x <= z <= y]).
  have A1z : ~ (A true) z.
    have cA0z : closure (A false) z.
      suff : closure (A false `&` [set z | x <= z <= y]) z by case/closureI.
      apply: closure_sup; last by exists y => u [_] /andP[].
      by exists x; split => //; rewrite /mkset lexx /= (ltW xy).
    by move: sepA; rewrite /separated => -[] /disjoints_subset + _; apply.
  have /andP[xz zy] : x <= z < y.
    rewrite sup_ub //=; [|by exists y => u [_] /andP[]|].
    + rewrite lt_neqAle sup_le_ub ?andbT; last by move=> u [_] /andP[].
      * by apply/negP; apply: contraPnot A1y => /eqP <-.
      * by exists x; split => //; rewrite /mkset /= lexx /= (ltW xy).
    + by split=> //; rewrite /mkset lexx (ltW xy).
  have [A0z|A0z] := pselect ((A false) z); last first.
    have {}xzy : x < z < y.
      by rewrite zy lt_neqAle xz !andbT; apply/eqP; apply: contra_not A0z => <-.
    have : ~ E z by rewrite EU => -[].
    by apply; apply (intE x y) => //; rewrite EU; [left|right].
  suff [z1 [/andP[zz1 z1y] Ez1]] : exists z1 : R, z < z1 < y /\ ~ E z1.
    apply Ez1; apply (intE x y) => //; rewrite ?EU; [by left|by right|].
    by rewrite z1y (le_lt_trans _ zz1).
  have [r zcA1] : {r:{posnum R}| ball (z:R^o) r%:num `<=` ~` closure (A true)}.
    have ? : ~ closure (A true) z.
      by move: sepA; rewrite /separated => -[] _ /disjoints_subset; apply.
    have ? : open (~` closure (A true)) by exact/openC/closed_closure.
    exact/nbhsC_ball/open_nbhs_nbhs.
  pose z1 : R := z + r%:num / 2; exists z1.
  have z1y : z1 < y.
    rewrite ltNge; apply/negP => yz1.
    suff : (~` closure (A true)) y by apply; exact: subset_closure.
    apply zcA1; rewrite /ball /= ltr_distl (lt_le_trans zy) // ?ler_addl //.
    rewrite andbT ltr_subl_addl addrC (le_lt_trans yz1) // ltr_add2l.
    by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  rewrite z1y andbT ltr_addl; split => //.
  have ncA1z1 : (~` closure (A true)) z1.
    apply zcA1; rewrite /ball /= /z1 opprD addrA subrr add0r normrN.
    by rewrite ger0_norm // ltr_pdivr_mulr // ltr_pmulr // ltr1n.
  have nA0z1 : ~ (A false) z1.
    move=> A0z1; have : z < z1 by rewrite /z1 ltr_addl.
    apply/negP; rewrite -leNgt; apply sup_ub; first by exists y => u [_] /andP[].
    by split => //; rewrite /mkset /z1 (le_trans xz) /= ?ler_addl // (ltW z1y).
  by rewrite EU => -[//|]; apply: contra_not ncA1z1; exact: subset_closure.
Qed.
End interval_realType.


Section segment.
Variable R : realType.

(** properties of segments in [R] *)

Lemma segment_connected (a b : R) : connected [set x : R^o | x \in `[a, b]].
Proof. exact/connected_intervalP/interval_is_interval. Qed.

Lemma segment_compact (a b : R) : compact [set x : R^o | x \in `[a, b]].
Proof.
case: (lerP a b) => [leab|ltba]; last first.
  by move=> F FF /filter_ex [x abx]; move: ltba; rewrite (itvP abx).
rewrite compact_cover => I D f fop sabUf.
set B := [set x | exists2 D' : {fset I}, {subset D' <= D} &
  [set y | y \in `[a, x]] `<=` \bigcup_(i in [set i | i \in D']) f i /\
  (\bigcup_(i in [set i | i \in D']) f i) x].
set A := [set x | x \in `[a, b]] `&` B.
suff Aeab : A = [set x | x \in `[a, b]].
  suff [_ [D' ? []]] : A b by exists D'.
  by rewrite Aeab/= inE/=; apply/andP.
apply: segment_connected.
- have aba : a \in `[a, b] by rewrite inE/=; apply/andP.
  exists a; split=> //; have /sabUf [i /= Di fia] := aba.
  exists [fset i]%fset; first by move=> ?; rewrite inE inE => /eqP->.
  split; last by exists i => //=; rewrite inE.
  move=> x /= aex; exists i; [by rewrite /= inE|suff /eqP-> : x == a by []].
  by rewrite eq_le !(itvP aex).
- exists B => //; rewrite openE => x [D' sD [saxUf [i Di fx]]].
  have : open (f i) by have /sD := Di; rewrite inE => /fop.
  rewrite openE => /(_ _ fx) [e egt0 xe_fi]; exists e => // y xe_y.
  exists D' => //; split; last by exists i => //; apply/xe_fi.
  move=> z /= ayz; case: (lerP z x) => [lezx|ltxz].
    by apply/saxUf; rewrite /= inE/= (itvP ayz) lezx.
  exists i => //; apply/xe_fi; rewrite /ball_/= distrC ger0_norm.
    have lezy : z <= y by rewrite (itvP ayz).
    rewrite ltr_subl_addl; apply: le_lt_trans lezy _; rewrite -ltr_subl_addr.
    by have := xe_y; rewrite /ball_ => /ltr_distW.
  by rewrite subr_ge0; apply/ltW.
exists A; last by rewrite predeqE => x; split=> [[] | []].
move=> x clAx; have abx : x \in `[a, b].
  by apply: interval_closed; have /closureI [] := clAx.
split=> //; have /sabUf [i Di fx] := abx.
have /fop := Di; rewrite openE => /(_ _ fx) [_ /posnumP[e] xe_fi].
have /clAx [y [[aby [D' sD [sayUf _]]] xe_y]] := nbhsx_ballx x e.
exists (i |` D')%fset; first by move=> j /fset1UP[->|/sD] //; rewrite inE.
split=> [z axz|]; last first.
  exists i; first by rewrite /= !inE eq_refl.
  by apply/xe_fi; rewrite /ball_/= subrr normr0.
case: (lerP z y) => [lezy|ltyz].
  have /sayUf [j Dj fjz] : z \in `[a, y] by rewrite inE/= (itvP axz) lezy.
  by exists j => //=; rewrite inE orbC Dj.
exists i; first by rewrite /= !inE eq_refl.
apply/xe_fi; rewrite /ball_/= ger0_norm; last first.
  by rewrite subr_ge0 (itvP axz).
rewrite ltr_subl_addl -ltr_subl_addr; apply: lt_trans ltyz.
by apply: ltr_distW; rewrite distrC.
Qed.

End segment.

Lemma ler0_addgt0P (R : numFieldType) (x : R) :
  reflect (forall e, e > 0 -> x <= e) (x <= 0).
Proof.
apply: (iffP idP) => [lex0 e egt0|lex0]; first by rewrite (le_trans lex0)// ltW.
have [|//|x0] := comparable_leP.
  by rewrite (@comparabler_trans _ 1)// /Order.comparable ?lex0// ler01 orbT.
have : x <= x / 2 by rewrite lex0// divr_gt0.
rewrite {1}(splitr x) ger_addl pmulr_lle0 // => /(lt_le_trans x0);
  by rewrite ltxx.
Qed.

Lemma IVT (R : realType) (f : R^o -> R^o) (a b v : R^o) :
  a <= b -> {in `[a, b], continuous f} ->
  minr (f a) (f b) <= v <= maxr (f a) (f b) ->
  exists2 c, c \in `[a, b] & f c = v.
Proof.
move=> leab fcont; gen have ivt : f v fcont / f a <= v <= f b ->
    exists2 c, c \in `[a, b] & f c = v; last first.
  case: (leP (f a) (f b)) => [] _ fabv; first exact: ivt.
  have [||c cab /oppr_inj] := ivt (- f) (- v); last by exists c.
    by move=> x /fcont; apply: (@continuousN _ [normedModType R of R^o]).
  by rewrite ler_oppr opprK ler_oppr opprK andbC.
move=> /andP[]; rewrite le_eqVlt => /orP [/eqP<- _|ltfav].
  by exists a => //; rewrite inE/= lexx leab.
rewrite le_eqVlt => /orP [/eqP->|ltvfb].
  by exists b => //; rewrite inE/= lexx leab.
set A := [set c | (c <= b) && (f c <= v)].
have An0 : nonempty A by exists a; apply/andP; split=> //; apply: ltW.
have supA : has_sup A by split=> //; exists b; apply/ubP => ? /andP [].
have supAab : sup A \in `[a, b].
  rewrite inE; apply/andP; split; last first.
    by apply: sup_le_ub => //; apply/ubP => ? /andP [].
  by move/ubP : (sup_upper_bound supA); apply; rewrite /A/= leab andTb ltW.
exists (sup A) => //; have lefsupv : f (sup A) <= v.
  rewrite leNgt; apply/negP => ltvfsup.
  have vltfsup : 0 < f (sup A) - v by rewrite subr_gt0.
  have /fcont /(_ _ (@nbhsx_ballx _ [normedModType R of R^o] _ (PosNum vltfsup))) [_/posnumP[d] supdfe]
    := supAab.
  have [t At supd_t] := sup_adherent supA [gt0 of d%:num].
  suff /supdfe : @ball _ [normedModType R of R^o] (sup A) d%:num t.
    rewrite /= /ball /= ltr_norml => /andP [_].
    by rewrite ltr_add2l ltr_oppr opprK ltNge; have /andP [_ ->] := At.
  rewrite /= /ball /= ger0_norm.
    by rewrite ltr_subl_addr -ltr_subl_addl.
  by rewrite subr_ge0; move/ubP : (sup_upper_bound supA); exact.
apply/eqP; rewrite eq_le; apply/andP; split=> //.
rewrite -subr_le0; apply/ler0_addgt0P => _/posnumP[e].
rewrite ler_subl_addr -ler_subl_addl ltW //.
have /fcont /(_ _ (@nbhsx_ballx _ [normedModType R of R^o] _ e)) [_/posnumP[d] supdfe] := supAab.
have atrF := at_right_proper_filter (sup A); near (at_right (sup A)) => x.
have /supdfe /= : @ball _ [normedModType R of R^o] (sup A) d%:num x.
  by near: x; rewrite /= nbhs_simpl; exists d%:num => //.
rewrite /= => /ltr_distW; apply: le_lt_trans.
rewrite ler_add2r ltW //; suff : forall t, t \in `](sup A), b] -> v < f t.
  apply; rewrite inE; apply/andP; split; first by near: x; exists 1.
  near: x; exists (b - sup A) => /=.
    rewrite subr_gt0 lt_def (itvP supAab) andbT; apply/negP => /eqP besup.
    by move: lefsupv; rewrite leNgt -besup ltvfb.
  move=> t lttb ltsupt; move: lttb; rewrite /= distrC.
  by rewrite gtr0_norm ?subr_gt0 // ltr_add2r; apply: ltW.
move=> t /andP [ltsupt /= letb]; rewrite ltNge; apply/negP => leftv.
move: ltsupt => /=; rewrite ltNge => /negP; apply.
by move/ubP : (sup_upper_bound supA); apply; rewrite /A/= leftv letb.
Grab Existential Variables. all: end_near. Qed.

(** Local properties in [R] *)

(** * Topology on [R]² *)

(* Lemma locally_2d_align : *)
(*   forall (P Q : R -> R -> Prop) x y, *)
(*   ( forall eps : {posnum R}, (forall uv, ball (x, y) eps uv -> P uv.1 uv.2) -> *)
(*     forall uv, ball (x, y) eps uv -> Q uv.1 uv.2 ) -> *)
(*   {near x & y, forall x y, P x y} ->  *)
(*   {near x & y, forall x y, Q x y}. *)
(* Proof. *)
(* move=> P Q x y /= K => /locallyP [d _ H]. *)
(* apply/locallyP; exists d => // uv Huv. *)
(* by apply (K d) => //. *)
(* Qed. *)

(* Lemma locally_2d_1d_const_x : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally y (fun t => P x t). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* exists d => // z Hz. *)
(* by apply (Hd (x, z)). *)
(* Qed. *)

(* Lemma locally_2d_1d_const_y : *)
(*   forall (P : R -> R -> Prop) x y, *)
(*   locally_2d x y P -> *)
(*   locally x (fun t => P t y). *)
(* Proof. *)
(* move=> P x y /locallyP [d _ Hd]. *)
(* apply/locallyP; exists d => // z Hz. *)
(* by apply (Hd (z, y)). *)
(* Qed. *)

(* Lemma locally_2d_1d_strong (P : R -> R -> Prop) (x y : R): *)
(*   (\near x & y, P x y) -> *)
(*   \forall u \near x & v \near y, *)
(*       forall (t : R), 0 <= t <= 1 -> *)
(*       \forall z \near t, \forall a \near (x + z * (u - x)) *)
(*                                & b \near (y + z * (v - y)), P a b. *)
(* Proof. *)
(* move=> P x y. *)
(* apply locally_2d_align => eps HP uv Huv t Ht. *)
(* set u := uv.1. set v := uv.2. *)
(* have Zm : 0 <= Num.max `|u - x| `|v - y| by rewrite ler_maxr 2!normr_ge0. *)
(* rewrite ler_eqVlt in Zm. *)
(* case/orP : Zm => Zm. *)
(* - apply filterE => z. *)
(*   apply/locallyP. *)
(*   exists eps => // pq. *)
(*   rewrite !(RminusE,RmultE,RplusE). *)
(*   move: (Zm). *)
(*   have : Num.max `|u - x| `|v - y| <= 0 by rewrite -(eqP Zm). *)
(*   rewrite ler_maxl => /andP[H1 H2] _. *)
(*   rewrite (_ : u - x = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite (_ : v - y = 0); last by apply/eqP; rewrite -normr_le0. *)
(*   rewrite !(mulr0,addr0); by apply HP. *)
(* - have : Num.max (`|u - x|) (`|v - y|) < eps. *)
(*     rewrite ltr_maxl; apply/andP; split. *)
(*     - case: Huv => /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*     - case: Huv => _ /sub_ball_abs /=; by rewrite mul1r absrB. *)
(*   rewrite -subr_gt0 => /RltP H1. *)
(*   set d1 := mk{posnum R} _ H1. *)
(*   have /RltP H2 : 0 < pos d1 / 2 / Num.max `|u - x| `|v - y| *)
(*     by rewrite mulr_gt0 // invr_gt0. *)
(*   set d2 := mk{posnum R} _ H2. *)
(*   exists d2 => // z Hz. *)
(*   apply/locallyP. *)
(*   exists [{posnum R} of d1 / 2] => //= pq Hpq. *)
(*   set p := pq.1. set q := pq.2. *)
(*   apply HP; split. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : p - x = p - (x + z * (u - x)) + (z - t + t) * (u - x)); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hp) // (ler_trans (absrM _ _)) //. *)
(*     apply (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)). *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(*   + apply/sub_abs_ball => /=. *)
(*     rewrite absrB. *)
(*     rewrite (_ : (q - y) = (q - (y + z * (v - y)) + (z - t + t) * (v - y))); last first. *)
(*       by rewrite subrK opprD addrA subrK. *)
(*     apply: (ler_lt_trans (ler_abs_add _ _)). *)
(*     rewrite (_ : pos eps = pos d1 / 2 + (pos eps - pos d1 / 2)); last first. *)
(*       by rewrite addrCA subrr addr0. *)
(*     rewrite (_ : pos eps - _ = d1) // in Hpq. *)
(*     case: Hpq => /sub_ball_abs Hp /sub_ball_abs Hq. *)
(*     rewrite mul1r /= (_ : pos eps - _ = d1) // !(RminusE,RplusE,RmultE,RdivE) // in Hp, Hq. *)
(*     rewrite absrB in Hp. rewrite absrB in Hq. *)
(*     rewrite (ltr_le_add Hq) // (ler_trans (absrM _ _)) //. *)
(*     rewrite (@ler_trans _ ((pos d2 + 1) * Num.max `|u - x| `|v - y|)) //. *)
(*     apply ler_pmul; [by rewrite normr_ge0 | by rewrite normr_ge0 | | ]. *)
(*     rewrite (ler_trans (ler_abs_add _ _)) // ler_add //. *)
(*     move/sub_ball_abs : Hz; rewrite mul1r => tzd2; by rewrite absrB ltrW. *)
(*     rewrite absRE ger0_norm //; by case/andP: Ht. *)
(*     by rewrite ler_maxr lerr orbT. *)
(*     rewrite /d2 /d1 /=. *)
(*     set n := Num.max _ _. *)
(*     rewrite mulrDl mul1r -mulrA mulVr ?unitfE ?lt0r_neq0 // mulr1. *)
(*     rewrite ler_sub_addr addrAC -mulrDl -mulr2n -mulr_natr. *)
(*     by rewrite -mulrA mulrV ?mulr1 ?unitfE // subrK. *)
(* Qed. *)
(* Admitted. *)

(* TODO redo *)
(* Lemma locally_2d_1d (P : R -> R -> Prop) x y : *)
(*   locally_2d x y P -> *)
(*   locally_2d x y (fun u v => forall t, 0 <= t <= 1 -> locally_2d (x + t * (u - x)) (y + t * (v - y)) P). *)
(* Proof. *)
(* move/locally_2d_1d_strong. *)
(* apply: locally_2d_impl. *)
(* apply locally_2d_forall => u v H t Ht. *)
(* specialize (H t Ht). *)
(* have : locally t (fun z => locally_2d (x + z * (u - x)) (y + z * (v - y)) P) by []. *)
(* by apply: locally_singleton. *)
(* Qed. *)

(* TODO redo *)
(* Lemma locally_2d_ex_dec : *)
(*   forall P x y, *)
(*   (forall x y, P x y \/ ~P x y) -> *)
(*   locally_2d x y P -> *)
(*   {d : {posnum R} | forall u v, `|u - x| < d -> `|v - y| < d -> P u v}. *)
(* Proof. *)
(* move=> P x y P_dec H. *)
(* destruct (@locally_ex _ (x, y) (fun z => P (fst z) (snd z))) as [d Hd]. *)
(* - move: H => /locallyP [e _ H]. *)
(*   by apply/locallyP; exists e. *)
(* exists d=>  u v Hu Hv. *)
(* by apply (Hd (u, v)) => /=; split; apply sub_abs_ball; rewrite absrB. *)
(* Qed. *)

Lemma compact_bounded (K : realType) (V : normedModType K) (A : set V) :
  compact A -> bounded_set A.
Proof.
rewrite compact_cover => Aco.
have covA : A `<=` \bigcup_(n : int) [set p | `|p| < n%:~R].
  move=> p Ap; exists (ifloor `|p| + 1) => //.
  by rewrite rmorphD /= -floorE floorS_gtr.
have /Aco [] := covA.
  move=> n _; rewrite openE => p; rewrite /= -subr_gt0 => ltpn.
  apply/nbhs_ballP; exists (n%:~R - `|p|) => // q.
  rewrite -ball_normE /= ltr_subr_addr distrC; apply: le_lt_trans.
  by rewrite -{1}(subrK p q) ler_norm_add.
move=> D _ DcovA.
exists (\big[maxr/0]_(i : D) (fsval i)%:~R).
rewrite bigmaxr_real ?real0 //; split => //.
move=> x ltmaxx p /DcovA [n Dn /lt_trans /(_ _)/ltW].
apply; apply: le_lt_trans ltmaxx.
have {} : n \in enum_fset D by [].
rewrite enum_fsetE => /mapP[/= i iD ->]; exact/BigmaxBigminr.ler_bigmaxr.
Qed.

Lemma rV_compact (T : topologicalType) n (A : 'I_n.+1 -> set T) :
  (forall i, compact (A i)) ->
  compact [ set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)].
Proof.
move=> Aico.
have : @compact (product_topologicalType _) [set f | forall i, A i (f i)].
  by apply: tychonoff.
move=> Aco F FF FA.
set G := [set [set f : 'I_n.+1 -> T | B (\row_j f j)] | B in F].
have row_simpl (v : 'rV[T]_n.+1) : \row_j (v ord0 j) = v.
  by apply/rowP => ?; rewrite mxE.
have row_simpl' (f : 'I_n.+1 -> T) : (\row_j f j) ord0 = f.
  by rewrite funeqE=> ?; rewrite mxE.
have [f [Af clGf]] : [set f | forall i, A i (f i)] `&`
  @cluster (product_topologicalType _) G !=set0.
  suff GF : ProperFilter G.
    apply: Aco; exists [set v : 'rV[T]_n.+1 | forall i, A i (v ord0 i)] => //.
    by rewrite predeqE => f; split => Af i; [have := Af i|]; rewrite row_simpl'.
  apply Build_ProperFilter.
    move=> _ [C FC <-]; have /filter_ex [v Cv] := FC.
    by exists (v ord0); rewrite /= row_simpl.
  split.
  - by exists setT => //; apply: filterT.
  - by move=> _ _ [C FC <-] [D FD <-]; exists (C `&` D) => //; apply: filterI.
  move=> C D sCD [E FE EeqC]; exists [set v : 'rV[T]_n.+1 | D (v ord0)].
    by apply: filterS FE => v Ev; apply/sCD; rewrite -EeqC/= row_simpl.
  by rewrite predeqE => ? /=; rewrite row_simpl'.
exists (\row_j f j); split; first by move=> i; rewrite mxE; apply: Af.
move=> C D FC f_D; have {}f_D :
  nbhs (f : product_topologicalType _) [set g | D (\row_j g j)].
  have [E f_E sED] := f_D; rewrite nbhsE.
  set Pj := fun j Bj => open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
  have exPj : forall j, exists Bj, open_nbhs (f j) Bj /\ Bj `<=` E ord0 j.
    move=> j; have := f_E ord0 j; rewrite nbhsE => - [Bj].
    by rewrite row_simpl'; exists Bj.
  exists [set g | forall j, (get (Pj j)) (g j)]; split; last first.
    move=> g Pg; apply: sED => i j; rewrite ord1 row_simpl'.
    by have /getPex [_ /(_ _ (Pg j))] := exPj j.
  split; last by move=> j; have /getPex [[]] := exPj j.
  exists [set [set g | forall j, get (Pj j) (g j)] | k in 'I_n.+1];
    last first.
    rewrite predeqE => g; split; first by move=> [_ [_ _ <-]].
    move=> Pg; exists [set g | forall j, get (Pj j) (g j)] => //.
    by exists ord0.
  move=> _ [_ _ <-]; set s := [seq (@^~ j) @^-1` (get (Pj j)) | j : 'I_n.+1].
  exists [fset x in s]%fset.
    move=> B'; rewrite in_fset => /mapP [j _ ->]; rewrite inE.
    exists j => //; exists (get (Pj j)) => //.
    by have /getPex [[]] := exPj j.
  rewrite predeqE => g; split=> [Ig j|Ig B'].
    apply: (Ig ((@^~ j) @^-1` (get (Pj j)))).
    by rewrite /= in_fset; apply/mapP; exists j => //; rewrite mem_enum.
  by rewrite /= in_fset => /mapP [j _ ->]; apply: Ig.
have GC : G [set g | C (\row_j g j)] by exists C.
by have [g []] := clGf _ _ GC f_D; exists (\row_j (g j : T)).
Qed.

Lemma bounded_closed_compact (R : realType) n (A : set 'rV[R^o]_n.+1) :
  bounded_set A -> closed A -> compact A.
Proof.
move=> [M [Mreal normAltM]] Acl.
have Mnco : compact
  [set v : 'rV[R^o]_n.+1 | (forall i, (v ord0 i) \in `[(- (M + 1)), (M + 1)])].
  apply: (@rV_compact [topologicalType of R^o] _
    (fun _ => [set x | x \in `[(- (M + 1)), (M + 1)]])).
  by move=> _; apply: segment_compact.
apply: subclosed_compact Acl Mnco _ => v /normAltM normvleM i.
suff : `|v ord0 i : R^o| <= M + 1 by rewrite ler_norml.
apply: le_trans (normvleM _ _); last by rewrite ltr_addl.
have /mapP[j Hj ->] : `|v ord0 i| \in [seq `|v ij.1 ij.2| | ij : 'I_1 * 'I_n.+1].
  by apply/mapP; exists (ord0, i) => //=; rewrite mem_enum.
rewrite [in X in _ <= X]/normr /= mx_normrE.
by apply/BigmaxBigminr.bigmaxr_gerP; right => /=; exists j.
Qed.

Section open_closed_sets_ereal.
Variable R : realFieldType (* TODO: generalize to numFieldType? *).
Implicit Types x y : {ereal R}.
Implicit Types r : R.

Lemma open_ereal_lt y : open [set r : R^o | r%:E < y]%E.
Proof.
case: y => [y||] /=; first exact: open_lt.
rewrite [X in open X](_ : _ = setT); first exact: openT.
by rewrite funeqE => ? /=; rewrite lte_pinfty trueE.
rewrite [X in open X](_ : _ = set0); first exact: open0.
by rewrite funeqE => ? /=; rewrite falseE.
Qed.

Lemma open_ereal_gt y : open [set r : R^o | y < r%:E]%E.
Proof.
case: y => [y||] /=; first exact: open_gt.
rewrite [X in open X](_ : _ = set0); first exact: open0.
by rewrite funeqE => ? /=; rewrite falseE.
rewrite [X in open X](_ : _ = setT); first exact: openT.
by rewrite funeqE => ? /=; rewrite lte_ninfty trueE.
Qed.

Lemma open_ereal_lt' x y : (x < y)%E -> ereal_nbhs x (fun u => u < y)%E.
Proof.
case: x => [x|//|] xy; first exact: open_ereal_lt.
case: y => [y||//] /= in xy *.
exists y; rewrite num_real; split => //= x ? //.
by exists 0.
case: y => [y||//] /= in xy *.
exists y; rewrite num_real; split => //= x ? //.
exists 0; rewrite real0; split => // x.
by move/lt_le_trans; apply; rewrite lee_pinfty.
Qed.

Lemma open_ereal_gt' x y : (y < x)%E -> ereal_nbhs x (fun u => y < u)%E.
Proof.
case: x => [x||] //=; do ?[exact: open_ereal_gt];
  case: y => [y||] //=; do ?by exists 0; rewrite real0.
by exists y; rewrite num_real.
move=> _; exists 0; rewrite real0; split => // x.
by apply/le_lt_trans; rewrite lee_ninfty.
Qed.

Let open_ereal_lt_real r : open (fun x => x < r%:E)%E.
Proof.
case => [? | // | ?]; [rewrite lte_fin => xy | by exists r].
by move: (@open_ereal_lt r%:E); rewrite openE; apply; rewrite /= lte_fin.
Qed.

Lemma open_ereal_lt_ereal x : open [set y | y < x]%E.
Proof.
case: x => [x | | [] // ] /=; first exact: open_ereal_lt_real.
suff -> : ([set y | y < +oo] = \bigcup_r [set y : {ereal R} | y < r%:E])%E.
  by apply open_bigU => x _; exact: open_ereal_lt_real.
rewrite predeqE => -[r | | ]/=.
- rewrite lte_pinfty; split => // _.
  by exists (r + 1) => //=; rewrite lte_fin ltr_addl.
- by rewrite ltxx; split => // -[] x /=; rewrite ltNge lee_pinfty.
- by split => // _; exists 0 => //=; rewrite lte_ninfty.
Qed.

Let open_ereal_gt_real r : open (fun x => r%:E < x)%E.
Proof.
case => [? | ? | //]; [rewrite lte_fin => xy | by exists r].
by move: (@open_ereal_gt r%:E); rewrite openE; apply; rewrite /= lte_fin.
Qed.

Lemma open_ereal_gt_ereal x : open [set y | x < y]%E.
Proof.
case: x => [x | [] // | ] /=; first exact: open_ereal_gt_real.
suff -> : ([set y | -oo < y] = \bigcup_r [set y : {ereal R} | r%:E < y])%E.
  by apply open_bigU => x _; exact: open_ereal_gt_real.
rewrite predeqE => -[r | | ]/=.
- rewrite lte_ninfty; split => // _.
  by exists (r - 1) => //=; rewrite lte_fin ltr_subl_addr ltr_addl.
- by split => // _; exists 0 => //=; rewrite lte_pinfty.
- by rewrite ltxx; split => // -[] x _ /=; rewrite ltNge lee_ninfty.
Qed.

Lemma closed_ereal_le_ereal y : closed [set x | (y <= x)%E].
Proof.
rewrite (_ : [set x | y <= x]%E = ~` [set x | y > x]%E); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_lt_ereal.
Qed.

Lemma closed_ereal_ge_ereal y : closed [set x | (y >= x)%E].
Proof.
rewrite (_ : [set x | y >= x]%E = ~` [set x | y < x]%E); last first.
  by rewrite predeqE=> x; split=> [rx|/negP]; [apply/negP|]; rewrite -leNgt.
exact/closedC/open_ereal_gt_ereal.
Qed.

End open_closed_sets_ereal.

Section ereal_is_hausdorff.
Variable R : realFieldType.
Implicit Types r : R.

Lemma nbhs_image_ERFin (x : R^o) (X : set R) :
  nbhs x X -> nbhs x%:E ((fun r => r%:E) @` X).
Proof.
case => _/posnumP[e] xeX; exists e%:num => //= r xer.
by exists r => //; apply xeX.
Qed.

Lemma nbhs_open_ereal_lt r (f : R -> R) : r < f r ->
  nbhs r%:E [set y | y < (f r)%:E]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_gt r (f : R -> R) : f r < r ->
  nbhs r%:E [set y | (f r)%:E < y]%E.
Proof.
move=> xfx; rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_fin].
Qed.

Lemma nbhs_open_ereal_pinfty r : nbhs +oo%E [set y | r%:E < y]%E.
Proof.
rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_gt_ereal | rewrite /= lte_pinfty].
Qed.

Lemma nbhs_open_ereal_ninfty r : nbhs -oo%E [set y | y < r%:E]%E.
Proof.
rewrite nbhsE /=; eexists; split; last by move=> y; exact.
by split; [apply open_ereal_lt_ereal | rewrite /= lte_ninfty].
Qed.

Lemma ereal_hausdorff : hausdorff (ereal_topologicalType R).
Proof.
move=> -[r| |] // [r' | |] //=.
- move=> rr'; congr (_%:E); apply Rhausdorff => /= A B rA r'B.
  have [/= z [[r0 ? r0z] [r1 ?]]] :=
    rr' _ _ (nbhs_image_ERFin rA) (nbhs_image_ERFin r'B).
  by rewrite -r0z => -[r1r0]; exists r0; split => //; rewrite -r1r0.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r : r < r + 1.
    by rewrite ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_pinfty (r + 1))) => -[z [zr rz]].
  by move: (lt_trans rz zr); rewrite lte_fin ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) loc_r : r - 1 < r.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ loc_r (nbhs_open_ereal_ninfty (r - 1))) => -[z [rz zr]].
  by move: (lt_trans zr rz); rewrite ltxx.
- have /(@nbhs_open_ereal_lt _ (fun x => x + 1)) loc_r' : r' < r' + 1.
    by rewrite ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_pinfty (r' + 1)) loc_r') => -[z [r'z zr']].
  by move: (lt_trans zr' r'z); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_pinfty 0) (nbhs_open_ereal_ninfty 0)).
  by move=> -[z [zx xz]]; move: (lt_trans xz zx); rewrite ltxx.
- have /(@nbhs_open_ereal_gt _ (fun x => x - 1)) yB : r' - 1 < r'.
    by rewrite ltr_subl_addr ltr_addl.
  move/(_ _ _ (nbhs_open_ereal_ninfty (r' - 1)) yB) => -[z [zr' r'z]].
  by move: (lt_trans r'z zr'); rewrite ltxx.
- move/(_ _ _ (nbhs_open_ereal_ninfty 0) (nbhs_open_ereal_pinfty 0)).
  by move=> -[z [zO Oz]]; move: (lt_trans Oz zO); rewrite ltxx.
Qed.

End ereal_is_hausdorff.

Hint Resolve ereal_hausdorff : core.

(** * Some limits on real functions *)

Lemma continuous_withinNx (R : numFieldType) {U V : pseudoMetricType R}
  (f : U -> V) x :
  {for x, continuous f} <-> f @ nbhs' x --> f x.
Proof.
split=> - cfx P /= fxP.
  rewrite /nbhs' !near_simpl near_withinE.
  by rewrite /nbhs'; apply: cvg_within; apply/cfx.
 (* :BUG: ssr apply: does not work,
    because the type of the filter is not inferred *)
rewrite !nbhs_nearE !near_map !near_nbhs in fxP *; have /= := cfx P fxP.
rewrite !near_simpl near_withinE near_simpl => Pf; near=> y.
by have [->|] := eqVneq y x; [by apply: nbhs_singleton|near: y].
Grab Existential Variables. all: end_near. Qed.
