(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum interval rat.
From mathcomp Require Import finmap.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality.
From mathcomp Require Import reals signed topology function_spaces set_interval.
From HB Require Import structures.

(**md**************************************************************************)
(* # The Cantor Space and Applications                                        *)
(*                                                                            *)
(* This file develops the theory of the Cantor space, that is bool^nat with   *)
(* the product topology. The two main theorems proved here are                *)
(* homeomorphism_cantor_like, and cantor_surj, a.k.a. Alexandroff-Hausdorff.  *)
(*                                                                            *)
(* ```                                                                        *)
(*          cantor_space == the Cantor space, with its canonical metric       *)
(*         cantor_like T == perfect + compact + hausdroff + zero dimensional  *)
(*             tree_of T == builds a topological tree with levels (T n)       *)
(* ```                                                                        *)
(*                                                                            *)
(* The overall goal of the next few sections is to prove that                 *)
(*       Every compact metric space `T` is the image of the Cantor space.     *)
(*  The overall proof will build two continuous functions                     *)
(*           Cantor space -> a bespoke tree for `T` -> `T`                    *)
(*                                                                            *)
(* The proof is in 4 parts:                                                   *)
(* - Part 1: Some generic machinery about continuous functions from trees.    *)
(* - Part 2: All cantor-like spaces are homeomorphic to the Cantor space.     *)
(*           (an application of part 1)                                       *)
(* - Part 3: Finitely branching trees are Cantor-like.                        *)
(* - Part 4: Every compact metric space has a finitely branching tree with    *)
(*           a continuous surjection. (a second application of part 1)        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.

Definition cantor_space :=
  prod_topology (fun _ : nat => discrete_topology discrete_bool).

HB.instance Definition _ := Pointed.on cantor_space.
HB.instance Definition _ := Nbhs.on cantor_space.
HB.instance Definition _ := Topological.on cantor_space.

Definition cantor_like (T : topologicalType) :=
  [/\ perfect_set [set: T],
      compact [set: T],
      hausdorff_space T &
      zero_dimensional T].

Lemma cantor_space_compact : compact [set: cantor_space].
Proof.
have := @tychonoff _ (fun _ : nat => _) _ (fun=> discrete_bool_compact).
by congr (compact _); rewrite eqEsubset.
Qed.

Lemma cantor_space_hausdorff : hausdorff_space cantor_space.
Proof.
apply: hausdorff_product => ?; apply: discrete_hausdorff.
exact: discrete_space_discrete.
Qed.

Lemma cantor_zero_dimensional : zero_dimensional cantor_space.
Proof.
apply: zero_dimension_prod => _; apply: discrete_zero_dimension.
exact: discrete_space_discrete.
Qed.

Lemma cantor_perfect : perfect_set [set: cantor_space].
Proof. by apply: perfect_diagonal => _; exists (true, false). Qed.

Lemma cantor_like_cantor_space : cantor_like cantor_space.
Proof.
split.
- exact: cantor_perfect.
- exact: cantor_space_compact.
- exact: cantor_space_hausdorff.
- exact: cantor_zero_dimensional.
Qed.

Section big_lexi_order.

Context {K : nat -> eqType} .

Definition share_prefix n (t1 t2: forall n, K n) :=
  (forall m, (m < n)%O -> t1 m = t2 m).

Lemma share_prefix0 t1 t2 : share_prefix 0 t1 t2.
Proof. by rewrite /share_prefix. Qed.

Hint Resolve share_prefix0 : core.

Lemma share_prefixC n t1 t2 : share_prefix n t1 t2 <-> share_prefix n t2 t1.
Proof. by rewrite /share_prefix; split => + m mn => /(_ m mn). Qed.

Lemma share_prefixS n m t1 t2 : 
  n <= m -> share_prefix m t1 t2 -> share_prefix n t1 t2.
Proof. 
move=> nm + r rn; apply; move: nm; rewrite leq_eqVlt => /orP.
by case=>[/eqP <- //|/(ltn_trans rn)]; exact.
Qed.

Lemma share_prefix_refl n x : share_prefix n x x.
Proof. by move=> ? ?. Qed.

Lemma share_prefix_trans n x y z : 
  share_prefix n x y -> 
  share_prefix n y z -> 
  share_prefix n x z. 
Proof. by move=> + + m mn => /(_ _ mn) ->; apply. Qed.

Definition first_diff (t1 t2: forall n, K n) : option nat :=
  xget None (Some  @` [set n | share_prefix n t1 t2 /\ t1 n <> t2 n]).

Lemma first_diffC t1 t2 : first_diff t1 t2 = first_diff t2 t1.
Proof.
by rewrite /first_diff /=; congr (_ _ _); rewrite eqEsubset; split => z /=;
  (case => w [wE /nesym NE]; exists w => //; split);
  rewrite // share_prefixC.
Qed.

Lemma first_diff_unique (x y : forall n, K n) : forall (n m : nat), 
  (share_prefix n x y /\ x n <> y n) ->
  (share_prefix m x y /\ x m <> y m) ->
  n = m.
Proof.
move=> n m [nPfx xyn] [mPfx xym]; apply/eqP.
apply: contrapT; move/negP; rewrite neq_ltn => /orP; case => RN.
  by move: xyn; have -> := mPfx _ RN.
by move: xym; have -> := nPfx _ RN.
Qed.
 
Lemma first_diff_SomeP x y n : 
  first_diff x y = Some n <-> share_prefix n x y /\ x n <> y n.
Proof.
split.
  rewrite /first_diff; case: xgetP=> // ? -> []? [+ + <-/Some_inj nE]. 
  by rewrite {}nE /= => ? ?; split.
case=> pfx xNy; rewrite /first_diff; case: xgetP => //=; first last.
  by move/(_ (Some n)); apply: absurd; exists n.
case; last by move => ? [].
by move=> m -> [o] [? ?] <-; congr(_ _); apply: (@first_diff_unique x y). 
Qed.

Lemma first_diff_NoneP t1 t2 : t1 = t2 <-> first_diff t1 t2 = None.
Proof.
split; rewrite /first_diff.
  by move=> ->; case: xgetP => //; case => // ? ? [? /=] []//.
case: xgetP; first by move=> ? -> [i /=] [?] ? <-.
move=> /= R _; apply/functional_extensionality_dep.
suff : forall n, forall x, x < n -> t1 x = t2 x.
  by move=> + n => /(_ n.+1)/(_ n); apply.
elim; first by move=> ?.
move=> n IH x; rewrite leq_eqVlt => /orP [/eqP/succn_inj ->|xn]; last exact: IH.
have /forall2NP/(_ n) [] := R (Some n) => // /not_andP.
case; first by case/existsNP=> m /not_implyP [//] mx; apply: absurd; apply/IH.
by move/contrapT ->.
Qed.

Lemma first_diff_lt a x y n m : 
  n < m ->
  first_diff a x = Some n ->
  first_diff a y = Some m ->
  first_diff x y = Some n.
Proof.
move=> nm /first_diff_SomeP [xpfx xE] /first_diff_SomeP [ypfx yE]. 
apply/first_diff_SomeP; split.
  by move=> o /[dup] on /xpfx <-; apply: ypfx; apply: (ltn_trans on).
by have <- := ypfx _ nm; exact/nesym.
Qed.

Lemma first_diff_eq a x y n m : 
  first_diff a x = Some n ->
  first_diff a y = Some n ->
  first_diff x y = Some m -> 
  n <= m.
Proof.
case/first_diff_SomeP => axPfx axn /first_diff_SomeP [ayPfx ayn].
case/first_diff_SomeP => xyPfx; rewrite leqNgt; apply: contra_notN => mn.
by have <- := ayPfx _ mn; have <- := axPfx _ mn.
Qed.

Lemma first_diff_dfwith x i b : 
  (x i) <> b <-> first_diff x (@dfwith _ K x i b) = Some i.
Proof.
split; first last.
  by case/first_diff_SomeP => _ /=; apply: contra_not; rewrite dfwithin.
move=> xNb; apply/first_diff_SomeP; split; last by rewrite dfwithin.
move=> n ni; apply/eqP; rewrite dfwithout //.
by apply/negP => /eqP E; move: ni; rewrite E ltexx.
Qed.

Definition lexi_bigprod  (R : forall n, K n -> K n -> bool) (t1 t2 : forall n, K n) :=
  match first_diff t1 t2 with  
  | Some n => R n (t1 n) (t2 n)
  | None => true
  end.

Lemma lexi_bigprod_reflexive R : reflexive (lexi_bigprod R).
Proof.
move=> x; rewrite /lexi_bigprod /=.
rewrite /lexi_bigprod/first_diff.
by case: xgetP => //=; case=> // n /= _ [m [/= _]].
Qed.

Lemma lexi_bigprod_anti R : (forall n, antisymmetric (R n)) ->
  antisymmetric (lexi_bigprod R).
Proof.
move=> antiR x y /andP [xy yx]; apply/first_diff_NoneP; move: xy yx.
rewrite /lexi_bigprod first_diffC; case E: (first_diff y x) => [n|]// ? ?.
case/first_diff_SomeP: E => _; apply: contra_notP => _.
by apply: antiR; apply/andP; split.
Qed.

Lemma lexi_bigprod_trans R : 
  (forall n, transitive (R n)) -> 
  (forall n, antisymmetric (R n)) -> 
  transitive (lexi_bigprod R).
move=> Rtrans Ranti y x z; rewrite /lexi_bigprod /=.
case Ep: (first_diff x y) => [p|]; last by move/first_diff_NoneP: Ep ->.
case Er: (first_diff x z) => [r|]; last by move/first_diff_NoneP: Er ->.
case Eq: (first_diff y z) => [q|]; first last.
  by move: Ep Er; move/first_diff_NoneP: Eq => -> -> /Some_inj ->. 
have := leqVgt p q; rewrite leq_eqVlt => /orP [/orP[]|].
- move=> /eqP pqE; move: Ep Eq; rewrite pqE => Eqx Eqz.
  rewrite first_diffC in Eqx; have := first_diff_eq Eqx Eqz Er.
  rewrite leq_eqVlt => /orP [/eqP ->|qr]; first by exact: Rtrans.
  case/first_diff_SomeP:Er => /(_ _ qr) -> _ ? ?; have : z q = y q.
    by apply: Ranti; apply/andP; split.
  by move=> E; case/first_diff_SomeP: Eqz=> + /nesym; rewrite E.
- move=> pq; move: Er.
  rewrite (@first_diff_lt y x z _ _ pq) ?[_ y x]first_diffC //.
  by move/Some_inj <- => ? _; case/first_diff_SomeP:Eq => /(_ _ pq) <-.
- move=> qp; move: Er.
  rewrite first_diffC (@first_diff_lt y _ _ _ _ qp) // ?[_ y x]first_diffC //.
  by move/Some_inj <- => _ ?; case/first_diff_SomeP:Ep => /(_ _ qp) ->.
Qed.

Lemma lexi_bigprod_total R : (forall n, total (R n)) -> total (lexi_bigprod R).
Proof.
move=> Rtotal; move=> x y.
case E : (first_diff x y) => [n|]; first last.
  by move/first_diff_NoneP:E ->; rewrite lexi_bigprod_reflexive.
rewrite /lexi_bigprod E first_diffC E; exact: Rtotal.
Qed.

Definition start_with n (t1 t2: forall n, K n) (i : nat) : K i := 
  if (i < n)%O then t1 i else t2 i.

Lemma start_with_prefix n x y : share_prefix n x (start_with n x y).
Proof. by move=> r rn; rewrite /start_with rn. Qed.

End big_lexi_order.

Definition big_lexi_order {I : Type} (T : I -> Type) : Type := forall i, T i.
HB.instance Definition _ (I : Type) (K : I -> choiceType) := 
  Choice.on (big_lexi_order K).

Section big_lexi_porder.
Context {d} {K : nat -> porderType d}.

Definition big_lexi_ord : rel (big_lexi_order K) := 
  lexi_bigprod (fun n k1 k2 => k1 <= k2)%O.

Lemma big_lexi_ord_reflexive : reflexive big_lexi_ord.
Proof. exact: lexi_bigprod_reflexive. Qed.

Lemma big_lexi_ord_anti : antisymmetric big_lexi_ord.
Proof. by apply: lexi_bigprod_anti => n; exact: le_anti. Qed.

Lemma big_lexi_ord_trans : transitive big_lexi_ord.
Proof. by apply: lexi_bigprod_trans=> n; [exact: le_trans| exact: le_anti]. Qed.

HB.instance Definition _ := Order.Le_isPOrder.Build d (big_lexi_order K)
  big_lexi_ord_reflexive big_lexi_ord_anti big_lexi_ord_trans.
End big_lexi_porder.

Section big_lexi_total.
Context {d} {K : nat -> orderType d}.

Lemma big_lexi_ord_total : total (@big_lexi_ord _ K).
Proof. by apply: lexi_bigprod_total => ?; exact: le_total. Qed.

HB.instance Definition _ := Order.POrder_isTotal.Build _ 
  (big_lexi_order K) big_lexi_ord_total.

End big_lexi_total.

Section big_lexi_bottom.
Context {d} {K : nat -> finOrderType d}.

Lemma big_lex_bot x : (@big_lexi_ord _ K) (fun=> \bot)%O x.
Proof. 
rewrite /big_lexi_ord/lexi_bigprod; case E: (first_diff _ _) => //.
exact: le0x.
Qed.

HB.instance Definition _ := @Order.hasBottom.Build _ 
  (big_lexi_order K) (fun=> \bot)%O big_lex_bot.

End big_lexi_bottom.

Section big_lexi_top.
Context {d} {K : nat -> finOrderType d}.

Lemma big_lex_top x : (@big_lexi_ord _ K) x (fun=> \top)%O.
Proof. 
rewrite /big_lexi_ord/lexi_bigprod; case E: (first_diff _ _) => //.
exact: lex1.
Qed.

HB.instance Definition _ := @Order.hasTop.Build _ 
  (big_lexi_order K) (fun=> \top)%O big_lex_top.

End big_lexi_top.

Lemma tree_prefix {K : nat -> topologicalType} (b : (prod_topology K)) (n : nat) :
  (forall n, discrete_space (K n)) ->
  \forall c \near b, share_prefix n b c. 
Proof.
move=> dscK; elim: n => [|n IH]; first by near=> z => ?.
near=> z => i; rewrite /Order.lt /= ltnS leq_eqVlt.
move=> /predU1P[|iSn]; last by rewrite (near IH z).
move=> ->; near: z; exists (proj n @^-1` [set b n]).
split => //; suff : @open (prod_topology K) (proj n @^-1` [set b n]) by [].
apply: open_comp; [move=> + _; exact: proj_continuous| apply: discrete_open].
exact: dscK.
Unshelve. all: end_near. Qed.

Lemma lexi_bigprod_prefix_lt {d} (K : nat -> orderType d) 
    (b a x: big_lexi_order K) n: 
  (a < b)%O -> 
  first_diff a b = Some n ->
  share_prefix n.+1 x b ->
  (a < x)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP [pfa abN].
case E1 : (first_diff a x) => [m|]; first last.
  by move/first_diff_NoneP:E1 <- => _ /(_ n (ltnSn _)).
move=> ab pfx; apply/andP; split.
  by apply/negP => /eqP/first_diff_NoneP; rewrite first_diffC E1.
move: ab; rewrite /Order.lt/= => /andP [?].
rewrite /big_lexi_ord /lexi_bigprod E1 abD; suff : n = m. 
  by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ a x) => //=; last by case/first_diff_SomeP:E1.
split; last by by have -> := pfx n (ltnSn _).
by apply: (share_prefix_trans pfa); rewrite share_prefixC; exact: share_prefixS.
Qed.

Lemma lexi_bigprod_prefix_gt {d} (K : nat -> orderType d) 
    (b a x: big_lexi_order K) n:
  (b < a)%O -> 
  first_diff a b = Some n ->
  share_prefix n.+1 x b ->
  (x < a)%O.
Proof.
move=> + /[dup] abD /first_diff_SomeP [pfa abN].
case E1 : (first_diff x a) => [m|]; first last.
  by move/first_diff_NoneP:E1 -> => _ /(_ n (ltnSn _)).
move=> ab pfx; apply/andP; split.
  by apply/negP => /eqP/first_diff_NoneP; rewrite first_diffC E1.
move: ab; rewrite /Order.lt/= => /andP [?].
rewrite /big_lexi_ord /lexi_bigprod [_ b a]first_diffC E1 abD; suff : n = m. 
  by have := pfx n (ltnSn _) => /[swap] -> ->.
apply: (@first_diff_unique _ x a) => //=; last by case/first_diff_SomeP:E1.
rewrite share_prefixC; split; last by have -> := pfx n (ltnSn _); apply/nesym.
by apply: (share_prefix_trans pfa); rewrite share_prefixC; exact: share_prefixS.
Qed.

Lemma big_lexi_interval_prefix {d} (K : nat -> orderType d) 
    (i : interval (big_lexi_order K))
    (x : big_lexi_order K) : 
  itv_open_ends i ->
  x \in i ->
  exists n, (share_prefix n x `<=` [set` i]).
Proof.
move: i; case=> [][[]l|[]] [[]r|[]] [][]; rewrite ?in_itv /= ?andbT.
- move=> /andP [] lx xr. 
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP: E1 ->; rewrite bnd_simp.
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP: E2 ->; rewrite bnd_simp.
  exists (Order.max n m).+1 => p xppfx; rewrite set_itvE. 
  apply/andP; split. 
    apply: (lexi_bigprod_prefix_lt lx E1) => w wm; apply/sym_equal/xppfx.
    by move/ltnSE/leq_ltn_trans: wm; apply; rewrite ltnS leq_max leqnn orbT.
  rewrite first_diffC in E2.
  apply: (lexi_bigprod_prefix_gt xr E2) => w wm; apply/sym_equal/xppfx.
  by move/ltnSE/leq_ltn_trans: wm; apply; rewrite ltnS leq_max leqnn.
- move=> lx. 
  case E1 : (first_diff l x) => [m|]; first last.
    by move: lx; move/first_diff_NoneP: E1 ->; rewrite bnd_simp.
  exists m.+1 => p xppfx; rewrite set_itvE /=.
  by apply: (lexi_bigprod_prefix_lt lx E1) => w wm; apply/sym_equal/xppfx.
- move=> xr. 
  case E2 : (first_diff x r) => [n|]; first last.
    by move: xr; move/first_diff_NoneP: E2 ->; rewrite bnd_simp.
  exists n.+1; rewrite first_diffC in E2 => p xppfx. 
  rewrite set_itvE /=.
  by apply: (lexi_bigprod_prefix_gt xr E2) => w wm; apply/sym_equal/xppfx.
by move=> _; exists 0=> ? ?; rewrite set_itvE.
Unshelve. all: end_near. Qed.

Lemma lexi_bigprod_between {d} (K : nat -> orderType d) 
    (a x b: big_lexi_order K) n:
  (a <= x <= b)%O -> 
  share_prefix n a b -> 
  share_prefix n x a. 
Proof.
move=> axb; elim: n => // n IH.
move=> pfxSn m mSn; have pfxA : share_prefix n a x.
  by rewrite share_prefixC; apply: IH; apply: (share_prefixS _  pfxSn).
have pfxB : share_prefix n x b.
  apply (@share_prefix_trans _ n x a b); first by rewrite share_prefixC.
  exact: (share_prefixS _  pfxSn).
move: mSn; rewrite /Order.lt/= ltnS leq_eqVlt => /orP []; first last.
  by move: pfxA; rewrite share_prefixC; exact.
move/eqP ->; apply: le_anti; apply/andP; split.
  case/andP:axb => ? +; rewrite {1}/Order.le/=/big_lexi_ord/lexi_bigprod.
  have -> := pfxSn n (ltnSn _).
  case E : (first_diff x b) => [r|]; last by move/first_diff_NoneP:E ->.
  move=> xrb; have : n <= r. 
    rewrite leqNgt; apply/negP=> /[dup] /pfxB xbE.
    by case/first_diff_SomeP:E => _; rewrite xbE. 
  rewrite leq_eqVlt => /orP [/eqP -> //|] => nr.
  by case/first_diff_SomeP:E => /(_ n nr) ->. 
case/andP:axb => + ?; rewrite {1}/Order.le/=/big_lexi_ord/lexi_bigprod.
case E : (first_diff a x) => [r|]; last by move/first_diff_NoneP:E <-. 
move=> xrb; have : n <= r. 
  rewrite leqNgt; apply/negP=> /[dup] /pfxA xbE.
  by case/first_diff_SomeP:E => _; rewrite xbE. 
rewrite leq_eqVlt => /orP [/eqP -> //|] => nr.
by case/first_diff_SomeP:E => /(_ n nr) ->. 
Qed.

Section foo.
Context {d} {K : nat -> finOrderType d}.
Let oT := order_topology (big_lexi_order K).

Lemma shared_prefix_closed_itv n (x : oT) :
  share_prefix n x = 
    `[(start_with n x (fun=>\bot):oT)%O, (start_with n x (fun=>\top))%O].
Proof.
rewrite eqEsubset; split=> z; first last.
  rewrite set_itvE /= => xbt; apply: share_prefix_trans.
    apply: (@start_with_prefix _ _ _ (fun=> \bot)%O).
  rewrite share_prefixC; apply: (lexi_bigprod_between xbt).
  apply:share_prefix_trans; last by apply: @start_with_prefix.
  by rewrite share_prefixC; apply: start_with_prefix.
move=> pfxz; rewrite set_itvE /= /Order.le /= /big_lexi_ord /= /lexi_bigprod. 
apply/andP; split.
  case E : (first_diff _ _ ) => [m|] //; rewrite /start_with /=.
  case mn : (_ < _)%O => //; last by rewrite le0x.
  by (suff -> : x m = z m by done); apply: pfxz.
case E : (first_diff _ _ ) => [m|] //; rewrite /start_with /=.
case mn : (_ < _)%O => //; last by rewrite lex1.
by (suff -> : x m = z m by done); apply: pfxz.
Qed.

Lemma shared_prefix_closed n (x : oT) : @closed oT (share_prefix n x).
Proof. by rewrite shared_prefix_closed_itv; exact: itv_closed. Qed.

Lemma shared_prefix_open n (x : oT) : 
  @open oT (share_prefix n x).
Proof. 
elim: n x.
  move=> x; suff -> : (share_prefix 0 x) = setT by exact: openT.
  by rewrite -subTset.
move=> n IH x.
suff -> : share_prefix n.+1 x = share_prefix n x `&` 
  \big[setI/setT]_(t <- enum (K n) | t != x n) (~` (share_prefix n.+1 (dfwith x n t))).
  apply: openI => //.
  apply: big_ind; [exact: openT | move=> ? ? ? ?; exact: openI |].
  move=> ? ?; apply: closed_openC; apply: shared_prefix_closed.
rewrite eqEsubset; split=> z.
  move=> zpfx; split; first by apply: (share_prefixS _ zpfx).
  rewrite -bigcap_seq_cond => w /= /andP [_]; apply: contra_neq_not.
  move/(_ n (ltnSn _)); rewrite dfwithin => ->; apply/sym_equal/ zpfx.
  exact: ltnSn.
case => /= pfzn; rewrite -bigcap_seq_cond => knz r.
rewrite /Order.lt /= ltnS leq_eqVlt => /orP []; last exact: pfzn.
move/eqP ->; move: knz; rewrite -setC_bigcup.
apply: contra_notP => xNz; exists (z n) => //=.
  apply/andP; split => //=; first exact: mem_enum.
  by move: xNz; apply: contra_not_neq => ->.
move=> w; rewrite /Order.lt /= ltnS leq_eqVlt => /orP []. 
  by move/eqP ->; rewrite dfwithin.
by move=> /[dup] wz /pfzn <-; rewrite dfwithout // neq_lt /Order.lt /= wz orbT.
Qed.
End foo.

#[short(type="finOrderTopologicalType")]
HB.structure Definition FiniteOrderTopologicalType d :=
  {T of OrderTopological d T & Order.FinDistrLattice d T}.
 Local Lemma bool_nbhs_itv (b : bool) : 
  nbhs b = filter_from 
    (fun i => itv_open_ends i /\ b \in i)
    (fun i => [set` i]).
Proof. 
rewrite discrete_bool eqEsubset; split=> U; first last.
  by case => V [_ Vb] VU; apply/principal_filterP/VU; apply: Vb.
move/principal_filterP; case: b.
  move=> Ut; exists (`]false, +oo[)%O; first split => //; first by left.
  by move=> r /=; rewrite in_itv /=; case: r.
move=> Ut; exists (`]-oo, true[)%O; first split => //; first by left.
by move=> r /=; rewrite in_itv /=; case: r.
Qed.
HB.instance Definition _ := Order_isNbhs.Build _ bool bool_nbhs_itv.
Section prod_order.
Context {d} {K : nat -> finOrderTopologicalType d}.

Local Notation oT := (order_topology (big_lexi_order K)).
Local Notation pT := (prod_topology K).
Hypothesis dscN : (forall n, discrete_space (K n)).

Lemma order_sub_prod (U : set (forall n, K n)) x : 
  nbhs (x : oT) U -> nbhs (x : pT) U.
Proof.
have ? : Filter (@nbhs _ pT x) by exact: nbhs_filter.
rewrite itv_nbhsE /=; case => i [roi xi] /filterS; apply. 
have [n npfx] := big_lexi_interval_prefix roi xi.
have := @tree_prefix K x n dscN; apply: filter_app. 
by near=> b => pfx; apply: npfx => ? ?; apply: pfx.
Unshelve. all: end_near. Qed.

Lemma order_prod_open (U : set (forall n, K n)) : 
  @open oT U -> @open pT U.
Proof.
by rewrite ?openE/interior => + x Ux => /(_ x Ux); apply: order_sub_prod.
Qed.

Lemma prod_sub_order (U : set (forall n, K n)) x : 
    nbhs (x : pT) U -> nbhs (x : oT) U.
Proof. 
suff : forall F, Filter F -> (F --> (x : oT)) -> {ptws, F --> x} by exact.
move=> F FF FcvgOrd; apply/cvg_sup => i V; rewrite nbhs_simpl /=.
case=> ? [/= [W] ? ]; rewrite (_ : @^~ i @^-1` W = (proj i) @^-1`W) // => <- /=.
rewrite {1}/proj => Wxi /filterS; apply; apply: FcvgOrd.
rewrite nbhsE /=; exists (share_prefix i.+1 x).
  split; [exact: shared_prefix_open|exact: share_prefix_refl].
move=> z pfxz /=; suff : x i = z i by rewrite /proj; move => <-.
by apply: pfxz; exact: ltnSn.
Qed.

End prod_order.

HB.instance Definition _ := Order.TBPOrder.copy 
  (cantor_space) (big_lexi_order (fun=>bool)).
HB.instance Definition _ := Order.Total.copy cantor_space (big_lexi_order (fun=>bool)).

Lemma nbhs_itv_cantor : forall (x:cantor_space), nbhs x = filter_from 
    (fun i => itv_open_ends i /\ x \in i)
    (fun i => [set` i]). 
Proof.
move=> x; rewrite eqEsubset; split => U.

  have := (@prod_sub_order _ (fun=>bool) U x).
  Set Printing Implicit.
  move/prod_sub_order. rewrite itv_nbhsE //.
by move=> ?; apply/order_sub_prod; rewrite itv_nbhsE.

HB.instance Definition _ := OrderTopological.copy
  cantor_space (prod_topology (fun=> bool)).


Definition preserve_order {X : Type} (K
  (f : forall n, set X -> K n -> set X)
  (g : prod_topology K -> X)
  (RT : forall n, K n -> K n -> bool) 
  (RX : X -> X -> bool) 
  (invar : set X -> Prop)
  :=
  (forall n U k1 k2, invar U -> k1 != k2 -> RT n k1 k2 -> lift_rel RX (f n U k1) (f n U k2)) ->
  (forall t1 t2, lexi_bigprod RT t1 t2 -> RX (g t1) (g t2)).


(**md**************************************************************************)
(* ## Part 1                                                                  *)
(*                                                                            *)
(* A tree here has countable levels, and nodes of type `K n` on the nth       *)
(* level.                                                                     *)
(* Each level is in the 'discrete' topology, so the nodes are independent.    *)
(* The goal is to build a map from branches to X.                             *)
(* 1. Each level of the tree corresponds to an approximation of `X`.          *)
(* 2. Each level refines the previous approximation.                          *)
(* 3. Then each branch has a corresponding Cauchy filter.                     *)
(* 4. The overall function from branches to X is a continuous surjection.     *)
(* 5. With an extra disjointness condition, this is also an injection         *)
(*                                                                            *)
(******************************************************************************)
Section topological_trees.
Context {K : nat -> ptopologicalType} {X : ptopologicalType}
        (refine_apx : forall n, set X -> K n -> set X)
        (tree_invariant : set X -> Prop).

Hypothesis cmptX : compact [set: X].
Hypothesis hsdfX : hausdorff_space X.
Hypothesis discreteK : forall n, discrete_space (K n).
Hypothesis refine_cover : forall n U, U = \bigcup_e @refine_apx n U e.
Hypothesis refine_invar : forall n U e,
  tree_invariant U -> tree_invariant (@refine_apx n U e).
Hypothesis invar_n0 : forall U, tree_invariant U -> U !=set0.
Hypothesis invarT : tree_invariant [set: X].
Hypothesis invar_cl : tree_invariant `<=` closed.
Hypothesis refine_separates: forall x y : X, x != y ->
  exists n, forall (U : set X) e,
    @refine_apx n U e x -> ~@refine_apx n U e y.

Let refine_subset n U e : @refine_apx n U e `<=` U.
Proof. by rewrite [X in _ `<=` X](refine_cover n); exact: bigcup_sup. Qed.

Let T := prod_topology K.

Local Fixpoint branch_apx (b : T) n :=
  if n is m.+1 then refine_apx (branch_apx b m) (b m) else [set: X].

Let tree_mapF b := filter_from [set: nat] (branch_apx b).

Let tree_map_invar b n : tree_invariant (branch_apx b n).
Proof. by elim: n => // n ?; exact: refine_invar. Qed.

Let tree_map_sub b i j : (i <= j)%N -> branch_apx b j `<=` branch_apx b i.
Proof.
elim: j i => [?|j IH i]; first by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /predU1P[->//|/IH].
by apply: subset_trans; exact: refine_subset.
Qed.

Instance tree_map_filter b : ProperFilter (tree_mapF b).
Proof.
split; first by case => n _ P; case: (invar_n0 (tree_map_invar b n)) => x /P.
apply: filter_from_filter; first by exists 0%N.
move=> i j _ _; exists (maxn i j)  => //; rewrite subsetI.
by split; apply: tree_map_sub; [exact: leq_maxl | exact: leq_maxr].
Qed.

Let tree_map b := lim (tree_mapF b).

Let cvg_tree_map b : cvg (tree_mapF b).
Proof.
have [|x [_ clx]] := cmptX (tree_map_filter b); first exact: filterT.
apply/cvg_ex; exists x => /=; apply: (compact_cluster_set1 _ cmptX) => //.
- exact: filterT.
- exact: filterT.
rewrite eqEsubset; split=> [y cly|? -> //].
have [->//|/refine_separates[n sep]] := eqVneq x y.
have bry : branch_apx b n.+1 y.
  have /closure_id -> := invar_cl (tree_map_invar b n.+1).
  by move: cly; rewrite clusterE; apply; exists n.+1.
suff /sep : branch_apx b n.+1 x by [].
have /closure_id -> := invar_cl (tree_map_invar b n.+1).
by move: clx; rewrite clusterE; apply; exists n.+1.
Qed.

Local Lemma tree_map_surj : set_surj [set: T] [set: X] tree_map.
Proof.
move=> z _; suff : exists g, forall n, branch_apx g n z.
  case=> g gnz; exists g => //; apply: close_eq => // U [oU Uz] V ngV; exists z.
  by split => //; have [n _] := @cvg_tree_map g _ ngV; exact.
have zcov' : forall n (U : set X), exists e, U z -> @refine_apx n U e z.
  move=> n U; have [|?] := pselect (U z); last by exists point.
  by rewrite [X in X z -> _](@refine_cover n U); case => e _ ?; exists e.
pose zcov n U := projT1 (cid (zcov' n U)).
pose fix g n : K n * set X :=
  if n is m.+1
  then (zcov m.+1 (g m).2, @refine_apx m.+1 (g m).2 (zcov m.+1 (g m).2))
  else (zcov O [set: X], @refine_apx O [set: X] (zcov O [set: X])).
pose g' n := (g n).1; have apxg n : branch_apx g' n.+1 = (g n).2.
  by elim: n => //= n ->.
exists g'; elim => // n /= IH.
have /(_ IH) := projT2 (cid (zcov' n (branch_apx g' n))).
by case: n {IH} => // n; rewrite apxg.
Qed.

Let apx_prefix b c n :
  (forall i, (i < n)%N -> b i = c i) -> branch_apx b n = branch_apx c n.
Proof.
elim: n => //= n IH inS; rewrite IH; first by rewrite inS.
by move=> ? ?; exact/inS/ltnW.
Qed.

Let tree_map_apx b n : branch_apx b n (tree_map b).
Proof.
apply: (@closed_cvg _ _ _ (tree_map_filter b)); last exact: cvg_tree_map.
  by apply: invar_cl; exact: tree_map_invar.
by exists n.
Qed.

Local Lemma tree_map_cts : continuous tree_map.
Proof.
move=> b U /cvg_tree_map [n _] /filterS; apply.
rewrite nbhs_simpl /=; near_simpl; have := tree_prefix b n; apply: filter_app.
by near=> z => /apx_prefix ->; exact: tree_map_apx.
Unshelve. all: end_near. Qed.

Let tree_map_setI x y n : tree_map x = tree_map y ->
  refine_apx (branch_apx x n) (x n) `&` refine_apx (branch_apx y n) (y n) !=set0.
Proof.
move=> xyE; exists (tree_map y); split.
  by rewrite -xyE -/(branch_apx x n.+1); exact: tree_map_apx.
by rewrite -/(branch_apx y n.+1); exact: tree_map_apx.
Qed.

Local Lemma tree_map_inj : (forall n U, trivIset [set: K n] (@refine_apx n U)) ->
  set_inj [set: T] tree_map.
Proof.
move=> triv x y _ _ xyE; apply: functional_extensionality_dep => n.
suff : forall n, branch_apx x n = branch_apx y n.
  move=> brE; apply: (@triv n (branch_apx x n) _ _ I I).
  by rewrite [in X in _ `&` X]brE; exact: tree_map_setI.
elim => // m /= brE.
rewrite (@triv m (branch_apx x m) (x m) (y m) I I) 1?brE//.
by rewrite -[in X in X `&` _]brE; exact: tree_map_setI.
Qed.

Local Lemma tree_map_mono RT RX : reflexive RX -> (forall n, reflexive (RT n)) ->
  @preserve_order K X refine_apx tree_map RT RX tree_invariant.
Proof.
move=> RXrefl RTrefl refine_ord t1 t2. 
rewrite /lexi_bigprod/first_diff.
case: xgetP => /=; first last.
  move=> fnE; suff -> : t1 = t2 by rewrite RXrefl.
  apply: functional_extensionality_dep.
  suff : forall n, forall x, x < n -> t1 x = t2 x.
    by move=> + n => /(_ n.+1)/(_ n); apply.
  elim; first by move=> ?.
  move=> n IH x; rewrite leq_eqVlt => /orP [/eqP/succn_inj ->|].
    have /forall2NP/(_ n) [] := fnE (Some n) => // /not_andP.
    case; last by move /negP; rewrite negbK => /eqP. 
    by case/existsNP => m /not_implyP [//] mx; apply: absurd; apply/eqP/IH.
  by move=> xn; apply: IH.
case => //; last by move=> + [//].
move=> n _ [? [+ +]] /Some_inj En; rewrite {}En => nmin t1nt2 t1Rt2.
apply: (@refine_ord n (branch_apx t1 n) (t1 n) (t2 n)) => //.
  exact: @tree_map_apx t1 n.+1.
suff -> : branch_apx t1 n = branch_apx t2 n.
  exact: @tree_map_apx t2 n.+1.
move: nmin {t1nt2} t1Rt2; elim: n => // n IH mn1 /= ?.
rewrite IH; first by congr (_ _ _); apply/eqP; apply: mn1.
  by move => m /ltnW/mn1.
suff -> : t1 n = t2 n by exact: RTrefl.
by apply/eqP; apply: mn1.
Qed.

Lemma tree_map_props : exists f : T -> X,
  [/\ continuous f,
      set_surj [set: T] [set: X] f &
      (forall n U, trivIset [set: K n] (@refine_apx n U)) ->
        set_inj [set: T] f].
Proof.
exists tree_map; split.
- exact: tree_map_cts.
- exact: tree_map_surj.
- exact: tree_map_inj.
Qed.

End topological_trees.

(**md**************************************************************************)
(* ## Part 2                                                                  *)
(* We can use `tree_map_props` to build a homeomorphism from the              *)
(* cantor_space to a Cantor-like space T.                                     *)
(******************************************************************************)

Section TreeStructure.
Context {R : realType} {T : pseudoPMetricType R}.
Hypothesis cantorT : cantor_like T.

Let dsctT : zero_dimensional T.   Proof. by case: cantorT. Qed.
Let pftT  : perfect_set [set: T]. Proof. by case: cantorT. Qed.
Let cmptT : compact [set: T].     Proof. by case: cantorT. Qed.
Let hsdfT : @hausdorff_space T.   Proof. by case: cantorT. Qed.

Let c_invar (U : set T) := clopen U /\ U !=set0.

Let U_ := unsquash (clopen_surj cmptT).

Let split_clopen' (U : set T) : exists V,
  open U -> U !=set0 -> [/\ clopen V, V `&` U !=set0 & ~`V `&` U !=set0].
Proof.
have [oU|?] := pselect (open U); last by exists point.
have [Un0|?] := pselect (U !=set0); last by exists point.
have [x [y] [Ux] Uy xny] := (iffLR perfect_set2) pftT U oU Un0.
have [V [clV Vx Vy]] := dsctT xny; exists V => _ _.
by split => //; [exists x | exists y].
Qed.

Let split_clopen (U : set T) := projT1 (cid (split_clopen' U)).

Let c_ind n (V : set T) (b : bool) :=
  let Wn :=
    if pselect ((U_ n) `&` V !=set0 /\ ~` (U_ n) `&` V !=set0)
    then U_ n else split_clopen V in
  (if b then Wn else ~` Wn) `&` V.

Local Lemma cantor_map : exists f : cantor_space -> T,
  [/\ continuous f,
      set_surj [set: cantor_space] [set: T] f &
      set_inj [set: cantor_space] f ].
Proof.
have [] := @tree_map_props
    (fun=> discrete_topology discrete_bool) T c_ind c_invar cmptT hsdfT.
- by move=> ?; exact: discrete_space_discrete.
- move=> n V; rewrite eqEsubset; split => [t Vt|t [? ? []]//].
  have [?|?] := pselect (U_ n `&` V !=set0 /\ ~` U_ n `&` V !=set0).
  + have [Unt|Unt] := pselect (U_ n t).
    * by exists true => //; rewrite /c_ind; case: pselect.
    * by exists false => //; rewrite /c_ind; case: pselect.
  + have [scVt|scVt] := pselect (split_clopen V t).
    * by exists true => //; rewrite /c_ind; case: pselect.
    * by exists false => //; rewrite /c_ind; case: pselect.
- move=> n U e [] clU Un0; rewrite /c_ind; case: pselect => /=.
  + move=> [UU CUU]; case: e => //; split => //; apply: clopenI => //.
      exact: funS.
    by apply: clopenC => //; exact: funS.
  + move=> _; have [|//|clscU scUU CscUU] := projT2 (cid (split_clopen' U)).
      by case: clU.
    case: e; split => //; first exact: clopenI.
    by apply: clopenI => //; exact: clopenC.
- by move=> ? [].
- by split; [exact: clopenT | exists point].
- by move=> ? [[]].
- move=> x y /dsctT [A [clA Ax Any]].
  have [n _ UnA] := @surj _ _ _ _ U_ _ clA; exists n => V e.
  have [|+ _] := pselect (V y); last by apply: subsetC => ? [].
  have [Vx Vy|? _ []//] := pselect (V x).
  rewrite {1 2}/c_ind; case: pselect => /=; rewrite ?UnA.
    by move=> _; case: e; case => // ? ?; apply/not_andP; left.
  by apply: absurd; split; [exists x | exists y].
- move=> f [ctsf surjf injf]; exists f; split => //.
  apply: injf.
  by move=> n U i j _ _ [z] [] [] + Uz [+ _]; move: i j => [] [].
Qed.

Let tree_map := projT1 (cid cantor_map).

Let tree_map_bij : bijective tree_map.
Proof.
by rewrite -setTT_bijective; have [? ? ?] := projT2 (cid cantor_map); split.
Qed.

#[local] HB.instance Definition _ := @BijTT.Build _ _ _ tree_map_bij.

Lemma homeomorphism_cantor_like :
  exists f : {splitbij [set: cantor_space] >-> [set: T]},
    continuous f /\ (forall A, closed A -> closed (f @` A)).
Proof.
exists [the {splitbij _ >-> _} of tree_map] => /=.
have [cts surj inje] := projT2 (cid cantor_map); split; first exact: cts.
move=> A clA; apply: (compact_closed hsdfT).
apply: (@continuous_compact _ _ tree_map); first exact: continuous_subspaceT.
apply: (@subclosed_compact _ _ [set: cantor_space]) => //.
exact: cantor_space_compact.
Qed.

End TreeStructure.

(**md**************************************************************************)
(* ## Part 3: Finitely branching trees are Cantor-like                        *)
(******************************************************************************)
Section FinitelyBranchingTrees.

Definition tree_of (T : nat -> pointedType) : Type :=
  prod_topology (fun n =>  discrete_topology_type (T n)).

HB.instance Definition _ (T : nat -> pointedType) : Pointed (tree_of T):= 
  Pointed.on (tree_of T).

HB.instance Definition _ (T : nat -> pointedType) := Uniform.on (tree_of T).

HB.instance Definition _ {R : realType} (T : nat -> pointedType) : 
    @PseudoMetric R _ :=
   @PseudoMetric.on (tree_of T).

Lemma cantor_like_finite_prod (T : nat -> ptopologicalType) :
  (forall n, finite_set [set: discrete_topology_type (T n)]) ->
  (forall n, (exists xy : T n * T n, xy.1 != xy.2)) ->
  cantor_like (tree_of T).
Proof.
move=> finiteT twoElems; split.
- exact/(@perfect_diagonal (discrete_topology_type \o T))/twoElems.
- have := tychonoff (fun n => finite_compact (finiteT n)).
  set A := (X in compact X -> _).
  suff : A = [set: tree_of (fun x : nat => T x)] by move=> ->.
  by rewrite eqEsubset.
- apply: (@hausdorff_product _ (discrete_topology_type \o T)) => n.
  by apply: discrete_hausdorff; exact: discrete_space_discrete.
- apply: zero_dimension_prod => ?; apply: discrete_zero_dimension.
  exact: discrete_space_discrete.
Qed.

End FinitelyBranchingTrees.

(**md**************************************************************************)
(* ## Part 4: Building a finitely branching tree to cover `T`                 *)
(******************************************************************************)
Section alexandroff_hausdorff.
Context {R : realType} {T : pseudoPMetricType R}.

Hypothesis cptT : compact [set: T].
Hypothesis hsdfT : hausdorff_space T.

Section two_pointed.
Context (t0 t1 : T).
Hypothesis T2e : t0 != t1.

Let ent_balls' (E : set (T * T)) :
  exists M : set (set T), entourage E -> [/\
    finite_set M,
    forall A, M A -> exists a, A a /\
      A `<=` closure (xsection (split_ent E) a),
    exists A B : set T, M A /\ M B /\ A != B,
    \bigcup_(A in M) A = [set: T] &
    M `<=` closed].
Proof.
have [entE|?] := pselect (entourage E); last by exists point.
move: cptT; rewrite compact_cover.
pose fs x := interior (xsection (split_ent E) x).
move=> /(_ T [ set: T] fs)[t _|t _ |].
- exact: open_interior.
- exists t => //; rewrite /fs /interior.
  by rewrite -nbhs_entourageE; exists (split_ent E) => // ? /xsectionP.
move=> M' _ Mcov; exists
  ((closure \o fs) @` [set` M'] `|` [set [set t0]; [set t1]]).
move=> _; split=> [|A [|]| | |].
- rewrite finite_setU; split; first exact/finite_image/finite_fset.
  exact: finite_set2.
- move=> [z M'z] <-; exists z; split.
  + apply: subset_closure; apply: nbhs_singleton; apply: nbhs_interior.
      by rewrite -nbhs_entourageE; exists (split_ent E) => // t /xsectionP.
  + by apply: closure_subset; exact: interior_subset.
- by case => ->; [exists t0 | exists t1]; split => // t ->;
    apply/subset_closure/xsectionP; exact: entourage_refl.
- exists [set t0], [set t1]; split;[|split].
  + by right; left.
  + by right; right.
  + apply/eqP; rewrite eqEsubset => -[] /(_ t0 erefl).
    by move: T2e => /[swap] -> /eqP.
- rewrite -subTset => t /Mcov [t' M't' fsxt]; exists (closure (fs t')).
    by left; exists t'.
  exact: subset_closure.
- move=> ? [[? ?] <-|]; first exact: closed_closure.
  by move=> [|] ->; exact/accessible_closed_set1/hausdorff_accessible.
Qed.

Let ent_balls E := projT1 (cid (ent_balls' E)).

Let count_unif' := cid2
  ((iffLR countable_uniformityP) (@countable_uniformity_metric _ T)).

Let count_unif := projT1 count_unif'.

Let ent_count_unif n : entourage (count_unif n).
Proof.
have := projT2 (cid (ent_balls' (count_unif n))).
rewrite /count_unif; case: count_unif'.
by move=> /= f fnA fnE; case /(_ (fnE _)) => _ _ _ + _; rewrite -subTset.
Qed.

Let count_unif_sub E : entourage E -> exists N, count_unif N `<=` E.
Proof.
by move=> entE; rewrite /count_unif; case: count_unif' => f + ? /=; exact.
Qed.

Let K' n : Type := @sigT (set T) (ent_balls (count_unif n)).

Let K'p n : K' n.
Proof.
apply: cid; have [//| _ _ _ + _] := projT2 (cid (ent_balls' (count_unif n))).
by rewrite -subTset => /(_ point I) [W Q ?]; exists W; exact: Q.
Qed.

HB.instance Definition _ n := gen_eqMixin (K' n).
HB.instance Definition _ n := gen_choiceMixin (K' n).
HB.instance Definition _ n := isPointed.Build (K' n) (K'p n).

Let K n := K' n.
Let Tree := @tree_of K.

Let embed_refine n (U : set T) (k : K n) :=
  (if pselect (projT1 k `&` U !=set0)
  then projT1 k
  else if pselect (exists e : K n , projT1 e `&` U !=set0) is left e
    then projT1 (projT1 (cid e))
    else set0) `&` U.
Let embed_invar (U : set T) := closed U /\ U !=set0.

Let Kn_closed n (e : K n) : closed (projT1 e).
Proof.
case: e => W; have [//| _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
exact.
Qed.

Let discrete_subproof (P : choiceType) :
  discrete_space (principal_filter_type P).
Proof. by []. Qed.

Local Lemma cantor_surj_pt1 : exists2 f : Tree -> T,
  continuous f & set_surj [set: Tree] [set: T] f.
Proof.
pose entn n := projT2 (cid (ent_balls' (count_unif n))).
have [//| | |? []//| |? []// | |] := @tree_map_props
    (discrete_topology_type \o K) T (embed_refine) (embed_invar) cptT hsdfT.
- by move=> n; exact: discrete_space_discrete.
- move=> n U; rewrite eqEsubset; split=> [t Ut|t [? ? []]//].
  have [//|_ _ _ + _] := entn n; rewrite -subTset.
  move=> /(_ t I)[W cbW Wt]; exists (existT _ W cbW) => //.
  by rewrite /embed_refine; case: pselect => //=; apply: absurd; exists t.
- move=> n U e [clU Un0]; split.
    apply: closedI => //; case: pselect => //= ?.
    by case: pselect => ?; [exact: Kn_closed|exact: closed0].
  rewrite /embed_refine; case: pselect => //= ?; case: pselect.
    by case=> i [z [pz bz]]; set P := cid _; have := projT2 P; apply.
  case: Un0 => z Uz; apply: absurd.
  have [//|_ _ _ + _] := entn n; rewrite -subTset; move=> /(_ z I)[i bi iz].
  by exists (existT _ _ bi), z.
- by split; [exact: closedT | exists point].
- move=> x y xny; move: hsdfT; rewrite open_hausdorff.
  move=> /(_ _ _ xny)[[U V]] /= [/set_mem Ux /set_mem Vy] [+ oV UVI0].
  rewrite openE => /(_ _ Ux); rewrite /interior -nbhs_entourageE => -[E entE ExU].
  have [//| n ctE] :=
    @count_unif_sub (split_ent E `&` (split_ent E)^-1%relation).
    exact: filterI.
  exists n => B [C ebC]; have [//|_ Csub _ _ _ embx emby] := entn n.
  have [[D cbD] /= Dx Dy] : exists2 e : K n, projT1 e x & projT1 e y.
    move: embx emby; rewrite /embed_refine; case: pselect => /=.
      by move=> ? [? ?] [? ?]; exists (existT _ _ ebC).
    case: pselect; last by move => ? ? [].
    by move=> e _ [? ?] [? ?]; exists (projT1 (cid e)).
  suff : E (x, y).
    by move/xsectionP/ExU; move/eqP/disjoints_subset: UVI0 => /[apply].
  have [z [Dz DzE]] := Csub _ cbD.
  have /ent_closure := DzE _ Dx => /(_ (ent_count_unif n))/xsectionP/ctE [_ /= Exz].
  have /ent_closure := DzE _ Dy => /(_ (ent_count_unif n))/xsectionP/ctE [Ezy _].
  exact: (@entourage_split _ (*[the uniformType of T]*) z).
by move=> f [ctsf surjf _]; exists f.
Qed.

Local Lemma cantor_surj_pt2 :
  exists f : {surj [set: cantor_space] >-> [set: Tree]}, continuous f.
Proof.
have [|f [ctsf _]] := @homeomorphism_cantor_like R Tree; last by exists f.
apply: (@cantor_like_finite_prod (discrete_topology_type \o K)) => [n /=|n].
  have [//| fs _ _ _ _] := projT2 (cid (ent_balls' (count_unif n))).
  suff -> : [set: {classic K' n}] =
      (@projT1 (set T) _) @^-1` (projT1 (cid (ent_balls' (count_unif n)))).
    by apply: finite_preimage => // ? ? _ _; exact: eq_sigT_hprop.
  by rewrite eqEsubset; split => // -[].
have [//| _ _ [A [B [pA [pB AB]]]] _ _] :=
  projT2 (cid (ent_balls' (count_unif n))).
exists (existT _ _ pA, existT _ _ pB) => /=.
by move: AB; apply: contra_neq => -[].
Qed.

Local Lemma cantor_surj_twop :
  exists f : {surj [set: cantor_space] >-> [set: T]}, continuous f.
Proof.
move: cantor_surj_pt2 cantor_surj_pt1 => -[f ctsf] [g ctsg /Psurj[sjg gsjg]].
exists [surj of sjg \o f] => z.
by apply continuous_comp; [exact: ctsf|rewrite -gsjg; exact: ctsg].
Qed.

End two_pointed.

(** The Alexandroff-Hausdorff theorem *)
Theorem cantor_surj :
  exists f : {surj [set: cantor_space] >-> [set: T]}, continuous f.
Proof.
have [[p ppt]|/forallNP xpt] := pselect (exists p : T, p != point).
  by apply: cantor_surj_twop; exact: ppt.
have /Psurj[f cstf] : set_surj [set: cantor_space] [set: T] (cst point).
  by move=> q _; exists point => //; have /negP/negPn/eqP -> := xpt q.
by exists f; rewrite -cstf; exact: cst_continuous.
Qed.

End alexandroff_hausdorff.
