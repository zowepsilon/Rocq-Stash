From Stdlib Require Import Setoids.Setoid.

Class Category := {
    Obj: Type;
    Hom: Obj -> Obj -> Type;
    comp: forall {A B C: Obj}, Hom B C -> Hom A B -> Hom A C;
    comp_assoc:
      forall {A0 B0 C0 D0: Obj},
      forall (f: Hom C0 D0),
      forall (g: Hom B0 C0),
      forall (h: Hom A0 B0),
      comp (comp f g) h = comp f (comp g h);
    id: forall (A: Obj), Hom A A;
    comp_id_left: forall (A B: Obj), forall (f: Hom A B), comp (id B) f = f;
    comp_id_right: forall (A B: Obj), forall (f: Hom A B), comp f (id A) = f;
}.

Instance Op (C: Category): Category := {
    Obj := C.(Obj);
    Hom A B := C.(Hom) B A;
    comp _ _ _ g f := C.(comp) f g;
    comp_assoc _ _ _ _ f g h := eq_sym (C.(comp_assoc) h g f);
    id := C.(id);
    comp_id_left A B f := comp_id_right B A f;
    comp_id_right A B f := comp_id_left B A f;
}.

Definition Isomorphism {C: Category} {A B: Obj} (f: Hom A B) :=
  exists (g: Hom B A), (comp g f = id A) /\ (comp f g = id B).

Lemma iso_id: forall (C: Category) (A: Obj),
    Isomorphism (id A).
Proof.
  intros.
  unfold Isomorphism.
  destruct C.
  set (IdA := id0 A).
  exists IdA.
  split;trivial.
Qed.

Lemma iso_comp: forall (C: Category) (X Y Z: Obj) (f: Hom X Y) (g: Hom Y Z),
    Isomorphism f -> Isomorphism g -> Isomorphism (comp g f).
Proof.
  intros C X Y Z f g fI gI.
  unfold Isomorphism in *.
  destruct fI as [f' [fI_left fI_right]].
  destruct gI as [g' [gI_left gI_right]].
  exists (comp f' g').
  split.
  - setoid_rewrite -> comp_assoc at 1.
    setoid_rewrite <- comp_assoc at 2.
    rewrite -> gI_left.
    rewrite comp_id_left.
    rewrite -> fI_left.
    reflexivity.
  - setoid_rewrite -> comp_assoc at 1.
    setoid_rewrite <- comp_assoc at 2.
    rewrite -> fI_right.
    rewrite comp_id_left.
    rewrite -> gI_right.
    reflexivity.
Qed.

Definition Isomorphic {C: Category} (A B: Obj) :=
  exists (f: Hom A B), Isomorphism f.

Lemma iso_refl: forall (C: Category), forall A, Isomorphic A A.
Proof.
  intros C A.
  unfold Isomorphic.
  exists (id A).
  exists (id A).
  split.
  - apply (comp_id_left A A).
  - apply (comp_id_left A A).
Qed.

Lemma iso_sym: forall (C: Category) (X Y: Obj), Isomorphic X Y -> Isomorphic Y X.
Proof.
  intros C X Y IsoXY.
  unfold Isomorphic in *.
  unfold Isomorphism.
  destruct IsoXY as [xy [yx [IsoXY IsoYX]]].
  exists yx.
  exists xy.
  split.
  apply IsoYX.
  apply IsoXY.
Qed.

Lemma iso_trans: forall (C: Category) (X Y Z: Obj), Isomorphic X Y -> Isomorphic Y Z -> Isomorphic X Z.
Proof.
  intros C X Y Z IsoXY IsoYZ.
  unfold Isomorphic in *.
  destruct IsoXY as [xy IsoXY].
  destruct IsoYZ as [yz IsoYZ].
  exists (comp yz xy).
  apply iso_comp.
  trivial. trivial.
Qed.

Lemma iso_in_op: forall (C: Category), forall (A B: Obj), @Isomorphic C A B <-> @Isomorphic (Op C) A B.
Proof.
  intros C A B.
  unfold Isomorphic.
  unfold Isomorphism.
  simpl.
  split.
  - intro H. destruct H as [f [g [invleft invright]]].
    exists g. exists f.
    split. trivial. trivial.
  - intro H. destruct H as [f [g [invleft invright]]].
    exists g. exists f.
    split. trivial. trivial.
Qed.

Definition Initial {C: Category} (A0: Obj) :=
  forall (A: Obj), exists (f: Hom A0 A), forall (f': Hom A0 A), f = f'.

Theorem uniq_initial:
  forall (C: Category) (A B: Obj), Initial A -> Initial B -> Isomorphic A B.
Proof.
  intros C A B IA IB.
  unfold Initial in IA.
  unfold Initial in IB.
  unfold Isomorphic.
  destruct (IA B) as [f _].
  destruct (IB A) as [g _].
  exists f.
  exists g.
  destruct (IA A) as [id_A uniq_id_A].
  destruct (IB B) as [id_B uniq_id_B].
  specialize (uniq_id_A (id A)) as uniq_id_A_id.
  specialize (uniq_id_B (id B)) as uniq_id_B_id.
  rewrite uniq_id_A_id in uniq_id_A.
  rewrite uniq_id_B_id in uniq_id_B.
  split.
  - specialize (uniq_id_A (comp g f)).
    symmetry.
    assumption.
  - specialize (uniq_id_B (comp f g)).
    symmetry.
    assumption.
Qed.

Definition Final {C: Category} (A0: Obj) := @Initial (Op C) A0.

Theorem uniq_final:
  forall (C: Category) (A B: Obj), Final A -> Final B -> Isomorphic A B.
Proof.
  intros C A B FA FB.
  apply iso_in_op.
  apply uniq_initial.
  trivial. trivial.
Qed.

Class Product {C: Category} (A B: Obj) := {
  obj: Obj;

  proj1: Hom obj A;
  proj2: Hom obj B;

  univ: forall (X: Obj) (f: Hom X A) (g: Hom X B), exists! (u: Hom X obj),
               comp proj1 u = f /\ comp proj2 u = g;
}.

Lemma id_as_product_hom: forall (C: Category) (A B: Obj) (P: Product A B),
    comp proj1 (id obj) = proj1 /\ comp proj2 (id obj) = proj2.
Proof.
  intros.
  split.
  - apply comp_id_right.
  - apply comp_id_right.
Qed.


Theorem unique_product: forall (C: Category) (A B: Obj) (P Q: Product A B), Isomorphic P.(obj) Q.(obj).
Proof.
  intros C A B P Q.

  specialize (P.(univ) P.(obj) P.(proj1) P.(proj2)) as univPP.
  specialize (Q.(univ) Q.(obj) Q.(proj1) Q.(proj2)) as univQQ.
  specialize (Q.(univ) P.(obj) P.(proj1) P.(proj2)) as univPQ.
  specialize (P.(univ) Q.(obj) Q.(proj1) Q.(proj2)) as univQP.

  destruct univPP as [pp [univPP uniqPP]].
  destruct univQQ as [qq [univQQ uniqQQ]].
  destruct univPQ as [pq [univPQ _]].
  destruct univQP as [qp [univQP _]].

  unfold Isomorphic.

  exists pq.
  exists qp.

  specialize (uniqPP (id P.(obj)) (id_as_product_hom C A B P)) as uniqPP_id.
  specialize (uniqQQ (id Q.(obj)) (id_as_product_hom C A B Q)) as uniqQQ_id.
  rewrite uniqPP_id in uniqPP.
  rewrite uniqQQ_id in uniqQQ.

  destruct univPQ as [univPQ1 univPQ2].
  destruct univQP as [univQP1 univQP2].

  split.
  - symmetry.
    apply (uniqPP (comp qp pq)).
    split.
    + rewrite <- comp_assoc.
      rewrite -> univQP1.
      rewrite -> univPQ1.
      reflexivity.
    + rewrite <- comp_assoc.
      rewrite univQP2.
      rewrite univPQ2.
      reflexivity.
  - symmetry.
    apply (uniqQQ (comp pq qp)).
    split.
    + rewrite <- comp_assoc.
      rewrite -> univPQ1.
      rewrite -> univQP1.
      reflexivity.
    + rewrite <- comp_assoc.
      rewrite univPQ2.
      rewrite univQP2.
      reflexivity.
Qed.

Class Functor (C D: Category) := {
  F_Obj: C.(Obj) -> D.(Obj);
  F_Hom: forall {A B: C.(Obj)}, C.(Hom) A B -> D.(Hom) (F_Obj A) (F_Obj B);

  F_id: forall (A: C.(Obj)), F_Hom (id A) = id (F_Obj A);
  F_comp: forall (X Y Z: C.(Obj)) (f: C.(Hom) X Y) (g: C.(Hom) Y Z), F_Hom (C.(comp) g f) = D.(comp) (F_Hom g) (F_Hom f);
}.

Theorem functor_preserve_iso:
  forall (C D: Category) (F: Functor C D) (A B: C.(Obj)), @Isomorphic C A B -> @Isomorphic D (F_Obj A) (F_Obj B).
Proof.
  intros C D F A B IAB.
  unfold Isomorphic in *.
  unfold Isomorphism in *.
  destruct IAB as [f [g [invLeft invRight]]].
  exists (F_Hom f).
  exists (F_Hom g).
  split.
  - rewrite <- F_comp.
    rewrite <- F_id.
    f_equal.
    trivial.
  - rewrite <- F_comp.
    rewrite <- F_id.
    f_equal.
    trivial.
Qed.
