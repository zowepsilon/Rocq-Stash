From Stdlib Require Import Setoids.Setoid.
From Stdlib Require Import Program.

Require Import Stdlib.Logic.ProofIrrelevance.

Record Category := {
    Obj :> Type;
    Hom: Obj -> Obj -> Type;
    comp: forall {A B C: Obj}, Hom B C -> Hom A B -> Hom A C;
    comp_assoc:
      forall {A0 B0 C0 D0: Obj},
      forall (f: Hom C0 D0),
      forall (g: Hom B0 C0),
      forall (h: Hom A0 B0),
      comp (comp f g) h = comp f (comp g h);
    id : forall (A: Obj), Hom A A;
    comp_id_left: forall (A B: Obj), forall (f: Hom A B), comp (id B) f = f;
    comp_id_right: forall (A B: Obj), forall (f: Hom A B), comp f (id A) = f;
}.

Definition Op (C: Category): Category := {|
    Obj := C.(Obj);
    Hom A B := C.(Hom) B A;
    comp _ _ _ g f := C.(comp) f g;
    comp_assoc _ _ _ _ f g h := eq_sym (C.(comp_assoc) h g f);
    id := C.(id);
    comp_id_left A B f := (comp_id_right C) B A f;
    comp_id_right A B f := (comp_id_left C) B A f;
|}.

Definition Inverses {C: Category} {A B: C} (f: (Hom C) A B) (g: (Hom C) B A) :=
  ((comp C) g f = (id C) A) /\ ((comp C) f g = (id C) B).

Definition Isomorphism {C: Category} {A B: C} (f: (Hom C) A B) :=
  exists (g: (Hom C) B A), Inverses f g.

Lemma iso_id: forall (C: Category) (A: C),
    Isomorphism ((id C) A).
Proof.
  intros.
  unfold Isomorphism.
  destruct C.
  set (IdA := id0 A).
  exists IdA.
  split;trivial.
Qed.

Lemma iso_comp: forall (C: Category) (X Y Z: C) (f: (Hom C) X Y) (g: (Hom C) Y Z),
    Isomorphism f -> Isomorphism g -> Isomorphism (comp C g f).
Proof.
  intros C X Y Z f g fI gI.
  unfold Isomorphism in *.
  destruct fI as [f' [fI_left fI_right]].
  destruct gI as [g' [gI_left gI_right]].
  exists ((comp C) f' g').
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

Definition Isomorphic {C: Category} (A B: C) :=
  exists (f: (Hom C) A B), Isomorphism f.

Lemma iso_refl: forall (C: Category), forall A:C, Isomorphic A A.
Proof.
  intros C A.
  unfold Isomorphic.
  exists ((id C) A).
  exists ((id C) A).
  split.
  - apply ((comp_id_left C) A A).
  - apply ((comp_id_left C) A A).
Qed.

Lemma iso_sym: forall (C: Category) (X Y: C), Isomorphic X Y -> Isomorphic Y X.
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

Lemma iso_trans: forall (C: Category) (X Y Z: C), Isomorphic X Y -> Isomorphic Y Z -> Isomorphic X Z.
Proof.
  intros C X Y Z IsoXY IsoYZ.
  unfold Isomorphic in *.
  destruct IsoXY as [xy IsoXY].
  destruct IsoYZ as [yz IsoYZ].
  exists ((comp C) yz xy).
  apply iso_comp.
  trivial. trivial.
Qed.

Lemma iso_in_op: forall (C: Category), forall (A B: C), @Isomorphic C A B <-> @Isomorphic (Op C) A B.
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

Definition Initial {C: Category} (A0: C) :=
  forall (A: C), exists (f: (Hom C) A0 A), forall (f': (Hom C) A0 A), f = f'.

Theorem uniq_initial:
  forall (C: Category) (A B: C), Initial A -> Initial B -> Isomorphic A B.
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
  specialize (uniq_id_A (id C A)) as uniq_id_A_id.
  specialize (uniq_id_B (id C B)) as uniq_id_B_id.
  rewrite uniq_id_A_id in uniq_id_A.
  rewrite uniq_id_B_id in uniq_id_B.
  split.
  - specialize (uniq_id_A (comp C g f)).
    symmetry.
    assumption.
  - specialize (uniq_id_B (comp C f g)).
    symmetry.
    assumption.
Qed.

Definition Final {C: Category} (A0: C) := @Initial (Op C) A0.

Theorem uniq_final:
  forall (C: Category) (A B: C), Final A -> Final B -> Isomorphic A B.
Proof.
  intros C A B FA FB.
  apply iso_in_op.
  apply uniq_initial.
  trivial. trivial.
Qed.

Class Product {C: Category} (A B: C) := {
  obj: Obj C;

  proj1: Hom C obj A;
  proj2: Hom C obj B;

  univ: forall (X: C) (f: Hom C X A) (g: Hom C X B), exists! (u: Hom C X obj),
               comp C proj1 u = f /\ comp C proj2 u = g;
}.

Lemma id_as_product_hom: forall (C: Category) (A B: C) (P: Product A B),
    comp C proj1 (id C obj) = proj1 /\ comp C proj2 (id C obj) = proj2.
Proof.
  intros.
  split.
  - apply comp_id_right.
  - apply comp_id_right.
Qed.


Theorem unique_product: forall (C: Category) (A B: C) (P Q: Product A B), Isomorphic P.(obj) Q.(obj).
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

  specialize (uniqPP (id C P.(obj)) (id_as_product_hom C A B P)) as uniqPP_id.
  specialize (uniqQQ (id C Q.(obj)) (id_as_product_hom C A B Q)) as uniqQQ_id.
  rewrite uniqPP_id in uniqPP.
  rewrite uniqQQ_id in uniqQQ.

  destruct univPQ as [univPQ1 univPQ2].
  destruct univQP as [univQP1 univQP2].

  split.
  - symmetry.
    apply (uniqPP (comp C qp pq)).
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
    apply (uniqQQ (comp C pq qp)).
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

  F_id: forall (A: C.(Obj)), F_Hom (id C A) = id D (F_Obj A);
  F_comp: forall (X Y Z: C.(Obj)) (f: C.(Hom) X Y) (g: C.(Hom) Y Z), F_Hom (C.(comp) g f) = D.(comp) (F_Hom g) (F_Hom f);
}.

Instance functor_id (C: Category): Functor C C := {
    F_Obj A := A;
    F_Hom _ _ f := f;
    F_id _ := eq_refl;
    F_comp _ _ _ _ _ := eq_refl;
}.

Lemma functor_comp_id:
  forall (C D E: Category) (F: Functor C D) (G: Functor D E) (A : C),
    (compose G.(F_Hom) F.(F_Hom)) (id C A) = id E ((compose G.(F_Obj) F.(F_Obj)) A).
Proof.
  intros.
  unfold compose.
  rewrite F.(F_id).
  rewrite G.(F_id).
  reflexivity.
Qed.

Lemma functor_comp_comp:
  forall (C D E: Category) (F: Functor C D) (G: Functor D E) (X Y Z: C) (f: Hom C X Y) (g: Hom C Y Z),
    (compose G.(F_Hom) F.(F_Hom)) (C.(comp) g f)
    = E.(comp) ((compose G.(F_Hom) F.(F_Hom)) g) ((compose G.(F_Hom) F.(F_Hom)) f).
Proof.
  intros.
  unfold compose.
  rewrite F.(F_comp).
  rewrite G.(F_comp).
  reflexivity.
Qed.

Instance functor_comp {C D E: Category} (F: Functor C D) (G: Functor D E): Functor C E := {
  F_Obj := compose G.(F_Obj) F.(F_Obj);
  F_Hom _ _ := compose G.(F_Hom) F.(F_Hom);
  F_id := functor_comp_id _ _ _ _ _;
  F_comp := functor_comp_comp _ _ _ _ _;
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

Class NatTrans {C D: Category} (F G: Functor C D) := {
  nt: forall (A: C), Hom D (F.(F_Obj) A) (G.(F_Obj) A);
  nt_naturality: forall (A B: C) (f: Hom C A B),
    comp D (F_Hom f) (nt A) = comp D (nt B) (F_Hom f);
}.

Definition NatIsomorphism {C D: Category} {F G: Functor C D} (a: NatTrans F G) :=
  exists (b: NatTrans G F), forall (A: C), Inverses (a.(nt) A) (b.(nt) A).

Theorem C_op_op_is_C: forall (C: Category), Op (Op C) = C.
Proof.
  intro.
  set (D := Op (Op C)).
  destruct C.
  destruct D.
  simpl.
Admitted.

Definition monomorphism {C : Category} {E F : C} (f : Hom C E F) :=
  forall G : C, forall g h : Hom C G E, comp C f g = comp C f h -> g = h.

Definition epimorphism {C : Category} {E F : C} (f : Hom C E F) :=
  forall G : C, forall g h : Hom C F G, comp C g f = comp C h f -> g = h.

Theorem id_mono :
  forall (C : Category), forall (A : C), monomorphism (id C A).
Proof.
  intros.
  unfold monomorphism.
  intros.
  now repeat rewrite comp_id_left in H.
Qed.

Theorem id_epi :
  forall (C : Category), forall (A : C), epimorphism (id C A).
Proof.
  intros.
  unfold epimorphism.
  intros.
  now repeat rewrite comp_id_right in H.
Qed.