(*Imports*)

From Coq Require Import Program.Tactics.

From Coq Require Import Setoids.Setoid. 

(*Content*)

Class Category := {
    (*data*)
    C_obj: Type;
    C_hom: C_obj -> C_obj -> Type;
    C_comp: forall {A B C: C_obj}, C_hom B C -> C_hom A B -> C_hom A C;
    
    (*constraints*)
    C_comp_assoc:
        forall {A B C D: C_obj},
        forall (f: C_hom C D),
        forall (g: C_hom B C),
        forall (h: C_hom A B),
        C_comp (C_comp f g) h = C_comp f (C_comp g h);
    C_id: forall (A: C_obj), C_hom A A;
    C_comp_id_left: forall (A B: C_obj), forall (f: C_hom A B), C_comp (C_id B) f = f;
    C_comp_id_right: forall (A B: C_obj), forall (f: C_hom A B), C_comp f (C_id A) = f;
}.

(*TODO : Set, Grp, Top, Poset...*)
(*TODO : Catégorie à partir d'un anneau unitaire*)
(*TODO : Enveloppe de Karoubi*)

Class Functor (C D : Category) := {
    (*data*)
    F_obj : C.(C_obj) -> D.(C_obj);
    F_hom : forall {A B : C.(C_obj)},
        C.(C_hom) A B -> D.(C_hom) (F_obj A) (F_obj B);

    (*constraints*)
    F_id: forall (A : C.(C_obj)),
        F_hom (C.(C_id) A) = D.(C_id) (F_obj A);
    F_comp :
        forall {A B E : C.(C_obj)}
               (g : C.(C_hom) B E) (f : C.(C_hom) A B),
          F_hom (C.(C_comp) g f)
          = D.(C_comp) (F_hom g) (F_hom f)
}.

(*TODO : foncteur identité*)

Definition id_functor (C : Category) : Functor C C := {|
    F_obj := fun A => A;
    F_hom := fun _ _ f => f;
    F_id  := fun _ => eq_refl;
    F_comp := fun _ _ _ _ _ => eq_refl
|}.

(*TODO : foncteur d'oubli Grp -> Set*)
(*TODO : List foncteur sur Type*)
(*TODO : application croissante sur les Poset*)

(*Catégorie opposée*)
Program Definition Opp (C : Category) : Category := {|
    C_obj := C.(C_obj);
    C_hom A B := C.(C_hom) B A;                (* on renverse le sens *)
    C_comp _ _ _ f g := C.(C_comp) g f;        (* composition renversée *)
    C_id A := C.(C_id) A
|}.
Next Obligation.
    now rewrite C.(C_comp_assoc).
Qed.
Next Obligation.
    now rewrite C.(C_comp_id_right).
Qed.
Next Obligation.
    now rewrite C.(C_comp_id_left).
Qed.

(*TODO : Si C est abélienne C ressemble à C^op*)

(*TODO : C^op^op = C*)

(*TODO : D(F(X), G(Y)) = D^op(G^op(Y), F^op(X))*)

(*TODO : bifoncteurs ?*)

Definition is_inverse {C: Category} {A B : C.(C_obj)} (f : C.(C_hom) A B) (g : C.(C_hom) B A) : Prop :=
    C.(C_comp) f g = C.(C_id) B /\ C.(C_comp) g f = C.(C_id) A.

Definition is_iso {C : Category} {A B : C.(C_obj)} (f : C.(C_hom) A B) : Prop :=
    exists (g : C.(C_hom) B A), is_inverse f g.

Definition iso {C: Category} {A B : C.(C_obj)} : Prop :=
    exists f : C.(C_hom) A B, is_iso f.

(*un foncteur préserve les isomorphismes*)
Theorem functor_preserves_isomorphism : (
    forall C D : Category,
    forall F : Functor C D,
    forall A B : C.(C_obj),
    @iso C A B -> @iso D (F.(F_obj) A) (F.(F_obj) B)
).
Proof.
    intros.
    unfold iso in *.
    destruct H as [f Pf].
    destruct F.
    set (f' := F_hom0 A B f).
    exists f'.
    unfold is_iso.
    unfold is_iso in *.
    destruct Pf as [j Pj].
    set (j' := F_hom0 B A j).
    exists j'.
    unfold is_inverse in *.
    simpl.
    destruct Pj.
    unfold f', j'.
    split.
    pose proof (f_equal (F_hom0 B B) H) as Hmap.
    rewrite (F_comp0 B A B f j) in Hmap.
    rewrite (F_id0 B) in Hmap.
    exact Hmap.
    pose proof (f_equal (F_hom0 A A) H0) as Hmap.
    rewrite (F_comp0 A B A j f) in Hmap.
    rewrite (F_id0 A) in Hmap.
    exact Hmap.
Qed.

(*TODO? : un foncteur ne reflète pas forcément les isomorphismes*)

(*TODO : si f possède un inverse, il est unique*)
Theorem iso_invert_unique : (
    forall Cat : Category,
    forall A B : Cat.(C_obj),
    forall f : Cat.(C_hom) A B,
    forall g, is_inverse f g -> exists! g, is_inverse f g
).
Proof.
Admitted.

(*TODO : si f possède un inverse, c'est un isomorphisme*)
Theorem iso_invert_iso : (
    forall Cat : Category,
    forall A B : Cat.(C_obj),
    forall f : Cat.(C_hom) A B,
    forall g, is_inverse f g -> is_iso g
).
Proof.
    intros.
    unfold is_inverse in *.
    unfold is_iso.
    unfold is_inverse.
    destruct H.
    exists f.
    split.
    trivial. trivial.
Qed.

(*composition de 2 iso = iso*)
Theorem iso_comp : (
    forall Cat : Category,
    forall A B C : Cat.(C_obj),
    forall f : Cat.(C_hom) A B,
    forall g : Cat.(C_hom) B C,
    is_iso f -> is_iso g -> is_iso (Cat.(C_comp) g f)
).
Proof.
    intros.
    unfold is_iso in *.
    destruct H as [f_iso Pf].
    destruct H0 as [g_iso Pg].
    exists (Cat.(C_comp) f_iso g_iso).
    destruct Pf.
    destruct Pg.
    split.

    setoid_rewrite <- Cat.(C_comp_assoc) at 1.
    setoid_rewrite Cat.(C_comp_assoc) at 2.
    rewrite H.
    setoid_rewrite Cat.(C_comp_assoc) at 1.
    rewrite Cat.(C_comp_id_left).
    
    now rewrite H1.
    setoid_rewrite <- Cat.(C_comp_assoc) at 1.
    setoid_rewrite Cat.(C_comp_assoc) at 2.
    rewrite H2.
    rewrite Cat.(C_comp_id_right).
    now rewrite H0.
Qed.

(*identité = iso*)
Theorem identity_is_isomorphism : (
    forall Cat : Category,
    forall A : Cat.(C_obj),
    is_iso (Cat.(C_id) A)
).
Proof.
    intros.
    unfold is_iso.
    exists (Cat.(C_id) A).
    split.
    apply Cat.(C_comp_id_left).
    apply Cat.(C_comp_id_left).
Qed.

(*définition de groupoïde*)
Definition groupoide {C: Category} : Prop := 
    forall A B : C.(C_obj), forall f : C.(C_hom) A B, is_iso f.

(*définition de catégorie squelettique*)
Definition squelettique {C: Category} : Prop := 
    forall A B : C.(C_obj), forall f : C.(C_hom) A B, is_iso f -> A = B.

(*définition de catégorie connexe*)
Definition connexe {C: Category} : Prop := 
    (@groupoide C) /\ (forall A B : C.(C_obj), exists f : C.(C_hom) A B, is_iso f).

(*TODO : dans la cat associée à un anneau unitaire, (a, b) iso ssi b inversible dans A*)

(*TODO : maybe formaliser les diagrammes ? Jsp comment faire ça proprement*)

(*TODO : comma catégories*)

(*TODO : catégorie relative*)

(*TODO : comma catégorie avec une cat = 1*)

(*TODO : comma catégorie avec F et G étant id (catégorie des flèches de C)*)

(*transformations naturelles*)
Class Natural_transformation (C D : Category) (F G : Functor C D) := {
    (*data*)
    nt : forall A : C.(C_obj),
        D.(C_hom) (F.(F_obj) A) (G.(F_obj) A);

    (*constraints*)
    nt_naturality :
        forall {A B : C.(C_obj)} (f : C.(C_hom) A B),
            D.(C_comp) (G.(F_hom) f) (nt A)
            = D.(C_comp) (nt B) (F.(F_hom) f)
}.

(*TODO : a shitton of things*)

Definition initial {C: Category} (A : C_obj) : Prop :=
    forall (X: C.(C_obj)), 
    exists f : C.(C_hom) A X,
    forall g : C.(C_hom) A X,
    f = g.

(*Check it works*)
Definition final {C: Category} (A : C_obj) : Prop :=
    @initial (Opp C) A.

Theorem iso_initial : (
    forall Cat : Category,
    forall A B : C_obj,
    initial A -> initial B -> @iso Cat A B
).
Proof.
    intros.
    unfold iso.
    simpl.
    unfold initial in *.
    simpl.
    destruct (H B) as [f _].
    destruct (H0 A) as [g _].
    exists f.
    unfold is_iso.
    exists g.
    unfold is_inverse.
    destruct (H A) as [idA idAu].
    destruct (H0 B) as [idB idBu].
    specialize (idAu (C_id A)) as UNIQA.
    specialize (idBu (C_id B)) as UNIQB.
    rewrite UNIQA in idAu.
    rewrite UNIQB in idBu.
    split.
    specialize (idAu (C_comp g f)). symmetry. trivial.
    specialize (idBu (C_comp f g)). symmetry. trivial.
Qed.

(*initial dans C ssi terminal dans C^op*)
Theorem init_equiv_final : (
    forall Cat : Category,
    forall A : C_obj,
    @initial Cat A <-> @final (Opp Cat) A
).
Proof.
    intros.
    unfold final.
    split.
    trivial. trivial.
Qed.

(*TODO : Objets finaux iso (par dualité ?)*)
Theorem iso_final : (
    forall Cat : Category,
    forall A B : C_obj,
    final A -> final B -> @iso Cat A B
).
Proof.
Admitted.

(*TODO : équivalence de catégorie*)

(*TODO : N et Z par div sont des cats équivalentes*)


