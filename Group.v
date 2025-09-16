Record Group := {
    (*Data*)
    Grp :> Type;
    Loi : Grp -> Grp -> Grp;
    Id: Grp;

    (*Contraints*)
    associative := forall x y z : Grp, Loi (Loi x y) z = Loi x (Loi y z);
    id_left : forall x : Grp, Loi Id x = x;
    id_right : forall x : Grp, Loi x Id = x;
    inverse_left : forall x : Grp, exists x' : Grp, Loi x' x = Id;
    inverse_right : forall x : Grp, exists x' : Grp, Loi x x' = Id;
}.

Definition is_neutral {G: Group} (e: G) :=
    (forall y : G, (Loi G) e y = y) /\ (forall y : G, (Loi G) y e = y).

Theorem uniq_neutral:
  forall (G: Group) (x y: Grp G), is_neutral x -> is_neutral y -> x = y.
Proof.
  (*Woah thats a bad proof*)
  intros.
  assert (x = (Loi G) x y).
  unfold is_neutral in H0.
  destruct H0 as [H1 H2].
  rewrite H2. reflexivity.
  assert ((Loi G ) x y = y).
  unfold is_neutral in H.
  destruct H as [H3 H4].
  rewrite H3. reflexivity.
  rewrite H1. rewrite H2. trivial.
Qed.

Definition puissance {G : Group} (g: G) (n: nat) := match n with
  | 0 => Id G
  | S n => Loi G g (puissance g (n-1))
end
.
Definition ordre {G: Group} (g: G) :=

