Require Import List.
Require Import Cpdt.CpdtTactics.
Set Implicit Arguments.
Set Asymmetric Patterns.

Inductive unit := tt.
Inductive Empty_set := .
Inductive bool := true | false.
Inductive sum := .
Inductive prod := .
Inductive and := conj.
Inductive or := or_introl | or_intror.
Inductive ex := ex_intro.
Inductive eq := eq_refl.
Reset unit.

Print unit.

Print True.

Section Propositional.
  Variables P Q R : Prop.
  Theorem obvious : True.
    apply I.
  Qed.
  Theorem obvious' : True.
    constructor.
  Qed.
  Print False.
  Theorem False_imp : False -> 2 + 2 = 5.
    destruct 1.
  Qed.

  Theorem arith_neq : 2 + 2 = 5 -> 9 + 9 = 835.
    intro.
    cut False. intro Hn. elim Hn; clear Hn.
  Restart.
    intro.
    elimtype False.
    crush.
  Qed.

  Definition foo := not.
  Print not.

  Theorem arith_neq' : ~ (2 + 2 = 5).
    unfold not.
    crush.
  Qed.

  Print and.

  Theorem and_comm : P /\ Q -> Q /\ P.
    destruct 1.
    spli
    assumption.
    assumption.
  Qed.

  Print or.

  Theorem or_comm : P \/ Q -> Q \/ P.
    destruct 1.
    right; assumption.
    left; assumption.
  Qed.

  Theorem contra : P -> ~P -> R.
    unfold not.
    intros.
    elimtype False.
    apply H0.
    assumption.
  Admitted.

  Theorem and_assoc : (P /\ Q) /\ R -> P /\ (Q /\ R).
    intros.
    destruct H.
    destruct H.
    split.
    assumption.
    split.
    assumption.
    assumption.
  Admitted.

  Theorem or_assoc : (P \/ Q) \/ R -> P \/ (Q \/ R).
    intros.
    destruct H.
    destruct H.
    left.
    assumption.
    right.
    left.
    assumption.
    right.
    right.
    assumption.
  Admitted.

  Theorem or_comm' : P \/ Q -> Q \/ P.
    tauto.
  Qed.

  Theorem arith_comm : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    intuition.
    rewrite app_length.
    tauto.
  Qed.

  Theorem arith_comm' : forall ls1 ls2 : list nat,
    length ls1 = length ls2 \/ length ls1 + length ls2 = 6
    -> length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2.
    Hint Rewrite app_length.

    crush.
  Qed.

End Propositional.

  Print ex.

Theorem exist1 : exists x : nat, x + 1 = 2.
  exists 1.
  reflexivity.
Qed.

Theorem exist2 : forall n m : nat, (exists x : nat, n + x = m) -> n <= m.
  destruct 1.
  crush.
Qed.

Theorem forall_exists_commute : forall (A B : Type) (P : A -> B -> Prop),
  (exists x : A, forall y : B, P x y) -> (forall y : B, exists x : A, P x y).
  intros.
  destruct H.
  exists x.
  apply H.
Admitted.

Inductive isZero : nat -> Prop :=
| IsZero : isZero 0.

Theorem isZero_zero : isZero 0.
  constructor.
Qed.

Print eq.

Theorem isZero_plus : forall n m : nat, isZero m -> n + m = n.
  destruct 1.
  crush.
Qed.

Theorem isZero_contra : isZero 1 -> False.
  destruct 1.
  Undo.
  inversion 1.
Qed.

Theorem isZero_contra' : isZero 1 -> 2 + 2 = 5.
  destruct 1.
Abort.

Check isZero_ind.

Section twoEls.
  Variable A : Type.

  Inductive twoEls : list A -> Prop :=
  | TwoEls : forall x y, twoEls (x :: y :: nil).

  Theorem twoEls_nil : twoEls nil -> False.
    inversion 1.
  Qed.

  Theorem twoEls_two : forall ls, twoEls ls -> length ls = 2.
    inversion 1.
    reflexivity.
  Qed.
End twoEls.

Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).

Theorem even_0 : even 0.
  constructor.
Qed.

Theorem even_4 : even 4.
  constructor; constructor; constructor.
Qed.

Hint Constructors even.

Theorem even_4' : even 4.
  auto.
Qed.

Theorem even_1_contra : even 1 -> False.
  inversion 1.
Qed.

Theorem even_3_contra : even 3 -> False.
  inversion 1.
  inversion H1.
Qed.

Theorem even_plus : forall n m, even n -> even m -> even (n + m).
  induction n; crush.
  inversion H.
  simpl.
  constructor.
Restart.
  induction 1.
  crush.
  intro.
  simpl; constructor.
  apply IHeven; assumption.
Restart.
  induction 1; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  induction 1.
Abort.

Lemma even_contra' : forall n', even n' -> forall n, n' = S (n + n) -> False.
  induction 1; crush.
  destruct n; destruct n0; crush.
  SearchRewrite (_ + S _).
  rewrite <- plus_n_Sm in H0.
  apply IHeven with n0; assumption.
Restart.
  Hint Rewrite <- plus_n_Sm.
  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.
Qed.

Theorem even_contra : forall n, even (S (n + n)) -> False.
  intros; eapply even_contra'; eauto.
Qed.

Lemma even_contra'' : forall n' n, even n' -> n' = S (n + n) -> False.
  induction 1; crush;
    match goal with
      | [ H : S ?N = ?N0 + ?N0 |- _ ] => destruct N; destruct N0
    end; crush.
Abort.

Inductive prop : Set :=
| Tru : prop
| Fals : prop
| And : prop -> prop -> prop
| Or : prop -> prop -> prop.

Inductive holds : prop -> Prop :=
| HTru : holds Tru
| HAnd : forall p1 p2, holds p1 -> holds p2 -> holds (And p1 p2)
| HOr1 : forall p1 p2, holds p1 -> holds (Or p1 p2)
| HOr2 : forall p1 p2, holds p2 -> holds (Or p1 p2).

Inductive falseFree : prop -> Prop :=
| FFTru : falseFree Tru
| FFAnd : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (And p1 p2)
| FFNot : forall p1 p2, falseFree p1 -> falseFree p2 -> falseFree (Or p1 p2).

Hint Constructors holds.

Theorem falseFree_holds : forall p, falseFree p -> holds p.
  induction 1; crush.
Qed.

Inductive prop' : Set :=
| Tru' : prop'
| And' : prop' -> prop' -> prop'
| Or' : prop' -> prop' -> prop'.

Inductive holds' : prop' -> Prop :=
| HTru' : holds' Tru'
| HAnd' : forall p1 p2, holds' p1 -> holds' p2 -> holds' (And' p1 p2)
| HOr1' : forall p1 p2, holds' p1 -> holds' (Or' p1 p2)
| HOr2' : forall p1 p2, holds' p2 -> holds' (Or' p1 p2).

Fixpoint propify (p : prop') : prop :=
  match p with
    | Tru' => Tru
    | And' p1 p2 => And (propify p1) (propify p2)
    | Or' p1 p2 => Or (propify p1) (propify p2)
  end.

Hint Constructors holds'.

Lemma propify_holds' : forall p', holds p' -> forall p, p' = propify p -> holds' p.
  induction 1; crush; destruct p; crush.
Qed.

Theorem propify_holds : forall p, holds (propify p) -> holds' p.
  intros; eapply propify_holds'; eauto.
Qed.