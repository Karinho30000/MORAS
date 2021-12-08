Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Omega.

(* Bit *)

Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
match x with
  | O => O
  | I => y
end.

Definition Or (x y : B) : B :=
match x with
  | O => y
  | I => I
end.

Definition Not (x : B) : B :=
match x with
  | O => I
  | I => O
end.

Definition Add (x y c : B) : B :=
match x, y with
  | O, O => c
  | I, I => c
  | _, _ => Not c
end.

Definition Rem (x y c : B) : B :=
match x, y with
  | O, O => O
  | I, I => I
  | _, _ => c
end.

(* List *)

Fixpoint AndL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => And x y :: AndL xs ys
end.

Fixpoint OrL (x y : list B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Or x y :: OrL xs ys
end.

Fixpoint NotL (x : list B) : list B :=
match x with
  | [] => []
  | x :: xs => Not x :: NotL xs
end.

Fixpoint AddLr (x y : list B) (c : B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Add x y c :: AddLr xs ys (Rem x y c)
end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

Fixpoint IncLr (x : list B) (c : B) : list B :=
match x with
| [] => []
| x :: xs => Add x I c :: IncLr xs (Rem x I c)
end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* ALU *)

Definition flag_zx (f : B) (x : list B) : list B :=
match f with
| I => repeat O (length x)
| O => x
end.

Definition flag_nx (f : B) (x : list B) : list B :=
match f with
| I => NotL x
| O => x
end.

Definition flag_f (f : B) (x y : list B) : list B :=
match f with
| I => AddL x y
| O => AndL x y
end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B := 
  flag_nx no (flag_f f (flag_nx nx (flag_zx zx x)) (flag_nx ny (flag_zx zy y))).

(* Teoremi *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof.
    assert (P : forall (n : nat), AddL (repeat O n) (repeat O n) = repeat O n).
    {
      assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. reflexivity.
      }
      assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
      }
      intros. unfold AddL.
      rewrite P_rev_2. 
      induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros H. simpl. rewrite H. rewrite P. reflexivity.
Qed.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof.
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AddL : forall (n : nat), AddL (repeat I n) (repeat O n) = repeat I n).
  {
    assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. reflexivity.
    }
    assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros. unfold AddL. rewrite P_rev_2, P_rev_2. induction n.
    - reflexivity.
    - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
  }
  intros H. simpl. rewrite H, P_NotL. rewrite P_AddL. reflexivity.
Qed.

Lemma ALU_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O O = x.
Proof. Abort.

Lemma ALU_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O O = y.
Proof. Abort.

Lemma ALU_Not_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. Abort.

Lemma ALU_Not_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. Abort.

Lemma ALU_Add (x y : list B) : 
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. Abort.




Lemma ALU_And (x y : list B) : 
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma ALU_Or (x y : list B) : 
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof.
  assert (DemorganL : forall (a b : list B), AndL (NotL a) (NotL b) = NotL (OrL a b)).
  {
    induction a, b ; simpl ; try reflexivity.
    - specialize (IHa b0). rewrite IHa.
      assert (Demorgan : forall (c d : B), And (Not c) (Not d) = Not (Or c d)).
      {
        intros. destruct c, d ; simpl ; try reflexivity.
      }
      rewrite Demorgan. reflexivity.
  }
  assert (H : forall (x y : list B), NotL (NotL (OrL x y)) = OrL x y).
  {
    induction x0, y0 ; simpl ; try reflexivity. specialize (IHx0 y0). rewrite IHx0.
    assert (H1 : forall (x y : B), Not (Not (Or x y)) = Or x y).
    {
      - intros. destruct x1, y1 ; simpl ; try reflexivity.
    } 
    rewrite H1. reflexivity.
  }
  intros. simpl. rewrite DemorganL. rewrite H. reflexivity.
Qed.

Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
  intros [a [b c]]. simpl. rewrite a,b.
  assert (NotL_H : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n0.
    - simpl. reflexivity.
    - simpl. rewrite IHn0. reflexivity. 
  }
  rewrite NotL_H.
  assert (AddL_H : AddL (repeat I n) (repeat I n) = repeat I (pred n) ++ [O]).
  {
    assert (Rev_1_H : forall (a : B) (n : nat), repeat a n ++ [a] = a :: repeat a n).
    {
      induction n0.
      - simpl. reflexivity.
      - simpl. rewrite IHn0. reflexivity.
    }
    assert (Rev_2_H : forall (a : B) (n : nat), rev (repeat a n) = repeat a n).
    {
        induction n0.
        - simpl. reflexivity.
        - simpl. rewrite IHn0. rewrite Rev_1_H. reflexivity.
    }
    induction n.
    - simpl. contradiction.
    - unfold AddL. simpl.
      rewrite Rev_2_H. rewrite Rev_1_H. simpl. f_equal.
      assert (AddLr_H : forall (a : B) (n : nat) , AddLr (repeat a n) (repeat a n) a = repeat a n).
      {
        intros. induction a0.
        - induction n0. 
           -- simpl. reflexivity.
           -- simpl. rewrite IHn0. reflexivity.
        - induction n0.
          -- simpl. reflexivity.
          -- simpl. rewrite IHn0. reflexivity. 
      }
      rewrite AddLr_H. rewrite Rev_2_H. reflexivity.
  }
  rewrite AddL_H. 
  assert (NotL1_H : forall (n : nat), NotL (repeat I (n) ++ [O]) = repeat O (n) ++ [I]).
  {
    intros. induction n0.
    - simpl. reflexivity.
    - simpl. rewrite <- IHn0. reflexivity.
  }
  rewrite NotL1_H. reflexivity.
Qed.








