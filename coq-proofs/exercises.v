(* 

Prove the lemmas given below (and replace Admitted with Qed).

It is not allowed to: 
1. import other modules than List,
2. define Ltac tactics,
3. erase statements of the lemma (if you fail to prove a lemma leave Admitted).

It is allowed to:

1. introduce your own definitions and auxiliary lemmas,
2. change the order of the lemmas to prove,
3. add comments.

Remember about revert/generalize tactics.
*)



Require Import List.
Set Implicit Arguments.

Section Zal.

Check list.
Print list.

Variable A: Type.

Inductive podciag : list A -> list A -> Prop :=
| PC_Nil : forall l, podciag nil l
| PC_ConsH : forall a l1 l2, podciag l1 l2 -> podciag (cons a l1) (cons a l2)
| PC_ConsT : forall a l1 l2, podciag l1 l2 -> podciag l1 (cons a l2).

Inductive prefix : list A -> list A -> Prop :=
| P_Nil : forall l, prefix nil l
| P_Cons : forall a l1 l2, prefix l1 l2 -> prefix (cons a l1) (cons a l2).

Inductive sufix : list A -> list A -> Prop :=
| S_Nil : forall l, sufix l l
| S_Cons : forall a l1 l2, sufix l1 l2 -> sufix l1 (cons a l2).

Inductive podlista : list A -> list A -> Prop :=
| PL_Base : forall l1 l2, prefix l1 l2 -> podlista l1 l2
| PL_Cons : forall a l1 l2, podlista l1 l2 -> podlista l1 (cons a l2).


Lemma Prefix_Podlista : forall l1 l2, prefix l1 l2 -> podlista l1 l2.
Proof.
intros.
constructor.
auto.
Qed.

(* My lemma *)
Lemma Prefix_self : forall l, prefix l l.
Proof.
induction l.
+ apply P_Nil.
+ apply P_Cons.
  assumption.
Qed. 

Lemma Sufix_Podlista : forall l1 l2, sufix l1 l2 -> podlista l1 l2.
Proof.
induction l2.
intros.
+ apply PL_Base.
  inversion H.
  apply P_Nil.
+ intros.
  induction l1.
  * apply PL_Base.
    apply P_Nil.
  * inversion H.
    - apply PL_Base.
      apply P_Cons.
      apply Prefix_self.
    - apply PL_Cons.
      auto.
Qed.

Lemma Prefix_Podciag : forall l1 l2, prefix l1 l2 -> podciag l1 l2.
Proof.
induction l1.
+ intros.
  apply PC_Nil.
+ intros.
  induction l2.
  * inversion H.
  * inversion H.
    apply PC_ConsH.
    apply IHl1.
    assumption.
Qed.

Lemma Podlista_Podciag: forall l1 l2, podlista l1 l2 -> podciag l1 l2.
Proof.
induction l1.
+ intros.
  apply PC_Nil.
+ intros.
  induction l2.
  - inversion H.
    inversion H0.
  - inversion H.
    * inversion H0.
      apply PC_ConsH.
      apply IHl1.
      apply PL_Base.
      inversion H0.
      assumption.
    * apply PC_ConsT.
      apply IHl2.
      assumption.
Qed.


Lemma Append_Podciag_Podciag_Podciag: 
      forall p1 l1 p2 l2, podciag p1 l1 -> podciag p2 l2 
       -> podciag (p1 ++ p2) (l1 ++ l2).
Proof.
induction p1.
+ intros.
  simpl.
  induction l1.
  - auto.
  - simpl.
    apply PC_ConsT.
    apply IHl1.
    apply PC_Nil.
+ intros.
  simpl.
  induction l1.
  - simpl.
    inversion H.
  - simpl.
    inversion H.
    * apply PC_ConsH.
      apply IHp1.
      assumption.
      assumption.
    * apply PC_ConsT.
      apply IHl1.
      assumption.
Qed.

Lemma Append_Eq_Prefix_Prefix:
      forall l p2 l2, prefix p2 l2 -> prefix (l ++ p2)(l ++ l2).
Proof.
induction l.
+ intros.
  simpl.
  assumption.
+ intros.
  simpl.
  apply P_Cons.
  apply IHl.
  assumption.
Qed.

(* My lemma *)
Lemma Prefix_ignore_beginning: forall l1 p2 l2, prefix p2 l2 -> prefix (l1 ++ p2) (l1 ++ l2).
Proof.
induction l1.
+ intros.
  simpl.
  assumption.
+ intros.
  simpl.
  apply P_Cons.
  apply IHl1.
  assumption.
Qed.

Lemma Append_Sufix_Prefix_Podlista:
      forall p1 l1 p2 l2, sufix p1 l1 -> prefix p2 l2
       -> podlista (p1 ++ p2) (l1 ++ l2).
Proof.
induction p1.
+ intros.
  simpl.
  induction l1.
  - simpl.
    apply PL_Base.
    assumption.
  - simpl.
    apply PL_Cons.
    apply IHl1.
    destruct l1.
    * apply S_Nil.
    * inversion H.
      assumption.
+ intros.
  simpl.
  induction l1.
  - simpl.
    inversion H.
  - simpl.
    inversion H.
    * apply PL_Base.
      apply P_Cons.
      apply Prefix_ignore_beginning.
      assumption.
    * apply PL_Cons.
      apply IHl1.
      assumption.
Qed.

Definition sufixD (s l : list A):= exists p, p ++ s = l.

(* My lemma *)
Lemma Sufix_ignore_beginning: forall b l, sufix l l -> sufix l (b++l).
Proof.
intros.
induction b.
+ simpl.
  apply S_Nil.
+ simpl.
  apply S_Cons.
  assumption.
Qed.

Lemma Sufix_SufixD: forall s l, sufix s l <-> sufixD s l.
Proof.
intros.
split.
induction l.
+ intros.
  unfold sufixD.
  exists nil.
  inversion H.
  trivial.
+ intros.
  unfold sufixD.
  unfold sufixD in IHl.
  inversion H.
  - exists nil.
    simpl.
    trivial.
  - apply IHl in H2.
    inversion H2.
    exists (cons a x).
    simpl.
    rewrite H4.
    trivial.
+ unfold sufixD.
  intros.
  inversion H.
  destruct x.
  simpl in H0.
  rewrite H0.
  apply S_Nil.
  simpl in H0.
  symmetry in H0.
  rewrite H0.
  apply S_Cons.
  apply Sufix_ignore_beginning.
  apply S_Nil.
Qed.

Lemma Sufix_Prefix: forall s l, sufix s l -> exists p, prefix p l /\ p ++ s = l.
Proof.
induction l.
+ intros.
  exists nil.
  inversion H.
  split.
  - apply P_Nil.
  - trivial.
+ intros.
  inversion H.
  - exists nil.
    simpl.
    split.
    apply P_Nil.
    trivial.
  - apply IHl in H2.
    inversion H2.
    exists (cons a x).
    destruct H4.
    split.
    * apply P_Cons.
      assumption.
    * simpl.
      rewrite H5.
      trivial.
Qed.

End Zal.
