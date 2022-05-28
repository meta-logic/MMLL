(** * Utils *)
(** Common definitions including:
 -  theorems about lists and permutation.  
 -  the induction scheme for Strong Induction
 -  some arithmetic results (specially dealing with [max] and [min])
 *)

Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Export Permutation.
Require Import Coq.Relations.Relations.
Require Import Coq.Setoids.Setoid.
Require Export Coq.Sorting.PermutSetoid.
Require Export Coq.Sorting.PermutEq.
Require Import Coq.Program.Equality.
Require Export Coq.Lists.List.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Arith.Arith.
Require Export Coq.Init.Nat.
Require Import Lia.


Export ListNotations.

Set Implicit Arguments.

Lemma NatComp : forall x y, x >= y + 1 -> S x - y - 2 = x - y - 1.
Proof with subst;auto. lia.
Qed.  
  

(** ** Additional results about permutations *)
Section Permutations.

  Variable A:Type.

Lemma ListConsApp (a b: A) : forall L M , a :: L = M ++ [b] -> 
       (L=[]/\M=[]/\a=b) \/ exists X, M = a :: X /\ L = X++[b].
Proof with subst;auto.
  induction M; intros...
  * inversion H...
  * rewrite <- app_comm_cons in H. 
    inversion H;subst...
    right.
    exists M...
 Qed.   
 
 Lemma ListConsApp' (a b: A) : forall L M1 M2 , a :: L = M1 ++ [b] ++ M2 -> 
        (L=M2/\M1=[]/\a=b) \/ 
       exists X, M1 = a :: X /\ L = X++[b]++M2.
Proof with subst;auto.
  destruct M1;intros...
  * inversion H;subst...
  * rewrite <- app_comm_cons in H. 
    inversion H;subst...
    right.
    exists M1...
 Qed. 

  Lemma ListConsApp'' (a : A) M1: forall L M2 , a :: L = M1 ++ M2 -> 
       (M1=[ ]/\M2=a::L) \/ 
       exists X, M1 = a :: X /\ L = X++M2.
Proof with subst;auto.
  induction M1;intros...
  rewrite <- app_comm_cons in H. 
   inversion H;subst...
   right.
   exists M1... 
 Qed. 
       
  Lemma Perm_swap_inv : forall (x y : A) (N M : list A),
      Permutation (x :: N) (y :: x :: M) ->
      Permutation N ( y :: M).
    intros.
    rewrite perm_swap in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Lemma Perm_swap_inv_app : forall y N M (x : A) ,
      Permutation (x :: N) (y ++ x :: M) ->
      Permutation N ( y ++ M).
    intros.
    rewrite  (Permutation_cons_append M x) in H.
    rewrite  Permutation_cons_append in H.
    rewrite app_assoc in H.
    rewrite  <- Permutation_cons_append in H.
    rewrite  <- (Permutation_cons_append (y ++ M) x ) in H.
    apply Permutation_cons_inv in H;auto.
  Qed.

  Theorem PermutConsApp: forall (a : A) l1 b l2,
      Permutation (a :: l1 ++ b :: l2) (b :: a :: l1 ++ l2).
    intros.
    rewrite perm_swap.
    rewrite <- Permutation_middle.
    auto.
  Qed.

  Lemma PermutationInCons : forall (F:A) M N,
      Permutation (F::M) N -> In F N.
    intros.
    eapply Permutation_in with (x:= F) (l':=N);eauto.
    constructor;auto.
  Qed.


  (** A slightly different version of  [Permutation_map] *)
  Lemma PermuteMap : forall (L L' : list A) (f: A->Prop),
      Forall f L -> Permutation L L'-> Forall f L'.
    intros.
    apply Permutation_sym in H0.
    assert(forall x, In x L' -> In x L) by eauto using Permutation_in.
    rewrite Forall_forall in H.
    rewrite Forall_forall;intros.
    firstorder.
  Qed.

(* Permutation_app_inv *)
  Lemma Permutation_mid : forall (F:A) l1 l2 l1' l2', 
      Permutation (l1 ++ F :: l2) (l1' ++ F :: l2') ->
      Permutation (l1 ++ l2) (l1' ++ l2').
    intros.
    assert(Permutation (F::l2) (l2 ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H0 in H.
    assert(Permutation (F::l2') (l2' ++ [F]))
      by  apply Permutation_cons_append.
    rewrite H1 in H.
    apply Permutation_app_inv_r with (l:= [F]).
    do 2 rewrite app_assoc_reverse;auto.
  Qed.
  
 (* perm_takeit_5 *)
  Lemma Permutation_midle : forall  (F:A) l1 l2,
      Permutation (l1 ++ F :: l2) ( F :: l1  ++ l2).
    intros.
    generalize (Permutation_cons_append  l1 F);intro.
    change (F::l1++l2) with ( (F::l1) ++ l2).
    rewrite H.
    assert(l1 ++ F :: l2 = (l1 ++ [F]) ++ l2).
    rewrite app_assoc_reverse;auto.
    rewrite H0.
    auto.
  Qed.


(* Permutation_app_swap_app *)
  Lemma Permutation_midle_app : forall  (la lb lc: list A),
      Permutation (la ++ lb ++ lc) ( lb ++ la  ++ lc).
    intros.
    rewrite <- app_assoc_reverse. 
    rewrite Permutation_app_comm with (l:=la).
    rewrite app_assoc_reverse;auto.
  Qed.


  Lemma InPermutation : forall (l:A) L,
      In l L -> exists L', Permutation L (l :: L').
    induction L;intros.
    inversion H.
    inversion H;subst.
    exists L;auto.
    apply IHL in H0.
    destruct H0 as [L' H0].
    exists (a :: L').
    rewrite H0.
    constructor.
  Qed.
  

End Permutations.

(** ** Strong Induction *)

Section StrongIndPrinciple.

  Variable P: nat -> Prop.

  Hypothesis P0: P O.

  Hypothesis Pn: forall n, (forall m, m<=n -> P m) -> P (S n).

  Lemma strind_hyp : forall n, (forall m, ((m <= n) -> P m)).
  Proof.
    induction n; intros m H;inversion H;auto.
  Qed.
  (** Strong induction principle *)
  Theorem strongind: forall n, P n.
  Proof.
    induction n; auto.
    apply Pn.
    apply strind_hyp.
  Qed.

End StrongIndPrinciple.


(** ** Aditional results on Arithmentic *)
Section Arithmentic.

  Lemma MaxPlus : forall a b, (max a b <= plus a  b).
    intros;lia.
  Qed.
  
  Lemma MaxPlus' : forall a b c, (plus a b <= c -> max a b <= c).
    intros;lia.
  Qed.
  
  
  Theorem GtExists : forall n, n>0 -> exists n', n = S n'.
    intros.
    destruct n;inversion H;subst;eauto.
  Qed.

End Arithmentic.

Ltac mgt0 := let H := fresh "H" in
             match goal with [_ :  ?m >= S _ |- _] =>
                             assert(H : m>0) by lia;
                             apply GtExists in H;
                             destruct H;subst
             end.


Section Pairs.

Variable S:Type. (* SubExps *)
Variable F:Type. (* Formulas *)


(* fst (split L) *)
Definition first (L:list (S * F)) :=  map fst L.
(* snd (split L) *)
Definition second (L:list (S * F)) := map snd L.

         
Lemma secondApp C1 C2 : second (C1 ++ C2) = second C1 ++ second C2.
Proof.
  induction C1;simpl.
  reflexivity.
  rewrite IHC1.
  reflexivity. Qed.

Lemma firstApp C1 C2 : first (C1 ++ C2) = first C1 ++ first C2.
Proof.
  induction C1;simpl.
  reflexivity.
  rewrite IHC1.
  reflexivity. Qed.

Lemma InFirst c B : In c B -> In (fst c) (first B). 
Proof.
 induction B;intros;auto.
 unfold second.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
Lemma InSecond c B : In c B -> In (snd c) (second B). 
Proof.
 induction B;intros;auto.
 unfold second.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
 Lemma InSecondInv i A B : In (i,A) B -> In A (second B). 
Proof.
 induction B;intros;auto.
 inversion H;subst;auto;
 simpl;auto.
 Qed.
 
 End Pairs.

   
