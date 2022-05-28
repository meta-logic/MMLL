
(** * Tactics *)
(**  Some useful tactics dealing with permutations, lists and maps
 *)

Require Export Permutation.
Require Export Coq.Lists.List.
Require Export Coq.Arith.Arith.
Require Export Coq.Init.Nat.
Require Export MMLL.Misc.Permutations. 
Require Export MMLL.Misc.Utils.
Require Import Lia.
Export ListNotations.

Set Implicit Arguments.

  
 Global Hint Extern 1 (Permutation ?S ?U) =>
  match goal with
  | H: Permutation S ?T |- _ => apply (Permutation_trans H)
  | H: Permutation ?T S  |- _ => symmetry in H; apply (Permutation_trans H)  
  end : core.

Ltac clear_junk :=
repeat
 match goal with
 | [ H: ?a = ?a |- _ ] => clear H
 | [ H: (?a,?b) = (?a,?b) |- _ ] => clear H
 | [ H1: ?A, H2: ?A |- _ ] => clear H1
 
 | [ H: In ?F (?F :: _) |- _ ] => clear H
 | [ H: In ?F (_++[?F]) |- _ ] => clear H
 | [ H: In ?F (_++?F :: _)|- _ ] => clear H
 | [ H: Permutation ?A ?A |- _] => clear H 
 end.
 

Ltac simplifier :=
repeat
  match goal with
 | [ H: map ?f ?B = [_] |- _ ] => apply map_eq_cons in H;simplifier
 | [ H: map ?f ?B = [ ] |- _ ] => apply map_eq_nil in H;subst 
 | [ H: context[_++nil] |- _ ] => rewrite app_nil_r in H
 | [ H: context[nil++_] |- _ ] => rewrite app_nil_l in H
 | [  |- context[_++nil] ] => rewrite app_nil_r
 | [  |- context[nil++_] ] => rewrite app_nil_l

 | [ H: context[_ - 0] |- _ ] => rewrite Nat.sub_0_r in H
 | [ H: context[S _ - 1] |- _ ] => simpl in H;rewrite Nat.sub_0_r in H 
 | [ H: context[fst (_, _)] |- _ ] => simpl in H
 | [ H: context[snd (_, _)] |- _ ] => simpl in H
 | [  |- context[_ - 0] ] => rewrite Nat.sub_0_r
 | [  |- context[S _ - 1] ] => simpl;rewrite Nat.sub_0_r
 | [  |- context[fst (_, _)] ] => simpl
 | [  |- context[snd (_, _)] ] => simpl

  | [ H1: ?f ?a = true, H2: context[?f ?a] |- _ ] => rewrite H1 in H2
  | [ H1: ?f ?a = false, H2: context[?f ?a] |- _ ] => rewrite H1 in H2
                   
  | [ H: ?f ?a = true |- context[?f ?a]  ] => rewrite H
  | [ H: ?f ?a = false |- context[?f ?a]  ] => rewrite H
 
  | [ H1: ?f = [], H2: context[?f] |- _ ] => rewrite H1 in H2                 
  | [ H: ?f = [] |- context[?f]  ] => rewrite H
  
   
 | [H : exists (x : _), _ |- _ ] => destruct H
 | [H : _ /\ _ |- _ ] => decompose [and or] H;clear H
 | [H : _ \/ _ |- _ ] => decompose [and or] H;clear H
 | [ |- _ /\ _ ] => split
end;auto.
    
 
Ltac strivial := 
try
  match goal with
 | [H1: ?f ?a = true, H2: ?f ?a = false |- _] => rewrite H1 in H2; discriminate H2
 
 | [  |- ?a = ?a ] => reflexivity 
 | [H: False |- _] => contradiction
 | [H1: ?F , H2 : ~ ?F |- _ ] => contradiction
 | [ |- In ?F (?F :: _)] => apply in_eq
 | [H: In ?F ?L  |- In ?F (_ :: ?L)] => apply in_cons;auto
 | [H: In ?F ?L  |- In ?F (?L ++ _)] => apply in_or_app;left;auto
 | [H: In ?F ?L  |- In ?F (_ ++ ?L)] => apply in_or_app;right;auto
 | [ |- In ?F (_++ ?F :: _)] => apply in_elt
 | [ H: In _ nil |- _ ] => inversion H 
 | [ H: [_] = nil |- _ ] => inversion H 
 | [ H: nil = [_] |- _ ] => inversion H 

 | [ H: Permutation ?A ?B |- Permutation ?B ?A  ] => symmetry in H;auto
 | [ H: Permutation ?A ?B |- Permutation (?a::?A) (?a::?B)  ] => apply perm_skip;auto
 | [ |- Permutation (?x::?y::?A) (?y::?x::?A)  ] =>  rewrite perm_swap;auto
 | [H : ?A /\ ?B |- ?A ] => firstorder 
 | [H : ?A /\ ?B |- ?B ] => firstorder  
 | [H : ?A |- ?A \/ ?B ] => firstorder 
 | [H : ?B |- ?A \/ ?B] => firstorder 
  
 | [ H: ?a <> ?a |- _ ] => try solve [timeout 2 firstorder]

 | [ H1: forall x, ?P x -> ?L = ?R, H2: ?P ?X |- _ ] => rewrite (H1 X H2) in x
 | [ H1: ?P ?X -> ?P ?Y, H2: ?P ?X |- ?P ?Y ] => apply H1;auto
 | [ H1: _ ?P ?X -> _ ?P ?Y, H2: _ ?P ?X, H3: ?P ?F  |- _ ?P (?F::?Y) ] => simpl;apply H1;auto
 | [  |- _ <= _ ] => try solve[lia]
 | |- _ >= _ => try solve[lia]
 | |- _ < _ => try solve[lia]
 | |- _ > _ => try solve[lia]
 | [  |- Permutation _ _ ] => try solve[simpl;subst;perm]
 end;auto.

Ltac clean_goal :=
try
repeat 
 match goal with
 | [ H: ?a = ?b |- _ ] => solve [inversion H]
 | [ H: [?a] = [?b] |- _ ] => inversion H;subst;clear H
 | [ H: (_,_) = (_,_) |- _ ] => inversion H;clear H

 (* About Permutations *)
 | [ H: Permutation nil ?L |- _] => apply Permutation_nil in H
 | [ H: Permutation ?L nil  |- _] => symmetry in H; apply Permutation_nil in H
 | [ H: Permutation [?a] ?L  |- _] => apply Permutation_length_1_inv in H
 | [ H: Permutation ?L [?a] |- _] => symmetry in H; apply Permutation_length_1_inv in H
 | [ H: Permutation [?a] [?b]  |- _] => apply Permutation_length_1 in H
 
 (* About Lists *)

(*  | [ H: In _ [_] |- _ ] => 
        let newH := fresh "H" in inversion H as [newH | newH];[subst| inversion newH]    *) 
 | [ H: ?A ++ ?B = nil |- _ ] => 
        apply app_eq_nil in H; destruct H
 | [ H: nil =  ?A ++ ?B |- _ ] => 
      symmetry in H; apply app_eq_nil in H; destruct H
 | [ H: ?A ++ ?B = [_] |- _ ] => 
        apply app_eq_unit in H; decompose [and or] H;clear H
 | [ H: [_] = ?A ++ ?B |- _ ] => 
        symmetry in H; apply app_eq_unit in H; decompose [and or] H;clear H
        
end;subst.


Ltac sauto := subst; (* after an inversion *) 
              simplifier; clean_goal;
              try solve [strivial]; 
              clear_junk; auto.

(* Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.
Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
   |- _ ⇒ rewrite (H1 X H2) in x
  end.
 *) 
 

  (** ** Aditional results on Forall/map *)
Section ForAllMap. 
  
Lemma ForallIn :  forall {A : Type} {F : A} {L : list A} (f : A -> Prop), 
      Forall f L -> In F L -> f F. 
  Proof.
    intros.
    generalize (Forall_forall f L );intro.
    destruct H1.
    apply H1 with (x:= F) in H ;auto.
  Qed.
  
  
End ForAllMap .
  
  
Ltac solveForall :=  
try
  match goal with
   | [  |- Forall _ nil] => apply Forall_nil
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M ?N |- Forall ?f ?N  ] => rewrite <- H2; auto
   | [ H1 : Forall ?f ?M, H2 : Permutation ?N ?M |- Forall ?f ?N  ] => rewrite H2; auto
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?L) |- Forall ?f ?N  ] => rewrite H2 in H1; simpl in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?L) ?M |- Forall ?f ?N  ] => rewrite <- H2 in H1; simpl in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?L) |- Forall ?f ?L  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?L) ?M |- Forall ?f ?L  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?F::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?F::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?F::?L) |- Forall ?f ?L  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?F::?L) ?M |- Forall ?f ?L  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?F::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?F::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++?F::?L) |- Forall ?f [?F]  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++?F::?L) ?M |- Forall ?f [?F]  ] => rewrite <- H2 in H1; solveForall
 
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++(_ ?F _)::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation ?M (?N++(_ _ ?F)::?L) |- ?f ?F  ] => rewrite H2 in H1; solveForall
  
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++(_ ?F _)::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   | [ H1 : Forall ?f ?M, H2 : Permutation (?N++(_ _ ?F)::?L) ?M |- ?f ?F  ] => rewrite <- H2 in H1; solveForall
   

   | [ H : Forall ?f (?F :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
   | [ H : Forall ?f ((_ ?F _) :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
   | [ H : Forall ?f ((_ _ ?F) :: ?M) |- ?f ?F ] => eapply @Forall_inv with (l:=M) (a:=F);auto
  
   | [ H : Forall ?f (?F :: ?M) |- Forall ?f ?M ] => apply Forall_inv_tail in H;auto 
   | [ H1 : Forall ?f ?M, H2 : Forall ?f ?N |- Forall ?f (?M++?N) ] => apply Forall_app;split;auto 
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?M  /\ Forall ?f ?N ] => apply Forall_app;auto 
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?M ] => apply Forall_app in H; destruct H;auto
   | [ H: Forall ?f (?M++?N) |-  Forall ?f ?N ] => apply Forall_app in H; destruct H;auto 
   | [ H: Forall ?f (?M++?N++?L) |-  Forall ?f ?L ] => rewrite app_assoc in H;solveForall
   | [ H: Forall ?f (?M++?N++?L) |-  Forall ?f ?N ] => rewrite Permutation_app_swap_app in H;solveForall
   | [ H: Forall ?f (?M++?F::?L) |-  ?f ?F ] => apply Forall_elt in H;auto
   | [ H: Forall ?f (?M++?F::?L) |-  Forall ?f [?F] ] => apply Forall_elt in H;auto
   | [ H: Forall ?f (?M++?F::?L) |-  Forall ?f ?L ] => rewrite Permutation_cons_append in H;solveForall

  
   | H: Forall ?f ?M  |- Forall ?f (_ :: ?M) => apply Forall_cons; auto  
   | H: Forall ?f ?M  |- Forall ?f (?M++[_]) => apply Forall_app;split;auto 
   | [ |- Forall ?f (?M++_) ] => apply Forall_app;split;solveForall
   |  |- Forall ?f (_ :: ?M) => apply Forall_cons; solveForall 
   
    end;auto.
    

(* Definition plusT L := map (fun x => 2+x) L.

Lemma asas M N: plusT (M++N) = plusT M ++ plusT N.
rewrite map_app. *)


  

 Ltac solveFoldFALL1 isP :=  
try
  match goal with
   | [  |- ?isPL nil] => autounfold 
   | [H: ?isPL (?K1++?K2++_) |- ?isPL (?K1++?K2)] => autounfold; rewrite app_assoc in H;autounfold in H
   | [H: ?isPL (?K1++_++?K2) |- ?isPL (?K1++?K2)] => autounfold; autounfold in H;rewrite Permutation_app_rot in H


   | [ H : ?isPL (?F :: ?M) |- isP ?F ] => autounfold in H
   | [ H : ?isPL (?F :: ?M) |- ?isPL ?M ] => autounfold;autounfold in H 
   | [ H1 : ?isPL ?M, H2 : ?isPL ?N |- ?isPL (?M++?N) ] => autounfold;autounfold in H1;autounfold in H2 
   | [ H: ?isPL (?M++?N) |-  ?isPL ?M  /\ ?isPL ?N ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N) |-  ?isPL ?M ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N) |-  ?isPL ?N ] => autounfold;autounfold in H 
   | [ H: ?isPL (?M++?N++?L) |-  ?isPL ?L ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?N++?L) |-  ?isPL ?N ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  isP ?F ] => autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  ?isPL [?F] ] => autounfold;autounfold in H
   | [ H: ?isPL (?M++?F::?L) |-  ?isPL ?L ] => autounfold;autounfold in H

  
   | H: ?isPL ?M  |- ?isPL (_ :: ?M) => autounfold;autounfold in H
   | H: ?isPL ?M  |- ?isPL (?M++_) => autounfold;autounfold in H 
   | H: ?isPL ?M  |- ?isPL (_++?M) => autounfold;autounfold in H 
   | [ H1 : ?isPL ?M, H2 : Permutation ?M ?N |- ?isPL ?N  ] => autounfold;autounfold in H1 
   | [ H1 : ?isPL ?M, H2 : Permutation ?N ?M |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?L) |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?L) ?M |- ?isPL ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?L) |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?L) ?M |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?F::?L) |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?F::?L) ?M |- ?isPL ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation ?M (?N++?F::?L) |- ?isPL [?F]  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL ?M, H2 : Permutation (?N++?F::?L) ?M |- ?isPL [?F]  ] => autounfold;autounfold in H1

   | [ |- ?isPL (?M++_) ] => autounfold
   |  |- ?isPL (_ :: ?M) => autounfold 
   
    end;solveForall.
    
 (*   Variable f: nat -> Prop.
   Definition isNat M := Forall f M.
   Hint Unfold isNat.
   Lemma asas M L : isNat L -> isNat (M++L).
      intros. solveFoldForall isNat f.
  *)      
   
 Ltac solveFoldFALL2 isP :=  
try
  match goal with
   | [  |- ?isPL _ nil] => autounfold 
    | [H: ?isPL _ (?K1++?K2++_) |- ?isPL _ (?K1++?K2)] => autounfold; rewrite app_assoc in H;autounfold in H
   | [H: ?isPL _ (?K1++_++?K2) |- ?isPL _ (?K1++?K2)] => autounfold; autounfold in H;rewrite Permutation_app_rot in H

   
   | [ H : ?isPL _ (?F :: ?M) |- isP ?F ] => autounfold in H
   | [ H : ?isPL _ (?F :: ?M) |- ?isPL _ ?M ] => autounfold;autounfold in H 
   | [ H1 : ?isPL _ ?M, H2 : ?isPL _ ?N |- ?isPL _ (?M++?N) ] => autounfold;autounfold in H1;autounfold in H2 
   | [ H: ?isPL _ (?M++?N) |-  ?isPL _ ?M  /\ ?isPL _ ?N ] => autounfold;autounfold in H
   | [ H: ?isPL _ (?M++?N) |-  ?isPL _ ?M ] => autounfold;autounfold in H
   | [ H: ?isPL _ (?M++?N) |-  ?isPL _ ?N ] => autounfold;autounfold in H 
   | [ H: ?isPL _ (?M++?N++?L) |-  ?isPL _ ?L ] => autounfold;autounfold in H
   | [ H: ?isPL _ (?M++?N++?L) |-  ?isPL _ ?N ] => autounfold;autounfold in H
   | [ H: ?isPL _ (?M++?F::?L) |-  isP ?F ] => autounfold in H
     | [ H: ?isPL _ (?M++?F::?L) |-  ?isPL _ [?F] ] => autounfold;autounfold in H
 | [ H: ?isPL _ (?M++?F::?L) |-  ?isPL _ ?L ] => autounfold;autounfold in H

  
   | H: ?isPL _ ?M  |- ?isPL _ (_ :: ?M) => autounfold;autounfold in H
   | H: ?isPL _ ?M  |- ?isPL _ (?M++_) => autounfold;autounfold in H 
   | H: ?isPL _ ?M  |- ?isPL _ (_++?M) => autounfold;autounfold in H 
   
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M ?N |- ?isPL _ ?N  ] => autounfold;autounfold in H1 
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?N ?M |- ?isPL _ ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?N++?L) |- ?isPL _ ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?N++?L) ?M |- ?isPL _ ?N  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?N++?L) |- ?isPL _ ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?N++?L) ?M |- ?isPL _ ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?F::?L) |- ?isPL _ ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?F::?L) ?M |- ?isPL _ ?L  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?N++?F::?L) |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?N++?F::?L) ?M |- isP ?F  ] => autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation ?M (?N++?F::?L) |- ?isPL _ [?F]  ] => autounfold;autounfold in H1
   | [ H1 : ?isPL _ ?M, H2 : Permutation (?N++?F::?L) ?M |- ?isPL _ [?F]  ] => autounfold;autounfold in H1
 

   
   | [ |- ?isPL _ (?M++_) ] => autounfold
   |  |- ?isPL _ (_ :: ?M) => autounfold 
   
    end;solveForall. 
 
        
Ltac checkPermutationCases H := simpl in H;
 let Hs := type of H in 
  match Hs with
  | Permutation (?P1::?L1) (?P2::?L2) => apply PProp_perm_select in H;sauto
  | Permutation  (?L1++?L2) (?L3++?P::nil) => symmetry in H;apply PProp_perm_sel in H;sauto
  | Permutation (?L3++?P::nil) (?L1++?L2) => apply PProp_perm_sel in H;sauto
  | Permutation  (?L1++?L2) (?P::?L3) => apply PProp_perm_select' in H;sauto
  | Permutation (?P::?L3) (?L1++?L2) => symmetry in H;apply PProp_perm_select' in H;sauto
end.

