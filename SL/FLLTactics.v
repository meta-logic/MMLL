(** * Tactics for the focused system

In order to use MMLL, this module must be imported. It defines useful
tactics for forward and backward (inversion) reasoning. Some useful
notations are also introduced.

As a general rule, tactics for the system without measures are names
with an apostrophe. For instance, [solveLL] for the system [seqN] and
[solveLL'] for the system [seq].
 *)

Require Export MMLL.SL.StructuralRules.
Require Export MMLL.SL.FLLTacticsPre.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section FLL. *)

Ltac contraction_set M := 
 eapply @contractionSet with (L:=M);intros;
    match goal with
    | [H: In ?F ?X |- In ?F ?Y] =>
      try apply in_or_app;intuition
    end.

(** Finishes the proof if H is a sequent that only needs some exchanges to be
equal to the goal *) 
Ltac llExact H :=
  let G:= type of H in
  match G with
  | (seqN ?T ?x ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seqN ?T ?y ?Gamma' ?Delta' ?X ] =>
      assert( x <= y) by lia;
      eapply @HeightGeqEx with (n:=x) (CC':=Gamma) (LC':=Delta);
      [try perm | try perm | auto | lia ]

    end 
  end;auto.


Ltac llExact' H :=
  let G:= type of H in
  match G with
  | (seq ?T ?Gamma ?Delta ?X) =>
    match goal with
    | [ |- seq ?T ?Gamma' ?Delta' ?X ] =>
      apply @exchangeCC with (CC:= Gamma);auto; try perm;
      apply @exchangeLC with (LC:= Delta);auto;try perm
    end
  end;auto.

Ltac LLExact H := 
  match (type of H) with
  | seq _ _ _ _  =>  llExact' H
  | seqN _ _ _ _ _ => llExact H
  end.
  
 (* Hypothesis with a higher proof than the one needed *)
Ltac HProof :=
auto; try
  match goal with
 | [ H : seqN ?th ?y ?G ?M ?X |- seqN ?th ?x ?G ?M ?X ] =>
    assert( y <= x) by lia;
    eapply @HeightGeq  with (m:=x) in H;auto
 | [ H : seqN ?th ?y ?G ?M ?X |- seqN ?th ?x ?G' ?M' ?X ] =>
    LLExact H
 | [ H : seq ?th ?y ?G ?M ?X |- seq ?th ?G' ?M' ?X ] =>
    LLExact H
 | [ H : seqN _ ?n ?G ?M ?X |-  seq _ ?G ?M ?X ] =>
    eapply seqNtoSeq in H;exact H
 | [ H : seqN _ ?n ?G ?M ?X |-  seq _ ?G' ?M' ?X ] =>
    eapply seqNtoSeq in H; LLExact H

 | [ H : tri_bangK4 _ ?n ?B ?i ?D ?M (UP ?L) |- tri_bangK4' _ ?B ?i ?D ?M (UP ?L)  ] =>
    eapply seqNtoSeq_mutual in H;[exact H;firstorder]    
  end.

Ltac solveLinearLogic :=
solveLL;try solve [HProof];
try
  match goal with
  | [H: seqN _ ?n ?B ?L (DW ?F) |- seqN _ ?m ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusL; HProof
  | [H: seqN _ ?n ?B ?L (DW ?G) |- seqN _ ?m ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusR; HProof 
  | [H: seqN _ ?n ?B ?L (DW ?F) |- seq _ ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusL; HProof
  | [H: seqN _ ?n ?B ?L (DW ?G) |- seq _ ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusR; HProof 
  | [H: seq _ ?B ?L (DW ?F) |- seq _ ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusL
  | [H: seq _ ?B ?L (DW ?G) |- seq _ ?B ?L (DW (AOr ?F ?G))] =>
      LLPlusR       
 end; try solveF.


(** This tactic must be used to reason by inversion on hypotheses
  containing FLL sequents. Must of the "irrelevant" cases (as, e.g.,
  assuming that focused can be lost on a positive formula) are
  discarded. *)
Ltac invTriStep H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | seqN _ _  _ _ (UP []) => inversion H;subst;solveF (* decision rules *)
  | seqN _ _  _ _ (UP ((One ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (UP ((Zero ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (UP ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | seqN _ _  _ _ (UP ((atom _ ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (UP ((perp _ ):: _)) => inversion H;subst (* Store *)
  | seqN _ _  _ _ (UP ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | seqN _ _  _ _ (UP ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | seqN _ _  _ _ (UP ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (UP ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (UP ((Bang _ _) :: _)) => inversion H;subst (* store *)
  | seqN _ _  _ _ (UP ((Quest _ _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | seqN _ _  _ _ (UP ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | seqN _ _  _ _ (UP ((Some _):: _) ) => inversion H;subst (* store *)
  | seqN _ _  _ _ (UP ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | seqN _ _  _ _ (DW (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | seqN _ _  _ _ (DW (AOr _ _)) => inversion H;subst;[idtac | idtac | solveF]  (* oplus --2nd branch contradictory *)
  | seqN _ _  _ _ (DW (Bang _ _)) => inversion H;subst;[idtac | solveF]  (* --2nd branch contradictory *)
  | seqN _ _  _ _ (DW  (perp _)) => apply FocusAtomN in H as H';inversion H';solveF (* [solveF | intro; apply True]*)  (* focus on an atom*)
  | seqN _ _  _ _ (DW  (atom _ )) => inversion H;subst (* release *)
  | seqN _ _  _ _ (DW  (Top)) => inversion H;subst (* top *)
  | seqN _ _  _ _ (DW  (Bot)) => inversion H;subst (* bot *)
  | seqN _ _  _ _ (DW  (Quest _ _)) => inversion H;subst (* quest *)
  | seqN _ _  _ _ (DW  (MOr _ _)) => inversion H;subst 
  | seqN _ _  _ _ (DW  (AAnd _ _)) => inversion H;subst (* with /release *)
  | seqN _ _  _ _ (DW  (All _) ) => inversion H;subst (* forall /release *)
  | seqN _ _  _ _ (DW (Some _) ) => inversion H;subst; [solveF | ] (* exists *)
  | seqN _ _  _ _ (DW (Zero) ) => inversion H;solveF 
  end.

Ltac invTri H := invTriStep H ; clear H.

(** Version without measures *)
Ltac invTri' H :=
  repeat autounfold in H;
  simpl in H;
  let F := type of H in
  let H' := fresh "H" in
  match F with
  | seq _  _ _ (UP []) => inversion H;subst;solveF (* decision rules *)
  | seq _  _ _ (UP ((One ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (UP ((Zero ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (UP ((Bot ):: _)) => inversion H;[subst | solveF] (* Bot *)
  | seq _  _ _ (UP ((Top):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* top *)
  | seq _  _ _ (UP ((atom _ ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (UP ((perp _ ):: _)) => inversion H;subst (* Store *)
  | seq _  _ _ (UP ((AAnd _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with  *)
  | seq _  _ _ (UP ((MOr _ _) :: _)) => inversion H;subst;[idtac | solveF ] (* with /release *)
  | seq _  _ _ (UP ((AOr _ _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (UP ((MAnd _ _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (UP ((Bang _ _) :: _)) => inversion H;subst (* store *)
  | seq _  _ _ (UP ((Quest _ _):: _) ) => inversion H;subst; [idtac | solveF];simpl in H (* quest *)
  | seq _  _ _ (UP ((All _):: _) ) => inversion H;subst; [solveF | idtac] (* forall /release *)
  | seq _  _ _ (UP ((Some _):: _) ) => inversion H;subst (* store *)
  | seq _  _ _ (DW (MAnd _ _)) => inversion H;subst;[idtac | solveF] (* tensor --2nd branch contradictory/release*)
  | seq _  _ _ (DW (AOr _ _)) => inversion H;subst;[idtac | idtac |  solveF] (* oplus --2nd branch contradictory/release*)
  | seq _  _ _ (DW (Bang _ _)) => inversion H;subst;[idtac | solveF] (* 2nd branch contradictory/release*)
(*  | seq _  _ _ (DW  (perp _)) => apply FocusAtom in H as H'; inversion H'; solveF  *)  (* focus on an atom*)
  | seq _  _ _ (DW  (atom _ )) => inversion H;subst (* release *)
  | seq _  _ _ (DW  (Top)) => inversion H;subst (* top *)
  | seq _  _ _ (DW  (Bot)) => inversion H;subst (* bot *)
  | seq _  _ _ (DW  (Quest _ _)) => inversion H;subst (* quest *)
  | seq _  _ _ (DW  (MOr _ _)) => inversion H;subst 
  | seq _  _ _ (DW  (AAnd _ _)) => inversion H;subst (* with /release *)
  | seq _  _ _ (DW  (All _) ) => inversion H;subst (* forall /release *)
  | seq _  _ _ (DW (Some _) ) => inversion H;subst; [solveF | ] (* exists *)
  | seq _  _ _ (DW (Zero ) ) => inversion H;solveF
  end;
  clear H.

Ltac FLLInversion H :=
  match (type of H) with
  | seq _ _ _ _  =>  invTri' ; clear H
  | seqN _ _ _ _ _ => invTriStep H ; clear H
end.

    

(* Applies, possibly several times, inversion (invTri) on the 
    hypothesis containing focused sequents. It stops when the negative 
    phase ends ([Gamma ; Delta ; > []])
 *)

Ltac FLLInversionAll :=
  repeat
    match goal with
    | [H : seqN _ _ _ _ (DW _) |- _ ] => invTri H
    | [H : seqN _ _ _ _ (UP (?C :: _)) |- _ ] => invTri H
    | [H : seq _ _ _ (DW _) |- _ ] => invTri' H
    | [H : seq _ _ _ (UP (?C :: _)) |- _ ] => invTri' H
    end.
  

(* Check if the permutation P applies to the sequent in H and rewrites it *)
Ltac LLPermH H LI :=
  match goal with
  | [ H : seqN _ _ _ _ _ |- _] =>
          first[ apply exchangeLCN with (LC' := LI) in H ;[|sauto]
               | apply exchangeCCN with (CC' := LI) in H ;[|sauto]]
  | [ H : seq _ _ _ _ |- _] =>
          first[ apply exchangeLC with (LC' := LI) in H ;[|sauto]
               | apply exchangeCC with (CC' := LI) in H ;[|sauto]]
  | [ H : tri_bangK4 _ _ _ _ _ _ _ |- _] =>
          first[ apply exchangeCCNK4 with (CC' := LI) in H ;[|sauto]
               | apply exchangeCCNKK4 with (CC' := LI) in H ;[|sauto]]
  | [ H : tri_bangK4' _ _ _ _ _ _ |- _] =>
          first[ apply exchangeCCK4 with (CC' := LI) in H ;[|sauto]
               | apply exchangeCCKK4 with (CC' := LI) in H ;[|sauto]]
  end.


Ltac LLrew1 H1 H2 :=
 let G1:= type of H1 in
  match G1 with
  | Permutation ?A ?B => 
       let G2:= type of H2 in
         match G2 with
         | seq _ ?A _ _  =>
           eapply exchangeCC in H2; [| exact H1]
         | seq _ ?B _ _  =>
           eapply exchangeCC in H2; [| symmetry in H1; exact H1]
         | seq _ _ ?A _  =>
           eapply exchangeLC in H2; [| exact H1]
         | seq _ _ ?B _  =>
           eapply exchangeLC in H2; [| symmetry in H1; exact H1]
         
         | seqN _ _ ?A _ _  =>
           eapply exchangeCCN in H2; [| exact H1]
         | seqN _ _ ?B _ _  =>
           eapply exchangeCCN in H2; [| symmetry in H1; exact H1]
         | seqN _ _ _ ?A _  =>
           eapply exchangeLCN in H2; [| exact H1]
         | seqN _ _ _ ?B _  =>
           eapply exchangeLCN in H2; [| symmetry in H1; exact H1]
         
         | _ => idtac H2 "must to be a LL sequent"    
     end 
  | _ => idtac H1 "must to be a permutation"    
 end.

Ltac LLrew2 H :=
 let G:= type of H in
  match G with
  | Permutation ?A ?B => 
         match goal with
         | [ |- seq _ ?A _ _]  =>
           eapply (exchangeCC H)
         | [ |- seq _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCC H);
           symmetry in H
         | [ |- seq _ _ ?A _ ] =>
           eapply (exchangeLC H)
         | [ |- seq _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLC H);
           symmetry in H
          | [ |- seqN _ _ ?A _ _]  =>
           eapply (exchangeCCN H)
         | [ |- seqN _ _ ?B _ _ ] =>
           symmetry in H;
           eapply (exchangeCCN H);
           symmetry in H
         | [ |- seqN _ _ _ ?A _ ] =>
           eapply (exchangeLCN H)
         | [ |- seqN _ _ _ ?B _]  =>
           symmetry in H;
           eapply (exchangeLCN H);
           symmetry in H
         | _ => idtac "This goal is not compatible with " H    
     end 
  | _ => idtac H "must to be a permutation"    
 end.

 Tactic Notation "LLrewrite" constr(H) := LLrew2 H. 
 Tactic Notation "LLrewrite" constr(H1) "in" constr(H2) := LLrew1 H1 H2.

 Tactic Notation "LLSplit" :=  
     match goal with
      | [ |- seq _ ?B _ _]  => LLrewrite (symmetry (cxtDestruct B))
      | [ |- seqN _ _ ?B _ _]  => LLrewrite (symmetry (cxtDestruct B))
     end.
     
  Tactic Notation "LLSplit" "in" constr(H)  :=  
     match type of H with
      | seq _ ?B _ _  => LLrewrite (cxtDestruct B) in H
      | seqN _ _ ?B _ _  => LLrewrite (cxtDestruct B) in H
     end.    
        
  
Ltac LLPerm LI :=
  match goal with
  | [ |- seqN _ _ _ _ _ ] =>
          first[ apply exchangeLCN with (LC := LI);[sauto|]
               | apply exchangeCCN with (CC := LI);[sauto|]]
  | [ |- seq _ _ _ _ ] =>
          first[ apply exchangeLC with (LC := LI);[sauto|]
               | apply exchangeCC with (CC := LI);[sauto|]]
  | [ |- tri_bangK4 _ _ _ _ _ _ _ ] =>
          first[ apply exchangeCCNK4 with (CC := LI);[sauto|]
               | apply exchangeCCNKK4 with (CC := LI);[perm|]]
  | [ |- tri_bangK4' _ _ _ _ _ _ ] =>
          first[ apply exchangeCCK4 with (CC := LI);[sauto|]
               | apply exchangeCCKK4 with (CC := LI);[sauto|]]
end.
  
(** This version of [LLPerm] first simplifies the parameter LI *)
Ltac sLLPermH H LI :=
  let LI' := (eval cbn in LI ) in
  let LI'' := constr:(LI') in
  LLPermH H LI''.

Ltac sLLPerm LI :=
  let LI' := (eval cbn in LI ) in
  let LI'' := constr:(LI') in
  LLPerm LI''.
(** "rewrite perm_swap in H" would be enough for exchanging the first 2
elements of a list. However, such rewrite is quite slow (probably for
Coq's search mechanism in Class Instances). This tactic implement the
same step without using rewriting *)
Ltac LLSwapH H :=
        let Hs := type of H in 
        match Hs with
        |  (seqN _ _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCCN with (CC':= (G :: F :: L)) in H;[|perm]
        |  (seq  _ (?F :: ?G :: ?L) _ _) =>
           apply exchangeCC with (CC':= (G :: F :: L)) in H;[|perm]
        end.

Ltac LLSwap :=
  match goal with
  | [ |-seqN _ _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-seqN _ _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  | [ |-seq  _ (?A :: ?B :: ?G) _ _] => LLPerm (B :: A :: G)
  | [ |-seq  _ _ (?A :: ?B :: ?G) _] => LLPerm (B :: A :: G)
  end.

Ltac finishExponential :=  match goal with
  | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: m4 ?a = true, H3: u ?a = true |- _ ] => 
       let a := fresh "CK4" in
       let c := fresh "CN" in
        apply InvSubExpPhaseUK4 in H; 
        [ destruct H as [a H];
          destruct H as [c H];CleanContext | auto | auto | try solve[auto | intro;subst;solveSubExp] ]           

    | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: u ?a = true |- _ ] => 
     let a := fresh "CK4" in
     let b := fresh "CK" in
     let c := fresh "CN" in
        apply InvSubExpPhaseU in H; 
        [ destruct H as [a H];
          destruct H as [b H];
          destruct H as [c H];CleanContext | auto | try solve[auto | intro;subst;solveSubExp] ]; idtac H2    
    | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L), H2: m4 ?a = true |- _ ] => 
       let a := fresh "CK4" in
       let c := fresh "CN" in
        apply InvSubExpPhaseK4 in H; 
        [ destruct H as [a H];
          destruct H as [c H];CleanContext | auto | try solve[auto | intro;subst;solveSubExp] ]           
    | [ H: tri_bangK4 ?th ?n ?B ?a ?D ?O (UP ?L) |- _ ] => 
     let a := fresh "CK4" in
     let b := fresh "CK" in
     let c := fresh "CN" in
        apply InvSubExpPhase in H;
        [ destruct H as [a H];
         destruct H as [b H];
         destruct H as [c H];CleanContext |  try solve[auto | intro;subst;solveSubExp] ]
    end.


