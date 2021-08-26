(** * Definitions for the OL Cut-Elimination Theorem  *)

(** This file contains some useful definitions and tactics for the
proof of the cut-elimination theorem of Object Logics *)

Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.OLSyntax.
Require Import Coq.Init.Nat.
Require Import MMLL.SL.CutElimination.
Import MMLL.Misc.Permutations.
Import Coq.Init.Datatypes.
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.

Section PositiveAtoms.
  Context `{OL: OLSyntax}.
  Context `{SI: Signature}.
  (** Positive atoms are only [down] and [up] atoms. The linear and
  the classical context of the encoding must contain only formulas of
  this kind *)
  Inductive IsPositiveAtomFormula : oo -> Prop :=
  | IsFPA_dw : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (down (A)))
  | IsFPA_up : forall A, isOLFormula A -> IsPositiveAtomFormula (atom (up (A))).
  Local Hint Constructors IsPositiveAtomFormula : core .

  
  Definition IsPositiveAtomFormulaL L : Prop := Forall IsPositiveAtomFormula L.
  Local Hint Unfold IsPositiveAtomFormulaL : core. 
  Local Hint Constructors IsPositiveAtomFormula : core. 
 
  
   Global Instance perm_IsPositiveAtomFormulaL  :
      Proper (@Permutation oo ==> Basics.impl)
             (IsPositiveAtomFormulaL ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl.
      intros.
      unfold IsPositiveAtomFormulaL.
      rewrite <- H;auto.
    Qed.

  Lemma PositiveAtomIn : forall F A Gamma,
      In F (atom A :: Gamma) ->
      IsPositiveAtomFormulaL Gamma ->
      IsPositiveAtom F.
    intros.
    inversion H;subst;auto.
    unfold IsPositiveAtomFormulaL in H0.
    apply Forall_forall with (x:= F) in H0;auto.
    inversion H0;subst;auto.
  Qed.

  Lemma IsPositiveConsInv :
    forall M N A, isOLAtom A ->
                  Permutation N ( (atom (up A) ) :: M) ->
                  IsPositiveAtomFormulaL M ->
                  IsPositiveAtomFormulaL N.
  Proof with sauto.
    intros.
    assert (IsPositiveAtomFormulaL ((atom (up A) ) :: M)).
    constructor;auto.
    inversion H...  
    apply Permutation_sym in H0.
     generalize (PermuteMap H2 H0) ;auto.
  Qed.

  Lemma IsPositiveConsInvF :
    forall M N A, isOLFormula A ->
                  Permutation N ( (atom (up A) ) :: M) ->
                  IsPositiveAtomFormulaL M ->
                  IsPositiveAtomFormulaL N.
  Proof with solveF.
    intros.
    assert (IsPositiveAtomFormulaL ( (atom (up A) ) :: M)).
    constructor;auto.
    apply Permutation_sym in H0.
    generalize (PermuteMap H2 H0) ;auto.
  Qed.
  
  Lemma IsPosL0 :
    forall A N M G  L L',
      isOLFormula A ->
      IsPositiveAtomFormulaL N ->
      Permutation ((atom (up A) ) :: M) ((( atom (up A) ) :: L) ++ L') ->
      Permutation N (G :: M) ->
      IsPositiveAtomFormulaL L.
  Proof with subst;auto.
    intros.
    generalize (PermuteMap H0 H2);intro.
    inversion H3 ...
    assert( IsPositiveAtomFormulaL ((atom (up A) ) :: M))...
    generalize (PermuteMap H4 H1);intro.
    apply Forall_app in H5.
    inversion H5...
    inversion H8...
  Qed.

  Lemma IsPosL1 :
    forall M F L A X, IsPositiveAtomFormulaL M ->
                      Permutation M (F :: L) ->
                      IsPositiveAtomFormula A ->
                      Permutation X  ( A   :: L) ->
                      IsPositiveAtomFormulaL X.
    intros.
    Proof with subst;auto. 
      generalize (PermuteMap H H0);intro.
      inversion H3...
      apply Forall_cons with (x:= A) in H7 ...
      apply Permutation_sym in H2.
      eauto using PermuteMap.
    Qed.
    
    Lemma isPosL2 :
      forall N MN' M N0, IsPositiveAtomFormulaL N ->
                         Permutation N MN' ->
                         Permutation MN' (M ++ N0) ->
                         IsPositiveAtomFormulaL M.
      intros.
      generalize (PermuteMap H H0);intro.
      generalize (PermuteMap H2 H1);intro.
      apply Forall_app in H3.
      inversion H3;auto.
    Qed.

    Lemma isPosL3 :
      forall N MN' M N0, IsPositiveAtomFormulaL N ->
                         Permutation N MN' ->
                         Permutation MN' (M ++ N0) ->
                         IsPositiveAtomFormulaL N0.
      intros.
      generalize (PermuteMap H H0);intro.
      generalize (PermuteMap H2 H1);intro.
      apply Forall_app in H3.
      inversion H3;auto.
    Qed.

    Lemma isPosL4 :
      forall A N M A1 A2,  IsPositiveAtomFormula A ->
                           IsPositiveAtomFormulaL N ->
                           Permutation (A :: N) (A1 :: A2 :: M) ->
                           IsPositiveAtomFormulaL M.
      intros.
      apply Permutation_sym in H1.
      assert (H' : forall F, In F M ->  In F (A :: N)).
      intros FF H''; apply Permutation_in with (x:= FF) in H1;auto;do 2 eapply in_cons in H'';eauto.
      assert (H''' : IsPositiveAtomFormulaL (A :: N)) by auto.
      apply Forall_forall;intros.
      unfold IsPositiveAtomFormulaL in H'''.
      rewrite Forall_forall in H''';auto.
    Qed.

    Lemma IsPositiveAtomNotAsync :
      forall N, IsPositiveAtomFormulaL N ->  isNotAsyncL  N.
      
      induction N;simpl;auto;intros.
      apply Forall_forall; intros x Hx; inversion Hx.
      inversion H;subst.
      change  (a :: N) with ( [a] ++ N).
      apply Forall_app;split;auto.
      
      2:{ apply IHN;auto. }
      
      inversion H2;subst;auto.
      apply Forall_forall; intros x Hx;inversion Hx;subst;auto.
      intro Hc;inversion Hc.
      inversion H1.
      apply Forall_forall; intros x Hx;inversion Hx;subst;auto.
      intro Hc;inversion Hc.
      inversion H1.
    Qed.

    Lemma IsPositiveIsFormula :
      forall N, IsPositiveAtomFormulaL N ->  isFormulaL  N.
      intros.
      induction H.
      constructor.
      inversion H;subst;
      constructor;auto;
      constructor;auto.
    Qed.

    Lemma PermIsFormula :
      forall N M, Permutation N M -> IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL M.
      intros.
      eauto using PermuteMap.
    Qed.

    
    Lemma PermIsFormula' :
      forall N M, Permutation M N -> IsPositiveAtomFormulaL N ->
                  IsPositiveAtomFormulaL M.
      intros.
      apply Permutation_sym in H.
      eauto using PermuteMap.
    Qed.
    
    Lemma RemoveNotPos1 F M L: ~ IsPositiveAtom F -> IsPositiveAtomFormulaL M -> Remove F M L -> False.
Proof with sauto.
  intros.
  apply Remove_Permute in H1...
  destruct L...
  inversion H0...
  inversion H3...
  rewrite H1 in H0.
  inversion H0...
  inversion H4...
Qed. 

Lemma RemoveNotPos2 (i:subexp) F M L: ~ IsPositiveAtom F -> IsPositiveAtomFormulaL (second M) -> Remove (i,F) M L -> False.
Proof with sauto.
  intros.
  apply Remove_Permute in H1...
  destruct L...
  inversion H0...
  inversion H3...
  eapply Permutation_map with (f:=snd) in H1. 
  rewrite H1 in H0.
  inversion H0...
  inversion H4...
Qed. 

Lemma InUNotPos (i:subexp) F L: ~ IsPositiveAtom F -> IsPositiveAtomFormulaL (second L) -> In (i, F) L -> False.
Proof with sauto.
  induction L;intros...
  inversion H1...
  inversion H0...
  inversion H3...
  apply IHL in H2...
  inversion H0...
Qed.

    
End PositiveAtoms.

Global Hint Constructors IsPositiveAtomFormula : core.
Global Hint Unfold IsPositiveAtomFormulaL: core.  

(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
  Context `{OL: OLSyntax}.
  Context `{SI: Signature}.
  
  Inductive Side := Left | Right .

  (** Encoding of inference rules for units *)
  Record ruleCte :=
    {
      rc_rightBody : oo ; (* body of the right rule *)
      rc_leftBody : oo  (* body of the left rule *)
    } .

  (** Encoding of inference rules for unary connectives *)
  Record ruleUnary := 
    {
      ru_rightBody : uexp -> oo; 
      ru_leftBody : uexp ->  oo 
    }.
  
  (** Encoding of inference rules for binary connectives *)
  Record ruleBin := 
    {
      rb_rightBody : uexp -> uexp -> oo; 
      rb_leftBody : uexp -> uexp -> oo 
    }.

  (** Encoding of inference rules for quantifiers *)
  Record ruleQ := 
    {
      rq_rightBody : (uexp -> uexp) -> oo; (* body of the right rule *)
      rq_leftBody :  (uexp -> uexp) -> oo (* body of the left rule *)
    }.

  
  (** We assume an external definition mapping each
    connective/quantifier with a left and right rule *) 
  Class OORules :=
    {
      rulesCte : constants -> ruleCte ;
      rulesUnary : uconnectives -> ruleUnary;
      rulesBin : connectives -> ruleBin;
      rulesQ :   quantifiers -> ruleQ
    }.
  
End OLInferenceRules.



Section OLEncodings.
  Context `{OL: OLSyntax}.
  Context `{SI: Signature}.
  
  Definition LEncode L:= 
        map (fun x => d| x|) L.
  Definition REncode L:= 
        map (fun x => u| x|) L.
  Definition CEncode (i:subexp) (L:list oo) : list (subexp*oo) := 
        map (fun x => (i,x)) L.
 
Lemma LEncodeApp  L1 L2 : LEncode (L1++L2) = LEncode L1 ++ LEncode  L2.
Proof with sauto.
 unfold LEncode;
 rewrite map_app;auto.
Qed.

Lemma REncodeApp  L1 L2 : REncode (L1++L2) = REncode L1 ++ REncode  L2.
Proof with sauto.
 unfold REncode;
 rewrite map_app;auto.
Qed.

Lemma CEncodeApp i L1 L2 : CEncode i (L1++L2) = CEncode i L1 ++ CEncode i  L2.
Proof with sauto.
 unfold CEncode;
 rewrite map_app;auto.
Qed.

Lemma LEncodePerm L1 L2 : Permutation L1 L2 -> Permutation (LEncode L1) (LEncode L2).
   Proof.
   intros.
   apply Permutation_map;auto.
   Qed.                 

Lemma REncodePerm L1 L2 : Permutation L1 L2 -> Permutation (REncode L1) (REncode L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

Lemma CEncodePerm i L1 L2 : Permutation L1 L2 -> Permutation (CEncode i L1) (CEncode i L2).
Proof.
   intros.
   apply Permutation_map;auto.
Qed.                 

 Definition isLeftF (F:oo) := 
     match F with 
     | (atom (up' A)) => true
     | _ => false
 end.
 
 Definition isRightF (F:oo) := 
     match F with 
     | (atom (down' A)) => true
     | _ => false
 end.

  Definition getLeftF (l : list oo ) := filter isLeftF l.
  Definition getRightF (l : list oo ) := filter isRightF l.


Theorem posDestruct K: IsPositiveAtomFormulaL K -> Permutation K (getLeftF K++getRightF K).
 Proof with sauto.
 induction K;intros...
 inversion H...
 inversion H2...
 simpl. 
 apply Permutation_cons_app;auto.
 simpl...
Qed.

 Theorem posDestruct' K: IsPositiveAtomFormulaL K -> exists K1 K2, Permutation K (LEncode K1 ++ REncode K2).
 Proof with sauto.
 induction K;intros...
 exists [].
 exists [].
 simpl;auto.
 inversion H...
 inversion H2...
 - destruct IHK...
   exists (A::x).
   exists x0.
   simpl...
 - destruct IHK...
   exists x.
   exists (A::x0).
   simpl.
   rewrite H1...
 Qed.  

(*  Lemma secondCon (L: list TypedFormula): L = combine (first L) (second L).
 Proof with sauto.
 induction L;simpl;intros...
 
 rewrite <- IHL...
 destruct a...
 Qed.
 *) 

 Theorem destructREncode C: forall D1 D2, Permutation (REncode C) (D1++D2) ->
       exists X Y, Permutation D1 (REncode X) /\ Permutation D2 (REncode Y) /\ Permutation C (X++Y). 
Proof with sauto.
 induction C;intros...
 simpl in H...
 exists nil...
 exists nil...
 simpl in H.
 checkPermutationCases H.
 - symmetry in H1.
   eapply IHC in H1...
   exists (a::x0).
   exists x1...
   rewrite H0...
   rewrite H1...
   rewrite H4...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0.
   exists (a::x1)...
   rewrite H0...
   rewrite H3...
   rewrite H4...
Qed.

Theorem destructLEncode C: forall D1 D2, Permutation (LEncode C) (D1++D2) ->
       exists X Y, Permutation D1 (LEncode X) /\ Permutation D2 (LEncode Y) /\ Permutation C (X++Y). 
Proof with sauto.
 induction C;intros...
 simpl in H...
 exists nil...
 exists nil...
 simpl in H.
 checkPermutationCases H.
 - symmetry in H1.
   eapply IHC in H1...
   exists (a::x0).
   exists x1...
   rewrite H0...
   rewrite H1...
   rewrite H4...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0.
   exists (a::x1)...
   rewrite H0...
   rewrite H3...
   rewrite H4...
Qed.
  
   Theorem destructEncode C1 C1' C2 C2': 
    Permutation (LEncode C1 ++ REncode C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (LEncode K4_1 ++ REncode K4_2) /\ 
    Permutation C2' (LEncode K4_3 ++ REncode K4_4) /\ 
    Permutation C1 (K4_1 ++ K4_3) /\ 
    Permutation C2 (K4_2 ++ K4_4). 
  Proof with sauto.
    intros.
    revert dependent C1'.
    revert dependent C2.
    revert dependent C2'.
    induction C1;intros...
    * simpl in *... 
      apply destructREncode in H...
      eexists []. 
      eexists x. 
      eexists []. 
      eexists x0.
      split;auto...
    *
      simpl in H.
      checkPermutationCases H.
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists (a::x0).
         eexists x1.
         eexists x2.
         eexists x3.
         split;auto...
         rewrite H0.
         rewrite H1...
         rewrite <- app_comm_cons.
         rewrite H2...
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists x0.
         eexists x1.
         eexists (a::x2).
         eexists x3.
         split;auto...
         rewrite H0.
         simpl.
         rewrite H3...
         rewrite H2...

 Qed.          

Lemma setUCEncode i L : u i = true -> SetU (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 apply IHL...
Qed.
 
Lemma setK4CEncode i L : SetK4 i (CEncode loc L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H...
 assert(i=loc).
 apply locAlone'...
 subst.
 rewrite loc4 in H0...
Qed.

 
Lemma setKCEncode i L : SetK i (CEncode loc L) -> L=[] \/ i = loc.
Proof with sauto.
 induction L;simpl;intros...
 inversion H...
 assert(i=loc).
 apply locAlone'...
 right...
Qed.

Lemma setK4DCEncode i j L : md i = true -> md j = false -> SetK4 i (CEncode j L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H1...
 assert(md j = true).
 apply mdClosure with (x:=i)...
 rewrite H4 in H0...
Qed.

Lemma setKDCEncode i j L : md i = true -> md j = false -> SetK i (CEncode j L) -> L = [].
Proof with sauto.
 induction L;simpl;intros...
 inversion H1...
 assert(md j = true).
 apply mdClosure with (x:=i)...
 rewrite H4 in H0...
Qed.

Lemma setTCEncode i L : mt i = true -> SetT (CEncode i L).
Proof with sauto.
 induction L;simpl;intros...
 apply Forall_cons...
 apply IHL...
Qed.

Lemma secCEncode i L : second (CEncode i L) = L.
Proof with auto.
 induction L...
 simpl.
 rewrite IHL...
Qed. 

 
Lemma LocCEncode L : (CEncode loc (second L)) = Loc L.
Proof with auto.
 induction L...
 simpl.
 rewrite IHL...
Qed.  
 
Lemma getUCEncode i L : u i = true -> getU (CEncode i L) = CEncode i L.
Proof with auto.
intros. 
 induction L;intros...
 simpl. 
 rewrite H...
 rewrite IHL...
Qed.

Lemma getLCEncode i L : u i = true -> getL (CEncode i L) = [].
Proof with auto.
intros. 
 induction L;intros...
 simpl. 
 rewrite H...
Qed.

Lemma getULCEncode  L : getU (CEncode loc L) = CEncode loc L.
Proof with sauto.
  apply getUCEncode...
  apply locu.
Qed.
 
 
 Lemma LocCEncodeLoc  L : Loc (CEncode loc L) = CEncode loc L.
Proof with auto.
 induction L;intros...
 simpl. 
 rewrite IHL...
Qed.  
   
    Lemma PositiveAtomREOLFormula L : IsPositiveAtomFormulaL (REncode L) -> isOLFormulaL L.
 intros.
 induction L;intros;auto.
 simpl in H.
 inversion H;subst;auto.
 apply IHL in H3...
 apply Forall_cons;auto.
 inversion H2;subst;auto.
Qed.

 Lemma PositiveAtomLEOLFormula L : IsPositiveAtomFormulaL (LEncode L) -> isOLFormulaL L.
 intros.
 induction L;intros;auto.
 simpl in H.
 inversion H;subst;auto.
 apply IHL in H3...
 apply Forall_cons;auto.
 inversion H2;subst;auto.
Qed.
   
 Theorem destructCEncode i C: forall D1 D2, Permutation (CEncode i C) (D1++D2) ->
       exists X Y, Permutation D1 (CEncode i X) /\ Permutation D2 (CEncode i Y) /\
       Permutation C (X++Y). 
Proof with sauto.
 induction C;intros...
 simpl in H...
 exists nil...
 exists nil...
 simpl in H.
 checkPermutationCases H.
 - symmetry in H1.
   eapply IHC in H1...
   exists (a::x0).
   exists x1...
   rewrite H0...
   rewrite H1...
   rewrite H4...
 - symmetry in H1.
   eapply IHC in H1...
   exists x0.
   exists (a::x1)...
   rewrite H0...
   rewrite H3...
   rewrite H4...
Qed.

 Theorem destructEncode2 i j C1 C1' C2 C2': 
    Permutation (CEncode i C1 ++ CEncode j C2) (C1' ++ C2') -> 
    exists K4_1 K4_2 K4_3 K4_4, 
    Permutation C1' (CEncode i K4_1 ++ CEncode j K4_2) /\ 
    Permutation C2' (CEncode i K4_3 ++ CEncode j K4_4) /\ 
    Permutation C1 (K4_1 ++ K4_3) /\ 
    Permutation C2 (K4_2 ++ K4_4). 
  Proof with sauto.
    intros.
    revert dependent C1'.
    revert dependent C2.
    revert dependent C2'.
    induction C1;intros...
    * simpl in *... 
      apply destructCEncode in H...
      eexists []. 
      eexists x. 
      eexists []. 
      eexists x0.
      split;auto...
    *
      simpl in H.
      checkPermutationCases H.
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists (a::x0).
         eexists x1.
         eexists x2.
         eexists x3.
         split;auto...
         rewrite H0.
         rewrite H1...
         rewrite <- app_comm_cons.
         rewrite H2...
      - symmetry in H1.  
         eapply IHC1 in H1...
         eexists x0.
         eexists x1.
         eexists (a::x2).
         eexists x3.
         split;auto...
         rewrite H0.
         simpl.
         rewrite H3...
         rewrite H2...
 Qed.          
  

  Lemma isOLLEncode : forall L, isOLFormulaL L -> IsPositiveAtomFormulaL (LEncode L).
  Proof with subst;auto.
    intros.
    induction L; simpl...
    constructor.
    inversion H...
    apply IHL...
    inversion H...
  Qed.

  
  Lemma isOLREncode : forall L, isOLFormulaL L -> IsPositiveAtomFormulaL (REncode L).
  Proof with subst;auto.
    intros.
    induction L; simpl...
    constructor.
    inversion H...
    apply IHL...
    inversion H...
  Qed.

  Lemma PermutationLEncode : forall L a x x1,
      Permutation (LEncode L) (d| a | :: x) -> Permutation (a :: x1) L -> Permutation x (LEncode x1).
  Proof with subst;auto.
    intros.      
    assert(Permutation (d| a | :: x) (LEncode ((a :: x1)))).
    {  symmetry.
       symmetry in H.
       apply Permutation_map_inv in H.
       do 2 destruct H.
       rewrite H.
       apply Permutation_map.
       simpl.
       rewrite <- H1.
       unfold LEncode.
       rewrite <- H0;auto.
      }
    simpl in H1.
    eapply (Permutation_cons_inv H1).
  Qed.

  Lemma PermutationREncode : forall L a x x1,
      Permutation (REncode L) (u| a | :: x) -> Permutation (a :: x1) L -> Permutation x (REncode x1).
  Proof with subst;auto.
    intros.      
    assert(Permutation (u| a | :: x) (REncode ((a :: x1)))).
    {  symmetry.
       symmetry in H.
       apply Permutation_map_inv in H.
       do 2 destruct H.
       rewrite H.
       apply Permutation_map.
       simpl.
       rewrite <- H1.
       unfold REncode.
       rewrite <- H0;auto.
      }
    simpl in H1.
    eapply (Permutation_cons_inv H1).
  Qed.


  Lemma InLEncode : forall L a,
      In (d| a |) (LEncode L) <-> In a L.
  Proof with sauto.
    split;induction L;simpl;intros...
    inversion H0...
  Qed.

 Lemma InREncode : forall L a,
      In (u| a |) (REncode L) <-> In a L.
  Proof with sauto.
    split;induction L;simpl;intros...
    inversion H0...
  Qed.

  Lemma isOLFormulaIn : forall F L, 
      isOLFormulaL L -> In F L -> isOLFormula F. 
  Proof.
    intros.
    unfold isOLFormulaL in H.
    generalize (Forall_forall isOLFormula L );intro.
    destruct H1.
    apply H1 with (x:= F) in H ;auto.
  Qed.

  Theorem NoDinR : forall F L, In (d| F|) (REncode L) -> False .
  Proof with sauto.  
    intros.
    induction L;auto.
    simpl in H...
  Qed.

  Theorem NoUinL : forall F L, In (u| F|) (LEncode L) -> False .
  Proof with sauto.  
    intros.
    induction L;auto.
    simpl in H...
  Qed.

  Theorem NoDinR' : forall F L x, Permutation (REncode L) (d| F|::x) -> False .
  Proof with sauto.  
    intros.
    eapply NoDinR with (F:=F) (L:=L).
    rewrite H...
  Qed.

  Theorem NoUinL' : forall F L x, Permutation (LEncode L) (u| F|::x)  -> False .
  Proof with sauto.  
    intros.
    eapply NoUinL with (F:=F) (L:=L).
    rewrite H...
  Qed.
  
  Theorem downLeft : forall L L' F,
      In (d| F |) (LEncode L ++ REncode L') ->
      In (d| F |) (LEncode L).
  Proof with sauto.  
    intros.
    apply in_app_or in H...
    apply NoDinR in H0...
  Qed.
  
  
  Theorem upRight : forall L L' F,
    In (u| F |) (LEncode L ++ REncode L') ->
    In (u| F |) (REncode L').
  Proof with sauto.  
    intros.
    apply in_app_or in H...
    apply NoUinL in H0...
  Qed.

  Theorem OLInPermutation: forall L F,
      In (u| F |) (REncode L) ->
      exists L', Permutation L (F:: L').
    induction L;intros.
    inversion H.
    simpl in H.
    inversion H.
    inversion H0;subst.
    eexists;eauto.
    apply IHL in H0.
    CleanContext;sauto.
    exists L;auto.
    exists (a:: x).
    rewrite H0;perm.
  Qed.

Lemma MapREncodeEqual: forall L L', (REncode L) = (REncode L') -> L = L'.
Proof with sauto.
  induction L;intros;simpl in *...
  erewrite map_eq_nil...
  exact (symmetry H).
  destruct L'...
  simpl in H.
  inversion H...
  erewrite IHL;auto.
Qed.  

Lemma MapLEncodeEqual: forall L L', (LEncode L) = (LEncode L') -> L = L'.
Proof with sauto.
  induction L;intros;simpl in *...
  erewrite map_eq_nil...
  exact (symmetry H).
  destruct L'...
  simpl in H.
  inversion H...
  erewrite IHL;auto.
Qed.   

Lemma UpREncode P1 P2 L1 L2 :
    Permutation (u| P1 |::REncode L1) (u| P2 |:: REncode L2) ->
    (
      P1 = P2 /\ Permutation (REncode L1) (REncode L2)
    ) \/ (
      exists L2',
        Permutation (REncode L2) (u| P1 |::REncode L2') /\
        Permutation (REncode L1) (u| P2 |::REncode L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (u| P1 |) (REncode L1)).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - inversion HI... 
    left.
    split;auto.
    apply Permutation_cons_inv in HP;auto.
  - right.
    apply in_map_iff in HI...
    inversion H0...
    destruct (in_split _ _ H1) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      rewrite !REncodeApp.
      simpl... 
    + assert(Permutation (REncode L1) (REncode (  P2 :: L2A ++ L2B))).
      eapply Permutation_cons_inv with (a:=u| P1 |).
      rewrite HP.
      rewrite HL2.
      simpl... 
      rewrite !REncodeApp.
      simpl...
      rewrite H...
Qed.

Lemma DwLEncode P1 P2 L1 L2 :
    Permutation (d| P1 |::LEncode L1) (d| P2 |::LEncode L2) ->
    (
      P1 = P2 /\ Permutation (LEncode L1) (LEncode L2)
    ) \/ (
      exists L2',
        Permutation (LEncode L2) (d| P1 |::LEncode L2') /\
        Permutation (LEncode L1) (d| P2 |::LEncode L2')
    ).
Proof with sauto.
  intro HP.
  assert (HI:=in_eq  (d| P1 |) (LEncode L1)).
  rewrite HP in HI.
  destruct HI as [HI|HI].
  - inversion HI... 
    left.
    split;auto.
    apply Permutation_cons_inv in HP;auto.
  - right.
    apply in_map_iff in HI...
    inversion H0...
    destruct (in_split _ _ H1) as (L2A,(L2B,HL2)).
    exists (L2A++L2B).
    split.
    + rewrite HL2.
      rewrite !LEncodeApp.
      simpl... 
    + assert(Permutation (LEncode L1) (LEncode (  P2 :: L2A ++ L2B))).
      eapply Permutation_cons_inv with (a:=d| P1 |).
      rewrite HP.
      rewrite HL2.
      simpl... 
      rewrite !LEncodeApp.
      simpl...
      rewrite H...
Qed.
  
Theorem OLInPermutation': forall L x F,
     Permutation (REncode L) (u| F |:: REncode x) ->
     Permutation L (F:: x).
 Proof with sauto.
   induction L;intros...
   simpl in H...
   simpl in H...
   apply UpREncode in H...
   - apply Permutation_cons...
     apply Permutation_map_inv in H2...
     apply MapREncodeEqual in H0...
   - apply IHL in H1.
     assert(Permutation (REncode x) (REncode (a :: x0))).
     rewrite H0...
     apply Permutation_map_inv in H...
     apply MapREncodeEqual in H2...
     rewrite H1.
     rewrite <- H3...
Qed. 
   
  Theorem OLInPermutationL: forall L F,
      In (d| F |) (LEncode L) ->
      exists L', Permutation L (F:: L').
    induction L;intros.
    inversion H.
    simpl in H.
    inversion H.
    inversion H0;subst.
    eexists;eauto.
    apply IHL in H0.
    CleanContext;sauto.
    exists L;auto.
    exists (a:: x).
    rewrite H0;perm.
  Qed.

Theorem OLInPermutationL': forall L x F,
     Permutation (LEncode L) (d| F |:: LEncode x) ->
     Permutation L (F:: x).
 Proof with sauto.
   induction L;intros...
   simpl in H...
   simpl in H...
   apply DwLEncode in H...
   - apply Permutation_cons...
     apply Permutation_map_inv in H2...
     apply MapLEncodeEqual in H0...
   - apply IHL in H1.
     assert(Permutation (LEncode x) (LEncode (a :: x0))).
     rewrite H0...
     apply Permutation_map_inv in H...
     apply MapLEncodeEqual in H2...
     rewrite H1.
     rewrite <- H3...
Qed. 
  
  
Lemma LEncodePositiveAtom F L : In (F) (LEncode L) -> IsPositiveAtom F.
Proof with sauto.
  induction L;intros... 
  inversion H. 
  inversion H...
Qed.

Lemma REncodePositiveAtom F L : In (F) (REncode L) -> IsPositiveAtom F.
Proof with sauto.
  induction L;intros... 
  inversion H. 
  inversion H...
Qed.
  
Lemma InIsPositive : forall F L L', In F (LEncode L ++ REncode L') -> IsPositiveAtom F.
  Proof with sauto.
  intros.
  apply in_app_or in H...
  apply LEncodePositiveAtom in H0;auto.
  apply REncodePositiveAtom in H0;auto.
  Qed.

Theorem checkEncodeCasesU L L' x F : 
      Permutation (LEncode L ++ REncode L') (u| F | :: x) ->
      exists x1, Permutation (REncode L') (u| F | :: REncode x1) /\ Permutation (LEncode L++ REncode x1 ) x.
  Proof with sauto.
  intros.
  checkPermutationCases H...
  apply NoUinL' in H0...
  assert(In (u| F |) (REncode L')).
  rewrite H0...
  apply in_map_iff in H...
  inversion H2...
  apply InPermutation in H3...
  assert(Permutation (REncode L') (REncode (F :: x1))).
  apply Permutation_map...
  assert(Permutation x0 (REncode x1)).
  rewrite H2 in H0. 
  simpl in H0...
  apply Permutation_cons_inv in H0...
   exists x1...
   rewrite <- H3...
 Qed. 
 
 Theorem checkEncodeCasesD L L' x F : 
      Permutation (LEncode L ++ REncode L') (d| F | :: x) ->
      exists x1, Permutation (LEncode L) (d| F | :: LEncode x1) /\ Permutation (LEncode x1++ REncode L' ) x.
  Proof with sauto.
  intros.
  checkPermutationCases H...
  2:{ apply NoDinR' in H0... }
  assert(In (d| F |) (LEncode L)).
  rewrite H0...
  apply in_map_iff in H...
  inversion H2...
  apply InPermutation in H3...
  assert(Permutation (LEncode L) (LEncode (F :: x1))).
  apply Permutation_map...
  assert(Permutation x0 (LEncode x1)).
  rewrite H2 in H0. 
  simpl in H0...
  apply Permutation_cons_inv in H0...
   exists x1...
   rewrite <- H3...
 Qed. 
 
 
  Lemma IsOLPositiveLREnc : forall L L',
      isOLFormulaL L -> isOLFormulaL L' -> 
      IsPositiveAtomFormulaL (LEncode L ++ REncode L').
    intros L L' HisL HisL'.
    apply isOLLEncode in HisL.
    apply isOLREncode in HisL'.
    apply Forall_app;auto.
  Qed.

 Lemma Remove_LEncode F D D' : Remove F D D' -> Remove (d| F|) (LEncode D) (LEncode D').
 Proof with sauto.
 intros.
 change (d| F |) with ((fun x : uexp => d| x |) F).
 apply Remove_Map...
 Qed.
 
 Lemma Remove_REncode F D D' : Remove F D D' -> Remove (u| F|) (REncode D) (REncode D').
 Proof with sauto.
 intros.
 change (u| F |) with ((fun x : uexp => u| x |) F).
 apply Remove_Map...
 Qed.
 
 
End OLEncodings.

Global Hint Unfold LEncode REncode CEncode : core.
