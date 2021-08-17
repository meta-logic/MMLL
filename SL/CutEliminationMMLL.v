(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export FLL.Misc.Hybrid.
Require Export FLL.SL.FLLTactics.
Require Import Lia.
Require Import FLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export FLL.SL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section CutElimination.
Context `{SI : Signature}.
  Context `{OLS: OLSig}.
  Hint Constructors isFormula  Remove seqN IsPositiveAtom : core .
  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).
 
      
  
Ltac simplSet := 
repeat
    match goal with
    | [H1: SetK ?i ?K, H2: SetU ?K |- _] =>
      rewrite cxtDestruct in H1; rewrite (SetU_then_empty H2) in H1
   | [H1: SetK4 ?i ?K, H2: SetU ?K |- _] =>
      rewrite cxtDestruct in H1; rewrite (SetU_then_empty H2) in H1      
    end;CleanContext.

  (** |-- B; []; (> [perp A]) *)

Lemma substContext n BD M1 M2 M X :  
        Permutation (getU BD) M1 ->
        Permutation (getL BD) M2 ->
        n |--- BD; M; X -> n |--- M1++M2; M; X.
 Proof.
  intros.
  rewrite cxtDestruct in H1.
  rewrite H in H1.
  rewrite H0 in H1.
  assumption.
 Qed. 

Lemma  substContext' BD M1 M2 M X :  
        Permutation (getU BD) M1 ->
        Permutation (getL BD) M2 ->
        |-- M1++M2; M; X -> |-- BD ; M; X.
 Proof.
  intros.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H0.
  assumption.
 Qed. 

  Lemma substContext1 n B M X C:  
        n |--- B++C; M; X -> n |--- (getU B ++ getL B) ++ C ; M; X.
 Proof.
  intros.
  rewrite <- cxtDestruct;auto.
 Qed.
 
 Lemma substContext1' B M X C:  
        |-- B++C; M; X -> |-- (getU B ++ getL B) ++ C ; M; X.
 Proof.
  intros.
  rewrite <- cxtDestruct;auto.
 Qed.
 
  Ltac substCon := 
  repeat rewrite app_assoc_reverse;
  
  match goal with
  | [  |- context[getU ?B ++ ?C ++ getL ?B] ] => LLPerm ((getU B ++ getL B) ++ C)   
  | [  |- context[getU ?B ++ ?C1 ++ getL ?B ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2)   
  | [  |- context[?C1 ++ getU ?B ++ ?C2 ++ getL ?B] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2)   
  | [  |- context[?C ++ getU ?B ++ getL ?B] ] => LLPerm ((getU B ++ getL B) ++ C)  
  | [  |- context[?C1 ++ getU ?B ++ getL ?B ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2) 
  | [  |- context[?C1 ++ getU ?B ++ ?C2 ++ getL ?B ++ ?C3] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2 ++ C3) 
  | [  |- context[?C1 ++ (getU ?B ++ getL ?B) ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2) 

  | [  |- context[getL ?B ++ ?C ++ getU ?B] ] => LLPerm ((getU B ++ getL B) ++ C)   
  | [  |- context[getL ?B ++ ?C1 ++ getU ?B ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2)   
  | [  |- context[?C1 ++ getL ?B ++ ?C2 ++ getU ?B] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2)   
  | [  |- context[?C ++ getL ?B ++ getU ?B] ] => LLPerm ((getU B ++ getL B) ++ C)  
  | [  |- context[?C1 ++ getL ?B ++ getU ?B ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2) 
  | [  |- context[?C1 ++ getL ?B ++ ?C2 ++ getU ?B ++ ?C3] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2 ++ C3) 
  | [  |- context[?C1 ++ (getL ?B ++ getU ?B) ++ ?C2] ] => LLPerm ((getU B ++ getL B) ++ C1 ++ C2) 

  end;try apply substContext1;try apply substContext1'.

           
 Ltac InSet := 
 intuition; try
  match goal with
  | [H: In ?F ?X |- In ?F ?Y] =>
      apply in_or_app;right;InSet
  end.
 

Lemma CutK4BaseInit n C P a : a <> loc -> SetK4 a C -> n >= length C + 1 -> 
        n - length C - 1 |--- PlusT C; []; (> [P]) ->
        S n |--- PlusT C; []; (>> (plust a) ! P).
Proof with sauto.
 intros. 
  createWorld.
  apply plust_loc_diff...
  eapply @GenK4Rel with (C4:=PlusT C) (CK:=[]) (CN:=[])...
  apply plust_loc_diff...
  apply SetK4PlusT...
  autounfold.
  rewrite map_length...
  CleanContext...
  autounfold.
  
  rewrite map_length...
Qed.
             

  Hypothesis TheoryIsFormula: forall P, theory P -> isFormula P.  

  Theorem CutElimBase a C dualC A dualA B D BD L L1 L2 L3 S1 S2 M N P: 
    dualC = dual C ->
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
        (L = L1++L2 -> 0 |--- B; M ++ [C]; (> L1) -> 0 |--- D; N; (> dualC::L2) -> |-- BD; M ++ N; (> L)) /\
      (0 |--- B; M; (> C :: L) -> 0 |--- D; N; (>> dualC) -> |-- BD; M ++ N; (> L)) /\
      (L = (S1++S2)++L3 -> 0 |--- B; M; (> S1++[C]++S2) -> 0 |--- D; N; (> dual C::L3) -> |-- BD; M ++ N; (> L)  ) /\
       (dualA = A ^ ->
       dualC = a ! dualA -> L = [P] ->
       0 |--- B ++ [(a,A)] ; M; (>> P) -> 0 |--- D; []; (>> a ! dualA) -> |-- BD; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       0 |--- B ++ [(a,A)] ; M; (> L) -> 0 |--- D; []; (>> a ! dualA) -> |-- BD; M; (> L)). 
  
  Proof with sauto;solveLL.
    intros CDual.
    split;[intros
          |split;[intros
          |split;[intros 
          |split;intros]]].
    * inversion H3...
      rewrite app_normalize_2...    
    * inversion H2...
      inversion H3.
    * inversion H3...
      apply ListConsApp' in H9... 
      inversion H4...
      do 2 rewrite app_normalize_2...   
    * inversion H6...
    * inversion H5...
  Qed.
  
   Definition CutW (w: nat) :=  
    forall a m i j C dualC A dualA P M N L L1 L2 L3 S1 S2 BD B D, 
    m <= w ->
    isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL N ->
    isFormulaL L ->
    isFormula C ->
    isFormula dualC ->
    dualC = C ^ ->
    complexity C = m ->
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->   
      (L = L1++L2 -> i |--- B; M ++ [C]; (> L1) -> j |--- D; N; (> dualC::L2) -> |-- BD; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- D; N; (>> dualC) -> |-- BD; M ++ N; (> L)) /\
      (L = (S1++S2)++L3 -> i |--- B; M; (> S1++[C]++S2) -> j |--- D; N; (> dual C::L3) -> |-- BD; M ++ N; (> L)  ) /\
       (dualA = A ^ ->
       dualC = a ! dualA -> L = [P] ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> L)). 
    
  Definition CutH (w h: nat) :=  
    forall a m i j C dualC A dualA P M N L L1 L2 L3 S1 S2 BD B D, 
    m <= h ->
    m = i + j ->
    isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL N ->
    isFormulaL L ->
    isFormula C ->
    isFormula dualC ->
    dualC = C ^ ->
    complexity C = S w ->
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->   
      (L = L1++L2 -> i |--- B; M ++ [C]; (> L1) -> j |--- D; N; (> dualC::L2) -> |-- BD; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- D; N; (>> dualC) -> |-- BD; M ++ N; (> L)) /\
      (L = (S1++S2)++L3 -> i |--- B; M; (> S1++[C]++S2) -> j |--- D; N; (> dual C::L3) -> |-- BD; M ++ N; (> L)  ) /\
       (dualA = A ^ ->
       dualC = a ! dualA -> L = [P] ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> L)). 
       

Theorem CutUPLStar  i j w h C L L1 L2 M N BD B D : CutH w h -> complexity C = S w -> S h = i + j ->
 isFormulaL (second BD) -> isFormulaL M  -> isFormulaL N -> isFormulaL L -> isFormula C -> isFormula (C^) -> L = L1 ++ L2 ->
 Permutation (getU BD) (getU B) ->
 Permutation (getU BD) (getU D) ->
 Permutation (getL BD) (getL B ++ getL D) ->
  i |--- B; M ++ [C]; (> L1) ->
  j |--- D; N; (> C ^ :: L2) ->
  |-- BD; M ++ N; (> L).
Proof with sauto;solveLL. 
 intros CH compC hH isFBD isFM isFN isFL isFC isFDC eqH HP1 HP2 HP3 Hi Hj.
 subst.
 assert(isFormulaL L1 /\ isFormulaL L2).
 split;SLSolve.
 assert(isFormulaL (second D)) by SLSolve.
 assert(isFormulaL (second B)) by SLSolve.

 CleanContext.
 clear isFL.
 rename H0 into isFD.
 rename H1 into isFB.
 rename H2 into isFL1.
 rename H3 into isFL2.
                 
 inversion Hi...
 * rewrite <- app_comm_cons...
 * rewrite <- app_comm_cons...
   assert(n |--- B; M ++ [C]; (> M0) ->
          j |--- D; N; (> (dual C)::L2) ->
            |-- BD; M ++ N; (> M0++L2)) as Cut.
           eapply CH...
           SLSolve.
           inversion isFL1...              
           apply Cut...
 * rewrite <- app_comm_cons...
   assert(n |--- B; M ++ [C]; (> F :: G :: M0) ->
          j |--- D; N; (> (dual C)::L2) ->
            |-- BD; M ++ N; (> F :: G :: M0++L2)) as Cut.
           eapply CH... 
           inversion isFL1...
           SLSolve.
           apply Cut...                                       
 * rewrite <- app_comm_cons...
   assert(n |--- B; M ++ [C]; (> F  :: M0) ->
          j |--- D; N; (> (dual C)::L2) ->
            |-- BD; M ++ N; (> F :: M0++L2)) as CutF.
           eapply CH...
           inversion isFL1...
           SLSolve.   
           apply CutF...             

   assert(n |--- B; M ++ [C]; (> G  :: M0) ->
          j |--- D; N; (> (dual C)::L2) ->
            |-- BD; M ++ N; (> G :: M0++L2)) as CutG.
           eapply CH...
           inversion isFL1...
           SLSolve.
                    
           apply CutG...          
 * rewrite <- app_comm_cons...
   destruct (uDec i0).
   - assert(n |--- B ++ [(i0, F)]; M ++ [C]; (> M0) ->
            j |--- D ++ [(i0, F)]; N; (> (dual C)::L2) ->
              |-- BD ++ [(i0, F)]; M ++ N; (> M0++L2)) as Cut.
           eapply CH...
           inversion isFL1...
           SLSolve.
           inversion H1...
           SLSolve.
           inversion isFL1...
           CleanContext.
           rewrite HP1...         
           CleanContext.
           rewrite HP2...         
           CleanContext.
           rewrite Permutation_cons_append.         
           apply Cut...
           LLExact H3.
           apply weakeningGenN_rev...          
   -  assert(n |--- B ++ [(i0, F)]; M ++ [C]; (> M0) ->
             j |--- D ; N; (> (dual C)::L2) ->
               |-- BD ++ [(i0, F)]; M ++ N; (> M0++L2)) as Cut.
           eapply CH...
           inversion isFL1...
           SLSolve.
           inversion H1...
           SLSolve.
           inversion isFL1...
           SLSolve. 
           CleanContext.
           SLSolve. 
           CleanContext.
           SLSolve. 
           CleanContext.
           rewrite HP3... 
           rewrite Permutation_cons_append.        
           apply Cut...
           LLExact H3.
 * rewrite <- app_comm_cons...
   assert(n |--- B; (M ++ [F]) ++ [C]; (> M0) ->
          j |--- D; N; (> (dual C)::L2) ->
            |-- BD; (M ++ [F]) ++ N; (> M0++L2)) as Cut.
           eapply CH...
           
           inversion isFL1...
           SLSolve.
           inversion isFL1...
           SLSolve.
           LLPerm((M ++ [F]) ++ N).
           apply Cut...
           LLExact H4.
 * apply Remove_Permute in H1...
   checkPermutationCases H1.
   2:{ inversion H1...
       rewrite H2.
       assert(j |--- D; N; (> (dual C)::L2) ->
              n |--- B; L'; (>> C) ->
                |-- BD; N++L'; (> L2)) as Cut.
       eapply CH with (m:=n + j) ...
        
       lia.
       SLSolve.
   
       rewrite <- ng_involutive...
       rewrite DualComplexity in compC...
       rewrite HP3...
       LLPerm(N ++ L')... }
       
   destruct(PositiveOrRelease F).
   2:{ inversion H5;CleanContext... 
       rewrite H1.
       rewrite <- app_comm_cons.
       LLPerm((x++N)++[F]). 
       eapply UpExtensionInv'... 
       eapply EquivUpArrow2 with (L:=[F] ++ L2)...
       SLSolve. rewrite H1 in isFM. inversion isFM...  
        assert(S n0 |--- B; x++ [C]; (> [F]) ->
               j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; x ++ N; (> [F]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
                rewrite H1 in isFM. inversion isFM... 
                SLSolve.
                rewrite H1 in isFM. inversion isFM... 
                apply Cut... 
                rewrite <- H2 in H9.
                LLExact H9. }
       inversion H5...
            { 
            rewrite (simplUnb _ D HP1 HP2 HP3 H8).
              inversion Hj...
              apply seqNtoSeq in H9... } 
            {  
              rewrite H4 in H2.
              checkPermutationCases H2.
              - 
              destruct(PositiveOrRelease F0).
              { (* first *) 
              assert(S n0 |--- B0; (F0::x0)++[C]; (> [])).
              decide1 F0...
              inversion H2...  
              rewrite <- H3...
              rewrite H1.
              rewrite <- app_comm_cons.
              rewrite Permutation_cons_append.
              apply TensorComm'.
              rewrite <- H10.
              LLPerm(G**F0::N0++(x0++N)).
              change L2 with ([]++L2).
              eapply @InvTensor with (B:=D0) (D:=getU D ++ getL D ++ getL B0)...
              CleanContext.
               CleanContext.
                rewrite HP3...              
              rewrite H8...
              
              apply Derivation1.
              apply seqNtoSeq in H13...
              assert(isFormulaL (second B)) by SLSolve.
              assert(isFormulaL (second B0)) by SLSolve.
   
              assert(S n0 |--- B0; (F0::x0) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; (F0::x0) ++ N; (> [ ]++L2)) as Cut.
                eapply CH...
                SLSolve;SLSolve.
                rewrite H1 in isFM.
                inversion isFM...
                SLSolve.             
                SLSolve.    
               CleanContext.
               apply UpExtension'.
               inversion H2...
               
               LLPerm((F0 :: x0) ++ N)... }
             { (* second *) 
              inversion H9;CleanContext...
              rewrite H1.
              rewrite <- app_comm_cons.
              rewrite Permutation_cons_append.
              apply TensorComm'.
              rewrite <- H10.
              LLPerm(G**F0::N0++(x0++N)).
              change L2 with ([]++L2).
              eapply @InvTensor with (B:=D0) (D:=getU D ++ getL D ++ getL B0)...
                CleanContext.
                CleanContext.
                rewrite HP3...
                rewrite H8...
                apply Derivation1.
                apply seqNtoSeq in H13...
                assert(isFormulaL (second B0)) by SLSolve.
                
                 assert(n |--- B0; x0 ++ [C]; (> [F0]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; x0 ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n + j)... 
                SLSolve;SLSolve.
                rewrite H1 in isFM.
                inversion isFM...
                rewrite <- H10 in H15.
                inversion H15...
                 SLSolve.
                  SLSolve.  
                rewrite H1 in isFM.
                inversion isFM...
                inversion H14...
               CleanContext.
                eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
                srewrite H1 in isFM.
                inversion isFM...
                SLSolve. inversion H14...
                
                apply Cut...
                rewrite <- H3... } 
             - 
              destruct(PositiveOrRelease G).
              { (* first *) 
              assert(S n0 |--- D0; (G::x0)++[C]; (> [])).
              decide1 G...
              inversion H2...  
              rewrite <- H3...
              rewrite H1.
              rewrite <- H10.
              LLPerm(F0**G::M0++(x0++N)).
              change L2 with ([]++L2).
              eapply @InvTensor with (B:=B0) (D:=getU D ++ getL D ++ getL D0)...
              CleanContext...
              CleanContext...
              rewrite HP3...              
              rewrite H8...
              
              apply Derivation1.
              apply seqNtoSeq in H9...
              assert(S n0 |--- D0; (G::x0) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; (G::x0) ++ N; (> [ ]++L2)) as Cut.
                eapply CH... 
                 assert(isFormulaL (second D0)) by SLSolve.
               rewrite app_assoc.
                SLSolve;SLSolve.
                rewrite H1 in isFM.
                inversion isFM...
                SLSolve.                 
                rewrite <- H10 in H16.
                inversion H16...
                 SLSolve.  
               CleanContext.
               apply UpExtension'.
               inversion H2...
               
               
               LLPerm((G :: x0) ++ N)... }
             { (* second *) 
              inversion H13;CleanContext...
              rewrite H1.
              rewrite <- H10.
              LLPerm(F0**G::M0++(x0++N)).
              change L2 with ([]++L2).
              eapply @InvTensor with (B:=B0) (D:=getU D ++ getL D ++ getL D0)...
                CleanContext.
                CleanContext.
                CleanContext.
                rewrite HP3...
                rewrite H8...
                apply Derivation1.
                apply seqNtoSeq in H9...
              assert(n |--- D0; x0++ [C]; (> [G ]) ->
                          j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; x0 ++ N; (> [G]++L2)) as Cut.
                 eapply CH with (m:=n + j)... 
                 assert(isFormulaL (second D0)) by SLSolve.
                 rewrite app_assoc.
                SLSolve;SLSolve.
                rewrite H1 in isFM.
                inversion isFM...
                rewrite <- H10 in H14.
                inversion H14...
                 SLSolve.
                  SLSolve.  
                rewrite H1 in isFM.
                inversion isFM...
                inversion H11...
               CleanContext.
                eapply EquivUpArrow2 with (L:=[G] ++ L2)...
                 rewrite H1 in isFM.
                inversion isFM...
                 SLSolve.  inversion H11... 
                apply Cut...
                rewrite <- H3... }   
                }
    -   destruct(PositiveOrRelease F0).   
       {  assert ( (S n0) |--- B;(x ++ [F0]) ++ [C]; (> [])).
                LLPerm (F0::(x++[C])).
                 decide1 F0. inversion H3...                
                 rewrite H2...                
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus.
                assert((S n0) |--- B; (x ++ [F0]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; (x ++ [F0]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=(S n0) + j)...
                 rewrite H1 in isFM.
                inversion isFM...
                 SLSolve. inversion H9...  
                apply UpExtension'.
                inversion H3...
                 LLPerm ( (x ++ [F0]) ++ N)... }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus.
                assert(n |--- B; x ++ [C]; (> [F0]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; x ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:= n + j)...
                   rewrite H1 in isFM.
                inversion isFM...
                   rewrite H1 in isFM.
                inversion isFM...
                 SLSolve.  
               eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
                rewrite H1 in isFM.
                inversion isFM...
                 SLSolve. inversion H4...  
               apply Cut... 
               rewrite H2...
               } 
  -    destruct(PositiveOrRelease G).   
       {  assert ( (S n0) |--- B;(x ++ [G]) ++ [C]; (> [])).
                LLPerm (G::(x++[C])).
                 decide1 G. inversion H3...                
                 rewrite H2...                
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm.
                assert((S n0) |--- B; (x ++ [G]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; (x ++ [G]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=(S n0) + j)...
                   rewrite H1 in isFM.
                inversion isFM...
                SLSolve. inversion H9...
                
                apply UpExtension'.
                inversion H3...
                 LLPerm ( (x ++ [G]) ++ N)... }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm.
                assert(n |--- B; x ++ [C]; (> [G]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; x ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:= n + j)...
                       rewrite H1 in isFM.
                inversion isFM...
                     rewrite H1 in isFM.
                inversion isFM...
                SLSolve.
              
               eapply EquivUpArrow2 with (L:=[G] ++ L2)...
                    rewrite H1 in isFM.
                inversion isFM...
                SLSolve. inversion H4...
              
               apply Cut... 
               rewrite H2...
               }
   -  apply PositiveNotRelease in H. contradiction. 
   -   destruct(PositiveOrRelease (FX t)).   
            {    assert ( (S n0) |--- B;(x ++ [FX t]) ++ [C]; (> [])).
                LLPerm ((FX t)::(x++[C])).
                 decide1 (FX t). inversion H3...                
                 rewrite H2...
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert((S n0) |--- B; (x ++ [FX t]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; (x ++ [FX t]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=(S n0) + j)...
                    rewrite H1 in isFM.
                inversion isFM...
                SLSolve.
                inversion H11...
                 
                apply UpExtension'.
                inversion H3...
                LLPerm ( (x ++ [FX t]) ++ N)... }
             { 
                inversion H10;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert(n |--- B; x ++ [C]; (> [FX t]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- BD; x ++ N; (> [FX t]++L2)) as Cut.
                eapply CH with (m:= n + j)...  
                     rewrite H1 in isFM.
                inversion isFM...
                     rewrite H1 in isFM.
                inversion isFM...
                SLSolve. 
              
                eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...
                     rewrite H1 in isFM.
                inversion isFM...
                SLSolve. inversion H9...
               apply Cut... 
               rewrite H2... }
*  destruct(PositiveOrRelease F).
   2:{ inversion H7;CleanContext...
       apply @AbsorptionClassic' with (i:=i0) (F:=F)...
       rewrite cxtDestruct.
       rewrite HP1.
       apply in_or_app. left.
       apply uIngetU...
       eapply EquivUpArrow2 with (L:=[F] ++ L2)...
       SLSolve. 
       SLSolve.         
       assert(n0 |--- B; M ++ [C]; (> [F]) ->
                j |--- D; N; (> (dual C)::L2) ->
                  |-- BD; M ++ N; (> [F]++L2)) as Cut.
       eapply CH with (m:=n0 + j)... 
           
                SLSolve.
              
       apply Cut... } 
       inversion H7...
       -  apply @AbsorptionClassic' with (i:=i0) (F:=perp A)...
          rewrite cxtDestruct.
          rewrite HP1.
          apply in_or_app. left.
          apply uIngetU...
          rewrite cxtDestruct.
          rewrite HP2. rewrite HP3.
          rewrite (SetU_then_empty H9)...
          rewrite <- cxtDestruct.
          apply UpExtension'...
          inversion Hj...
          apply seqNtoSeq in H12...
          LLExact H12.  
       -  checkPermutationCases H5.
          {  destruct(PositiveOrRelease F0).
             { (* first *) 
               rewrite <- H11.
               assert (S n0 |--- B0; (F0 :: x) ++ [C]; (> [])).
               LLPerm (F0 :: x ++ [C]).
               decide1 F0. inversion H4...
               rewrite <- H5...
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r L2).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=getU D ++ getL D ++ getL B0) (D:=D0)...
               rewrite cxtDestruct.
               rewrite HP1.
               apply in_or_app. left.
               apply uIngetU...
               CleanContext...
               CleanContext...
                rewrite HP3...
               rewrite H9...
               apply UpExtension'.
                inversion H4...
                
                 assert(S n0 |--- B0; (F0::x) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; (F0::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH... 
                 assert(isFormulaL (second B0)) by SLSolve.
                 SLSolve;SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve.
                 SLSolve.  
               CleanContext...
               LLPerm((F0 :: x) ++ N)...
               apply Derivation1.
               apply seqNtoSeq in H14... }
            { (* first *) 
               rewrite <- H11.
               inversion H10;CleanContext...
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r L2).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=getU D ++ getL D ++ getL B0) (D:=D0)...
               rewrite cxtDestruct.
               rewrite HP1.
               apply in_or_app. left.
               apply uIngetU...
               CleanContext...
               CleanContext...
                rewrite HP3...
               rewrite H9...
                 assert(n |--- B0; x ++ [C]; (> [F0]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; x ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n+j)... 
              assert(isFormulaL (second B0)) by SLSolve.
               SLSolve;SLSolve. 
               SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve.  
               SLSolve.
               CleanContext...
               CleanContext...
               eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               SLSolve;SLSolve.
               
               apply Cut... 
               rewrite <- H5...
               apply Derivation1.
               apply seqNtoSeq in H14... } }
          {  destruct(PositiveOrRelease G).
             { (* first *) 
               rewrite <- H11.
               assert (S n0 |--- D0; (G :: x) ++ [C]; (> [])).
               LLPerm (G :: x ++ [C]).
               decide1 G. inversion H4...
               rewrite <- H5...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_l L2).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (D:=getU D ++ getL D ++ getL D0) (B:=B0)...
               rewrite cxtDestruct.
               rewrite HP1.
               apply in_or_app. left.
               apply uIngetU...
               CleanContext...
               CleanContext...
               rewrite HP3...
               rewrite H9...
               apply Derivation1.
               apply seqNtoSeq in H10... 
               apply UpExtension'.
                inversion H4...
                
                 assert(S n0 |--- D0; (G::x) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; (G::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH... 
                
                 assert(isFormulaL (second D0)) by SLSolve.
                 SLSolve;SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve. SLSolve.  
               CleanContext...
               LLPerm((G :: x) ++ N)...  }
            { (* first *) 
               rewrite <- H11.
               inversion H14;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_l L2).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (D:=getU D ++ getL D ++ getL D0) (B:=B0)...
               rewrite cxtDestruct.
               rewrite HP1.
               apply in_or_app. left.
               apply uIngetU...
               CleanContext...
               CleanContext...
                rewrite HP3...
               rewrite H9...
               apply Derivation1.
               apply seqNtoSeq in H10...                
               
                 assert(n |--- D0; x ++ [C]; (> [G]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; x ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n+j)... 
                 assert(isFormulaL (second D0)) by SLSolve.
                 SLSolve;SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve.  
               SLSolve.
               CleanContext...
               eapply EquivUpArrow2 with (L:=[G] ++ L2)... 
               SLSolve. SLSolve.
               apply Cut... 
               rewrite <- H5... } }                
  -  destruct(PositiveOrRelease F0).   
     {  assert ( (S n0) |--- B;(M ++ [F0]) ++ [C]; (> [])).
        LLPerm (F0::(M++[C])).
        decide1 F0. inversion H4...                
        eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (M ++ [F0]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[F0]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)... 
                SLSolve.
                SLSolve.
                
               LLPerm( (M ++ [F0]) ++ N)... }
     {  inversion H9;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        assert( n |--- B; M ++ [C]; (> [F0]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n + j)...
        SLSolve. SLSolve.
        eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
        SLSolve. SLSolve. } 
  -  destruct(PositiveOrRelease G).   
     {  assert ( (S n0) |--- B;(M ++ [G]) ++ [C]; (> [])).
        LLPerm (G::(M++[C])).
        decide1 G. inversion H4...                
        eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (M ++ [G]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[G]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)... 
        SLSolve. SLSolve.
               LLPerm( (M ++ [G]) ++ N)... }
     {  inversion H9;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        assert( n |--- B; M ++ [C]; (> [G]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n + j)...
      SLSolve. SLSolve.
        eapply EquivUpArrow2 with (L:=[G] ++ L2)...
        SLSolve. SLSolve.  } 
  -  apply PositiveNotRelease in H. contradiction. 
  -  destruct(PositiveOrRelease (FX t)).   
     {  assert ( (S n0) |--- B;(M ++ [FX t]) ++ [C]; (> [])).
        LLPerm ((FX t)::(M++[C])).
        decide1 (FX t). inversion H4...                
        eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (M ++ [FX t]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[FX t]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
        SLSolve.         SLSolve.
               LLPerm( (M ++ [FX t]) ++ N)... }
     {  inversion H11;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        rewrite cxtDestruct.
        rewrite HP1.
        apply in_or_app. left.
        apply uIngetU...
        assert( n |--- B; M ++ [C]; (> [FX t]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [FX t]++L2)) as Cut.
                eapply CH with (m:=n + j)...
                SLSolve. 
        eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...
        SLSolve. SLSolve. }
 *  destruct(PositiveOrRelease F).
    2:{ inversion H7;CleanContext...
        apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
        rewrite cxtDestruct.
        rewrite HP1. 
        rewrite HP3.
        LLPerm((i0, F):: (getU B' ++ getL B') ++ getL D).
        rewrite <- cxtDestruct.
        eapply @AbsorptionLinear with (i:=i0) (F:=F) (B':=B'++getL D)...
        eapply EquivUpArrow2 with (L:=[F] ++ L2)...
        SLSolve.
        SLSolve.
        assert(n0 |--- B'; M ++ [C]; (> [F]) ->
                j |--- getU B' ++ getL D; N; (> (dual C)::L2) ->
                  |-- B' ++ getL D; M ++ N; (> [F]++L2)) as Cut.
                eapply CH with (m:=n0 + j)...
       SLSolve.
        srewrite H3 in isFB.
        simpl in isFB.
        SLSolve.
        SLSolve.
        SLSolve.
                apply Cut...
                rewrite <- HP1.
                rewrite HP2.
                rewrite <- cxtDestruct... } 
        inversion H7...
     - 
       apply Remove_Permute in H3...
       rewrite H3 in *.
       CleanContext.
       rewrite cxtDestruct.
       rewrite HP1. 
       rewrite HP3.
       LLPerm((i0, perp A):: (getU B' ++ getL D)).
       eapply @AbsorptionLinear with (i:=i0) (F:=perp A) (B':=getU B'++getL D)...
       rewrite <- HP1.
       rewrite HP2.
         rewrite <- cxtDestruct...
       apply UpExtension'...      
       inversion Hj... 
       apply seqNtoSeq in H11...
        LLExact H11. 
    - 
       checkPermutationCases H5.
       { destruct(PositiveOrRelease F0).
         { apply Remove_Permute in H3...
           rewrite H3 in *.
           CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           rewrite <- H11.
           LLPerm((i0, F0 ** G):: (getU B' ++ getL B') ++ getL D).
           LLPerm ((x++N)++N0).
           rewrite <- (app_nil_r L2).
           
           eapply @InvTensorL1 with (i:=i0) (F:=F0) (G:=G) (D:=D0)
            (B:=(i0, F0 ** G):: (getU B' ++ getL B0++getL D)) (B':=(getU B' ++ getL B0++getL D));auto. 
           CleanContext...
           CleanContext...
           CleanContext...
           rewrite H9... 
           apply UpExtension'... inversion H4... 
           assert(S n0 |--- B0; (F0 :: x) ++ [C]; (> [])).
           decide1 F0. inversion H4...
           rewrite <- H5...
           assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
               assert(isFormulaL (second B0)) by SLSolve.
               
           assert(S n0 |--- B0; (F0::x) ++ [C]; (> [ ]) ->
                     j |--- D; N; (> (dual C)::L2) ->
                       |-- getU B0 ++ getL B0 ++ getL D; (F0::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH...
               
                SLSolve;SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve.  
                SLSolve.
               CleanContext...
               rewrite <- H6...
               rewrite <- HP2...
               CleanContext...
               
               LLPerm((F0 :: x) ++ N)...
               rewrite H6...
          apply Derivation1.
          apply seqNtoSeq in H14... }
       {   inversion H10;CleanContext...
           apply Remove_Permute in H3...
           rewrite H3 in *.
           CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           rewrite <- H11.
           LLPerm((i0, F0 ** G):: (getU B' ++ getL B') ++ getL D).
           LLPerm ((x++N)++N0).
           rewrite <- (app_nil_r L2).
           
           eapply @InvTensorL1 with (i:=i0) (F:=F0) (G:=G) (D:=D0)
            (B:=(i0, F0 ** G):: (getU B' ++ getL B0++getL D)) (B':=(getU B' ++ getL B0++getL D));auto. 
           CleanContext...
           CleanContext...
           CleanContext...
           rewrite H9... 
          assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
               assert(isFormulaL (second B0)) by SLSolve.
           
           assert( n |--- B0; x ++ [C]; (> [F0]) ->
                   j |--- D; N; (> (dual C)::L2) ->
                     |-- getU B0 ++ getL B0 ++ getL D; x ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n+j)...
                SLSolve;SLSolve.
                SLSolve.
                rewrite <- H11 in isFM.
                SLSolve.  
                SLSolve.
               CleanContext...
               rewrite <- H6...
               rewrite <- HP2...
               rewrite H6...
             eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
             SLSolve. SLSolve.
           apply Cut...
           rewrite <- H5...     
           apply Derivation1.
           apply seqNtoSeq in H14... } }
    { destruct(PositiveOrRelease G).
         { apply Remove_Permute in H3...
           rewrite H3 in *.
           CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           rewrite <- H11.
           LLPerm((i0, F0 ** G):: (getU B' ++ getL B') ++ getL D).
           LLPerm (M0++(x++N)).
           rewrite <- (app_nil_l L2).
           
           eapply @InvTensorL2 with (i:=i0) (F:=F0) (G:=G) (B:=B0)
            (D:=(i0, F0 ** G):: (getU B' ++ getL D0++getL D)) (D':=(getU B' ++ getL D0++getL D));auto. 
           CleanContext...
           CleanContext...
           CleanContext...
           rewrite H9... 
           apply Derivation1.
          apply seqNtoSeq in H10...
           apply UpExtension'... inversion H4... 
           assert(S n0 |--- D0; (G :: x) ++ [C]; (> [])).
           decide1 G. inversion H4...
           rewrite <- H5...
           assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
               assert(isFormulaL (second D0)) by SLSolve.
           
           assert(S n0 |--- D0; (G::x) ++ [C]; (> [ ]) ->
                     j |--- D; N; (> (dual C)::L2) ->
                       |-- getU D0 ++ getL D0 ++ getL D; (G::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH... 
                SLSolve;SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve. SLSolve.  
                
               CleanContext...
               rewrite <- H8...
               rewrite <- HP2...
               CleanContext...  
               rewrite H8... 
               
               LLPerm((G :: x) ++ N)...  }
       {   inversion H14;CleanContext...
           apply Remove_Permute in H3...
           rewrite H3 in *.
           CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           rewrite <- H11.
           LLPerm((i0, F0 ** G):: (getU B' ++ getL B') ++ getL D).
           LLPerm (M0++(x++N)).
           rewrite <- (app_nil_l L2).
           
           eapply @InvTensorL2 with (i:=i0) (F:=F0) (G:=G) (B:=B0)
            (D:=(i0, F0 ** G):: (getU B' ++ getL D0++getL D)) (D':=(getU B' ++ getL D0++getL D));auto. 
           CleanContext...
           CleanContext...
           CleanContext...
           rewrite H9... 
           apply Derivation1.
           apply seqNtoSeq in H10...
           assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
               assert(isFormulaL (second D0)) by SLSolve.
           
           assert( n |--- D0; x ++ [C]; (> [G]) ->
                   j |--- D; N; (> (dual C)::L2) ->
                     |-- getU D0 ++ getL D0 ++ getL D; x ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n+j)... 
                
                 SLSolve;SLSolve.
                SLSolve.
                rewrite <- H11 in isFM.
                 SLSolve.  
                SLSolve.
               CleanContext...
               rewrite <- H8...
               rewrite <- HP2...
               CleanContext...
               rewrite H8...
            eapply EquivUpArrow2 with (L:=[G] ++ L2)...
            SLSolve. SLSolve.
           apply Cut...
           rewrite <- H5...   } }          
  -  destruct(PositiveOrRelease F0).   
     {  apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, F0 op G):: (getU B' ++ getL B') ++ getL D).
           eapply @InvPlusL;eauto. 
           apply UpExtension'... inversion H4... 
           assert ( (S n0) |--- B';(M ++ [F0]) ++ [C]; (> [])).
           LLPerm (F0::(M++[C])).
                 decide1 F0. inversion H4...                
            assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
            
             assert(S n0 |--- B'; (M ++ [F0]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- (getU B' ++ getL B') ++ getL D; (M++[F0]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
               
                SLSolve;SLSolve.
                 SLSolve. SLSolve.  
                
               CleanContext...
               LLPerm( (M ++ [F0]) ++ N)... }
             { inversion H9;CleanContext...
              apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, F0 op G):: (getU B' ++ getL B') ++ getL D).
           eapply @InvPlusL;eauto. 
           assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
             assert( n |--- B'; M ++ [C]; (> [F0]) ->
                     j |--- D; N; (> (dual C)::L2) ->
                       |-- (getU B' ++ getL B') ++ getL D; M ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n + j)...
                SLSolve;SLSolve.
                SLSolve.
                 SLSolve.  
               CleanContext.
               CleanContext.
               eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
               SLSolve. SLSolve.  } 
  -  destruct(PositiveOrRelease G).   
     {  apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, F0 op G):: (getU B' ++ getL B') ++ getL D).
           eapply @InvPlusLComm;eauto. 
           apply UpExtension'... inversion H4... 
           assert ( (S n0) |--- B';(M ++ [G]) ++ [C]; (> [])).
           LLPerm (G::(M++[C])).
                 decide1 G. inversion H4...                
           assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
             assert(S n0 |--- B'; (M ++ [G]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- (getU B' ++ getL B') ++ getL D; (M++[G]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...

                SLSolve;SLSolve.
                SLSolve. 
                 SLSolve.                 CleanContext.
               CleanContext.
               LLPerm( (M ++ [G]) ++ N)... }
             { inversion H9;CleanContext...
              apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, F0 op G):: (getU B' ++ getL B') ++ getL D).
           eapply @InvPlusLComm;eauto. 
assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
           
             assert( n |--- B'; M ++ [C]; (> [G]) ->
                     j |--- D; N; (> (dual C)::L2) ->
                       |-- (getU B' ++ getL B') ++ getL D; M ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n + j)...
                SLSolve;SLSolve.
                SLSolve.
               CleanContext.
               CleanContext.
               eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               SLSolve. SLSolve.  }          
 -  apply PositiveNotRelease in H. contradiction. 
 - destruct(PositiveOrRelease (FX t)).   
     {  apply Remove_Permute in H3...
        rewrite H3 in *.
        CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, E{ FX}):: (getU B' ++ getL B') ++ getL D).
           eapply @InvExL;eauto. 
           apply UpExtension'... inversion H4... 
           assert ( (S n0) |--- B';(M ++ [FX t]) ++ [C]; (> [])).
           LLPerm ((FX t)::(M++[C])).
                 decide1 (FX t). inversion H4... 
                 assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
                          
             assert(S n0 |--- B'; (M ++ [FX t]) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- (getU B' ++ getL B') ++ getL D; (M++[FX t]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
                SLSolve;SLSolve.
                SLSolve. SLSolve.
               CleanContext.
               CleanContext.
               LLPerm( (M ++ [FX t]) ++ N)... }
             { inversion H11;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
              apply Remove_Permute in H3...
              rewrite H3 in *.
            CleanContext.
           rewrite cxtDestruct.
           rewrite HP1. 
           rewrite HP3.
           LLPerm((i0, E{ FX}):: (getU B' ++ getL B') ++ getL D).
           eapply @InvExL;eauto. 
          
          assert(isFormulaL (second B')). 
               srewrite H3 in isFB.
               SLSolve.    
              assert( n |--- B'; M ++ [C]; (> [FX t]) ->
                     j |--- D; N; (> (dual C)::L2) ->
                       |-- (getU B' ++ getL B') ++ getL D; M ++ N; (> [FX t]++L2)) as Cut.
                eapply CH with (m:=n + j)...
                SLSolve;SLSolve.
                SLSolve. 
               CleanContext.
               CleanContext.
               eapply EquivUpArrow2 with (L:=[FX t] ++ L2)... SLSolve. SLSolve.  } 
 *  destruct(PositiveOrRelease F).
    2:{ inversion H5;CleanContext...
        destruct (NegativeAtomDec F).
        assert(False). 
        inversion H;subst... 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
        eapply EquivUpArrow2 with (L:=[F] ++ L2)...
        SLSolve.
          assert(n0 |--- B; M ++ [C]; (> [F]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; M ++ N; (> [F]++L2)) as Cut.
                         
                eapply CH with (m:=n0 + j)...
                apply Cut... }
                 
    inversion H5...
    -   eapply @AbsorptionPerp' with (A:=A)...
        rewrite cxtDestruct.
        rewrite HP2.
        rewrite HP3.
              rewrite (SetU_then_empty H7)...
        rewrite <- cxtDestruct.
        apply UpExtension'...
        inversion Hj...
        apply seqNtoSeq in H10...
        LLExact H10.  
    - checkPermutationCases H3.
      {  destruct(PositiveOrRelease F0).
         { (* first *) 
           rewrite <- H9.
           assert (S n0 |--- B0; (F0 :: x) ++ [C]; (> [])).
           LLPerm (F0 :: x ++ [C]).
           decide1 F0. inversion H2...
           rewrite <- H3...
           LLPerm((x ++ N) ++ N0).
           rewrite <- (app_nil_r L2).
           eapply @InvTensorT with (F:=F0) (G:=G) (B:=getU D ++ getL D ++ getL B0) (D:=D0)...
           CleanContext...
           rewrite HP3...
           rewrite H7...
           CleanContext...
           apply UpExtension'.
           inversion H2...
           assert(isFormulaL (second B0)) by SLSolve. 
                 assert(S n0 |--- B0; (F0::x) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; (F0::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH...
                SLSolve;SLSolve.
                 rewrite <- H9 in isFM.
                 SLSolve.
                  SLSolve.
               CleanContext...
               LLPerm((F0 :: x) ++ N)...
               apply Derivation1.
               apply seqNtoSeq in H12... }
            { (* first *) 
               rewrite <- H9.
               inversion H8;CleanContext...
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r L2).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=getU D ++ getL D ++ getL B0) (D:=D0)...
               CleanContext...
               CleanContext...
               rewrite HP3...
               rewrite H7...
               assert(isFormulaL (second B0)) by SLSolve. 
           
                 assert(n |--- B0; x ++ [C]; (> [F0]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL B0; x ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n+j)...
                 rewrite <- H9 in isFM.
               SLSolve;SLSolve.
                 rewrite <- H9 in isFM.
                 SLSolve.
                  SLSolve.
               CleanContext...
               eapply EquivUpArrow2 with (L:=[F0] ++ L2)... 
               SLSolve. SLSolve.
               apply Cut... 
               rewrite <- H3...
               apply Derivation1.
               apply seqNtoSeq in H12... } }
          {  destruct(PositiveOrRelease G).
             { (* first *) 
               rewrite <- H9.
               assert (S n0 |--- D0; (G :: x) ++ [C]; (> [])).
               LLPerm (G :: x ++ [C]).
               decide1 G. inversion H2...
               rewrite <- H3...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_l L2).
               eapply @InvTensorT with (F:=F0) (G:=G) (D:=getU D ++ getL D ++ getL D0) (B:=B0)...
               CleanContext...
               CleanContext...
               rewrite HP3...
               rewrite H7...
               apply Derivation1.
               apply seqNtoSeq in H8... 
               apply UpExtension'.
                inversion H2...
                assert(isFormulaL (second D0)) by SLSolve.
                 assert(S n0 |--- D0; (G::x) ++ [C]; (> [ ]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; (G::x) ++ N; (> [ ]++L2)) as Cut.
                eapply CH...
                  rewrite <- H9 in isFM.
               SLSolve;SLSolve.
                 rewrite <- H9 in isFM.
                 SLSolve.
                  SLSolve.
               CleanContext...
              
               LLPerm((G :: x) ++ N)...  }
            { (* first *) 
               rewrite <- H9.
               inversion H12;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_l L2).
               eapply @InvTensorT with (F:=F0) (G:=G) (D:=getU D ++ getL D ++ getL D0) (B:=B0)...
               CleanContext...
               CleanContext...
                rewrite HP3...
               rewrite H7...
               apply Derivation1.
               apply seqNtoSeq in H8...                
               assert(isFormulaL (second D0)) by SLSolve.
                 assert(n |--- D0; x ++ [C]; (> [G]) ->
                       j |--- D; N; (> (dual C)::L2) ->
                         |-- getU D ++ getL D ++ getL D0; x ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n+j)...
                
                  rewrite <- H9 in isFM.
               SLSolve;SLSolve.
                 rewrite <- H9 in isFM.
                 SLSolve.
                  SLSolve.
               CleanContext...
               eapply EquivUpArrow2 with (L:=[G] ++ L2)...
               SLSolve. SLSolve. 
               apply Cut... 
               rewrite <- H3... } }                
  -  destruct(PositiveOrRelease F0).   
     {  assert ( (S n0) |--- B;(M ++ [F0]) ++ [C]; (> [])).
        LLPerm (F0::(M++[C])).
        decide1 F0. inversion H2...                
        eapply @InvPlusT with (F:=F0) (G:=G)...
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (M ++ [F0]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[F0]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
                 SLSolve. SLSolve.
               LLPerm( (M ++ [F0]) ++ N)... }
     {  inversion H7;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (> [F0]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [F0]++L2)) as Cut.
                eapply CH with (m:=n + j)...
      SLSolve.  SLSolve.        
        eapply EquivUpArrow2 with (L:=[F0] ++ L2)...
        SLSolve. SLSolve. }
   -  destruct(PositiveOrRelease G).   
     {  assert ( (S n0) |--- B;(M ++ [G]) ++ [C]; (> [])).
        LLPerm (G::(M++[C])).
        decide1 G. inversion H2...                
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (M ++ [G]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[G]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
               SLSolve. SLSolve.                 
               LLPerm( (M ++ [G]) ++ N)... }
     {  inversion H7;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (> [G]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [G]++L2)) as Cut.
                eapply CH with (m:=n + j)...
                SLSolve.
        eapply EquivUpArrow2 with (L:=[G] ++ L2)...
        SLSolve. SLSolve. }
        
  - apply PositiveNotRelease in H. contradiction.  
  -  destruct(PositiveOrRelease (FX t)).   
     {  assert ( (S n0) |--- B;(M ++ [FX t]) ++ [C]; (> [])).
        LLPerm ((FX t)::(M++[C])).
        decide1 (FX t). inversion H2...                
        eapply @InvExT;eauto...
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (M ++ [FX t]) ++ [C]; (> [ ]) ->
                  j |--- D; N; (> (dual C)::L2) ->
                    |-- BD; (M++[FX t]) ++ N; (> [ ]++L2)) as Cut.
                eapply CH with (m:=S n0 + j)...
               SLSolve. SLSolve.  
               LLPerm( (M ++ [FX t]) ++ N)... }
     {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.               
        eapply @InvExT;eauto... 
        assert( n |--- B; M ++ [C]; (> [FX t]) ->
                j |--- D; N; (> (dual C)::L2) ->
                 |-- BD; M ++ N; (> [FX t]++L2)) as Cut.
                eapply CH with (m:=n + j)...
         SLSolve.
        eapply EquivUpArrow2 with (L:=[FX t] ++ L2)...
        SLSolve. SLSolve. }
  * rewrite <- app_comm_cons... 
     assert(n |--- B; M ++ [C]; (> FX x :: M0) ->
           j |--- D; N; (> (dual C)::L2) ->
             |-- BD; M ++ N; (> FX x :: M0++L2)) as Cut.
           eapply CH...
           SLSolve. inversion H2... SLSolve.   
           apply H4 in properX...
  Qed.         
   
  Theorem CutUPStar  i j w h C L S1 S2 L3 M N BD B D : CutH w h -> complexity C = S w -> S h = i + j ->
 isFormulaL (second BD) -> isFormulaL L -> isFormulaL M -> isFormulaL N -> isFormula C -> isFormula (C^) -> L = (S1++S2)++L3 ->
 Permutation (getU BD) (getU B) ->
 Permutation (getU BD) (getU D) ->
 Permutation (getL BD) (getL B ++ getL D) ->
  i |--- B; M; (> S1++[C]++S2) ->
  j |--- D; N; (> dual C::L3) ->
  |-- BD; M ++ N; (> L).
Proof with sauto;solveLL;try SLSolve.   
 intros CH compC hH isFBD isFL isFM isFN isFC isFDC eqL HP1 HP2 HP3 Hi Hj.
 subst.
 assert(isFormulaL (S1++S2) /\ isFormulaL L3).
 split;SLSolve.
 CleanContext.
 assert(isFormulaL S1 /\ isFormulaL S2).
 split;SLSolve.
 assert(isFormulaL (second D))...
 assert(isFormulaL (second B))...
 clear isFL H0.
 rename H2 into isFD.
 rename H into isFB.
 rename H3 into isFS1.
 rename H4 into isFS2.
 rename H1 into isFL3.
 destruct S1.
 * CleanContext.
   destruct (PositiveOrRelease C).
   - simpl in Hi.
     
     assert(exists n, n < i /\ n |--- B; C::M; (> S2)).
     inversion Hi;subst;inversion H;
     exists n...
     CleanContext.
      assert(x |--- B; M ++ [C]; (> S2) ->
            j |--- D; N; (> (dual C)::L3) ->
             |-- BD; M ++ N; (> S2++L3)) as Cut.
           eapply CH with (m:=x + j)...
           
     apply Cut...
     LLExact H2. 
   - assert(exists n, n < j /\ n |--- D; N++[dual C]; (> L3)).
     apply ReleaseDualPositive in H.
     inversion Hj; match goal with
       [ H: _= dual ?C , H2: positiveFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;try solve [inversion H];exists n...
     CleanContext. LLExact H6. CleanContext.
      assert(x |--- D; N ++ [dual C]; (> L3) ->
            i |--- B; M; (> C::S2) ->
             |-- BD; N++M; (> L3++S2)) as Cut.
           eapply CH with (m:=x + i)...
           
           rewrite <- ng_involutive...
           rewrite DualComplexity.
           rewrite <- ng_involutive...
           rewrite HP3...
           LLPerm(N++M).
           eapply @EquivUpArrow2 with (L:=L3 ++ S2)...
 * repeat rewrite <- app_comm_cons in Hi.          
   CleanContext. 
   repeat rewrite <- app_comm_cons.
   inversion Hi...
   - assert(n |--- B; M; (> S1 ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; M ++ N; (> (S1 ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j) (C:=C) (dualC:=C ^)...
           SLSolve.            
           apply Cut...
   - assert(n |--- B; M; (> (F :: G :: S1) ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; M ++ N; (> ((F :: G :: S1) ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j) (C:=C) (dualC:=C ^)...
           inversion H1...
           inversion H1...
           SLSolve. 
           apply Cut...
   - assert(n |--- B; M; (> (F :: S1) ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; M ++ N; (> ((F :: S1) ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion H1...
           SLSolve.            
           apply Cut...
   - assert(n |--- B; M; (> (G :: S1) ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; M ++ N; (> ((G :: S1) ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion H1...
           SLSolve.
           apply Cut...
   - destruct (uDec i0) .
     -- assert(n |--- (i0, F)::B; M; (> S1 ++ [C] ++ S2) ->
            j |--- (i0, F)::D; N; (> C ^ :: L3) ->
               |-- (i0, F)::BD; M ++ N; (> (S1++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion H1...
           SLSolve.
           rewrite HP1...
           rewrite HP2...
           rewrite HP3...
           apply Cut...
           apply weakeningN...                  
     -- assert(n |--- (i0, F)::B; M; (> S1 ++ [C] ++ S2) ->
            j |--- D ; N; (> C ^ :: L3) ->
               |-- (i0, F)::BD; M ++ N; (> (S1++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion H1...
           SLSolve.
           rewrite HP1...
           rewrite HP2...
           rewrite HP3...
           apply Cut...
   - assert(n |--- B; (o::M) ; (> S1 ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; (o::M) ++ N; (> (S1 ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion isFS1...
           SLSolve.
        rewrite app_comm_cons...
    - assert(n |--- B; M ; (> (FX x :: S1) ++ [C] ++ S2) ->
            j |--- D; N; (> C ^ :: L3) ->
               |-- BD; M ++ N; (> ((FX x :: S1) ++ S2) ++ L3)) as Cut.
           eapply CH with (m:=n + j)(C:=C) (dualC:=C ^)...
           inversion H1...
           SLSolve.
           apply Cut...
      apply H5...
  Qed.    
 
 
  Theorem CutUP  i j w h C L M N BD B D : CutH w h -> CutW w -> complexity C = S w -> S h = i + j ->
  isFormulaL (second BD) -> isFormulaL L -> isFormulaL M -> isFormulaL N -> isFormula C -> isFormula (C^) ->
 Permutation (getU BD) (getU B) ->
 Permutation (getU BD) (getU D) ->
 Permutation (getL BD) (getL B ++ getL D) ->
  i |--- B; M; (> C::L) ->
  j |--- D; N; (>> dual C) ->
  |-- BD; M ++ N; (> L).
Proof with sauto;solveLL.   
 intros CH CW compC hH isFBD isFL isFM isFN isFC isFDC HP1 HP2 HP3 Hi Hj.

 assert(isFormulaL (second D)) by SLSolve.
 assert(isFormulaL (second B)) by SLSolve.
 rename H into isFD.
 rename H0 into isFB.
 
 inversion Hi;subst. 
 * inversion Hj...
   CleanContext.
 * inversion Hj; CleanContext...
   rewrite cxtDestruct.
   rewrite HP1.
   rewrite HP3.
   rewrite <- cxtDestruct.
   apply seqNtoSeq  in H3;auto.
 * inversion Hj; CleanContext...
   rewrite cxtDestruct.
   rewrite HP1.
   rewrite HP3.
   rewrite H5.
   assert(isFormulaL (second D0)) by SLSolve.
   assert(isFormulaL (second B0)) by SLSolve.
 
   assert( n |--- B; M; (> F :: G :: L) -> 
          n0 |--- B0; M0; (>> F ^) -> 
             |-- getU D0 ++  getL B ++ getL B0; M ++ M0; (> G :: L)) as HcutF.
    eapply CW with (m:=complexity F)...
    inversion compC...
    SLSolve;SLSolve.
    SLSolve. SLSolve.
    inversion isFC...
     inversion isFDC... 
    CleanContext...
    rewrite <- H4...
    rewrite <- HP2...
    CleanContext...
    CleanContext...
    apply HcutF in H9;auto.
    apply seqtoSeqN in H9.
    destruct H9.
    assert(isFormulaL (second B0)) by SLSolve.
    assert(isFormulaL (second D0)) by SLSolve.
    assert( x |--- getU D0 ++ getL B ++ getL B0; M ++ M0; (> G :: L) -> 
           n0 |--- D0; N0; (>> G ^) -> 
              |-- getU B ++ getL B ++ getL B0 ++ getL D0; (M ++ M0) ++ N0; > L) as HcutG.
      eapply CW with (m:=complexity G);sauto.
       
      inversion compC...
      SLSolve;SLSolve.
     SLSolve;SLSolve.
        SLSolve. inversion isFC...
        inversion isFDC...
    CleanContext...
    CleanContext...
    CleanContext...
    rewrite H1.
    LLPerm((M ++ M0) ++ N0)...
 * inversion Hj; CleanContext...
   assert( n |--- B; M; (> F :: L) -> 
          n0 |--- D; N; (>> F ^) -> 
             |-- BD; M ++ N; (> L)) as HcutF.
    eapply CW with (m:=complexity F)...
     
    inversion compC... 
    inversion isFC...
    inversion isFDC...
    apply  HcutF ... 
  assert( n |--- B; M; (> G :: L) -> 
          n0 |--- D; N; (>> G ^) -> 
             |-- BD; M ++ N; (> L)) as HcutG.
    eapply CW with (m:=complexity G)...
     
    inversion compC...
    inversion isFC...
    inversion isFDC...
     apply  HcutG...
 * assert(N=[]).
   inversion Hj...
   subst.
    assert( n |--- B ++ [(i0,F)]; M ; (> L) -> 
           j |--- D; []; (>> i0 ! F ^) -> 
             |-- BD; M ; (> L)) as UCCut.
    eapply CH with (m:=h) (C:=i0 ? F) (dualC:=i0 ! F^);eauto.
    rewrite app_nil_r...
    apply UCCut...
    LLExact H3.
 * apply NotAsynchronousPosAtoms in H4...
   apply PositiveDualRelease in H.
     inversion Hj;subst; try match goal with
       [ H: _= dual ?C , H2: release (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
    assert( n |--- B; M ++ [C]; (> L) -> 
            n0 |--- D; N; (> [dual C]) -> 
             |-- BD; M ++ N; (> L++[])) as ULCut.
   eapply CH with (m:=n+n0)... 
   CleanContext.
   apply ULCut...
   LLExact H5.
    
   inversion H...
   simpl in Hj.
   inversion Hj...
   rewrite (simplUnb BD _ HP2 HP1)...
   apply seqNtoSeq in Hi.  
   inversion Hi...
   LLExact H7.
   rewrite HP3...
   destruct (uDec i).
   rewrite <- H7 in HP2.
   rewrite <- H7 in HP3...
   CleanContext.
   rewrite cxtDestruct.
   rewrite HP3.
   rewrite HP2. 
   rewrite cxtDestruct in H5.
   rewrite <- HP1 in H5.
   rewrite HP2 in H5.
   rewrite <- app_comm_cons in H5.
   
   assert(n |--- (i, atom A) :: getU C ++ getL B;
     (atom A)::M; (> L)).
   LLExact H5.  
   eapply AbsorptionC in H0...
   apply seqNtoSeq in H0.
   LLExact H0.
   
   rewrite <- H7 in HP2.
   rewrite <- H7 in HP3...
   CleanContext.
   rewrite cxtDestruct.
   rewrite HP3.
   rewrite HP2. 
   rewrite cxtDestruct in H5.
   rewrite <- HP1 in H5.
   rewrite HP2 in H5.
   assert(n |--- getU C ++ getL B;
     (atom A)::M; (> L)).
   LLExact H5.  
   eapply @AbsorptionL with (i:=i) in H0...
   apply seqNtoSeq in H0.
   LLExact H0.
   inversion H1.
  * inversion Hj;CleanContext...
   assert( n  |--- B; M; (> (FX t :: L)) -> 
           n0 |--- D; N; (>> (FX t) ^) -> 
              |-- BD; M++N; (> L)) as HCut.
   eapply CW with (m:=complexity (FX (VAR con 0)));eauto...
   
   inversion compC...
   inversion isFC...
    inversion isFDC...
  inversion compC...
    remember (VAR con 0).
            assert(proper e).
            rewrite Heqe.  
            constructor.
            eapply ComplexityUniformEq...
            
            apply HCut... 
 Qed.           
     
      
Theorem CutK4SubCase (h n j w:nat) i a L B D BD P: CutH w h -> CutW w -> complexity P = w -> S h = S n + j -> i <> loc ->
  isFormulaL (second BD) -> isFormulaL L -> isFormula P -> isFormula (dual P) ->
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
 tri_bangK4 theory n (B ++ [(a, P)]) i [] [] (> L) -> 
 j |--- D; []; (>> a ! P ^) -> tri_bangK4' theory BD i [] [] (> L).
 Proof with sauto;solveF.
 intros HC WC comP hH Hd isFBD isFL isFP isFPD UB UD LBD Hyp Hj.
 
  assert(isFormulaL (second D)) by SLSolve.
  assert(isFormulaL (second B)) by SLSolve.
  rename H into isFD.
  rename H0 into isFB.
 
 
        apply InvSubExpPhase in Hyp;auto. 
        destruct Hyp as [C4 Hyp];
        destruct Hyp as [CK Hyp];
        destruct Hyp as [CN Hyp].
        CleanContext.
        assert(isFormulaL (second C4) /\ isFormulaL (second CK) /\ isFormulaL (second CN)).
        assert(isFormulaL (second (C4++CK++CN))).
        srewrite_reverse H.
        change (Forall isFormula (second (B ++ [(a, P)]))) with (isFormulaL (second (B ++ [(a, P)]))).
        SLSolve.
        
        CleanContext;SLSolve.
        CleanContext.
        rename H6 into isFC4.
        rename H8 into isF_K.
        rename H9 into isFCN.

        checkPermutationCases H. 
        { (* P in C4 *)
         rewrite <- Permutation_cons_append in H4. 
         inversion Hj...
         
         { rewrite H4 in H0... 
          assert(False).
            apply locAlone in Hd.
            apply Hd... left. 
          inversion H0...  
             contradiction. }
           assert(lt i a /\ m4 a = true /\ SetK4 i x).
          { rewrite H4 in H0.
            inversion H0...  } 
          CleanContext.
         finishExponential.    
       assert(isFormulaL (second CK4) /\ isFormulaL (second CN0)).
        assert(isFormulaL (second (CK4++CN0))).
        apply Permutation_map with (f:=snd) in H.
        rewrite <- H;auto.
        split;SLSolve.
        CleanContext.
        rename H15 into isF_K4.
        rename H17 into isFCN0.
          assert(SetK4 i CK4).
          { eapply @SetK4Trans with (i:=a)... }
          assert(Permutation (getU B) (getU D)).
      
          rewrite <- UB.
          rewrite <- UD...
          rewrite <- H6 in H15.
          rewrite H in H15.
          CleanContext.
          change (getU CK4 ++ getU CN0) with (getU CK4 ++ [] ++ getU CN0) in H15.
          eapply @destructClassicSet' with (a:=i) in H15;auto;SLSolve.
          destruct H15 as [K_1 H15].
          destruct H15 as [K_2 H15].
          destruct H15 as [K_3 H15].
          destruct H15 as [K4_1 H15].
          destruct H15 as [K4_2 H15].
          destruct H15 as [K4_3 H15].
          destruct H15 as [N H15].
          simpl in *.         
          CleanContext.
          assert(Hd': S n0 |--- PlusT CK4; []; (>> (plust a) ! P^)).
          { apply CutK4BaseInit...  }
           rewrite cxtDestruct.
           rewrite UD.
           rewrite LBD.
           rewrite H...
           rewrite <- H6...
           CleanContext.
           eapply @GenK4Rel' with (C4:=getL x++CK4++K4_2) (CK:=CK) (CN:=N);sauto;SLSolve.
           SLSolve. 
           apply SetK4Destruct in H12;sauto.
           rewrite H18 in H15.
           SLSolve.
           assert(SetU (K4_3 ++ N)).
           rewrite <- H21;SLSolve.
           SLSolve. 
           
           
         assert(Hp: Permutation ((getU CK4 ++ getU CN0) ++ (getL x ++ getL CK) ++ getL CK4)
                             ((getU CK4 ++ getL CK4) ++ (getL x ++ getL CK) ++ getU CN0)) by perm.
          rewrite Hp. clear Hp.
          rewrite <- cxtDestruct.
          rewrite H23...
         rewrite (cxtDestruct CK).
          CleanContext.
          
          rewrite H17...
          assert(isFormulaL (second x)).
           srewrite H4 in isFC4.
           simpl in isFC4.
           SLSolve.
          
  assert(Hp: 
 (n - length (C4 ++ CK) - 1) |--- (PlusT (getL x ++ getU CK4 ++ K4_2) ++ Loc (getU CK)) ++ [(plust a,P)]; []; (>  L ++ second (getL CK)) ->
   S n0 |--- PlusT (CK4 ++ getU K4_2) ++ Loc (getU CK); []; (>> (plust a) ! P ^) -> 
   |-- PlusT (getL x ++ CK4 ++ K4_2) ++ Loc (getU CK) ; []; (> L ++ second (getL CK))).
         
           eapply HC with  (m:=n - length (C4 ++ CK) - 1 + S n0) (C:=(plust a) ? P) (dualC:=(plust a) ! P^);sauto. 
           lia. CleanContext.
           
           SLSolve;
           SLSolve;
           SLSolve.
           apply isFormulaL_getU in H15 .
           srewrite H18 in H15.
           rewrite secondApp in H15.
           SLSolve. 
            apply isFormulaL_PlusT;auto.
           SLSolve. SLSolve. 
           CleanContext.
SLSolve.           
           
           CleanContext.
           rewrite PlusTgetU...
           CleanContext.
            rewrite PlusTgetU...
          
           CleanContext.
           CleanContext.
           apply Hp... all: try clear Hp.
           CleanContext.
           rewrite H20...
          CleanContext.
           LLPerm((PlusT (getL x) ++ (PlusT K4_1 ++ PlusT K4_2) ++ [(plust a, P)] ++ Loc (getU CK)) ++ PlusT K4_3).
           apply weakeningGenN_rev...
            eapply exchangeCCN.
            2:{ exact H5. }
            rewrite H4.
            CleanContext.
            rewrite (cxtDestruct x).
            CleanContext.
            rewrite H18...
            assert(SetU (K4_1 ++ K4_3)).
            rewrite <- H20...
            SLSolve.
            apply SetUPlusT.
            SLSolve.
            CleanContext.
            
            
            LLPerm(PlusT CK4++(PlusT (getU K4_2) ++ Loc (getU CK)) ).
            apply weakeningGenN_rev...
            SLSolve.
          }
     {  rewrite <- Permutation_cons_append in H4. 
          checkPermutationCases H4. 
          { (* P in CK *)
        inversion Hj...
          { rewrite H4 in H2. 
             assert(False).
            apply locAlone in Hd.
            apply Hd... 
            inversion H2... contradiction. }
            
         destruct (uDec a).
          {
          apply InvSubExpPhaseU in H12;auto.  
          destruct H12 as [C4' H12].
          destruct H12 as [CK' H12].
          destruct H12 as [CN' H12].
          CleanContext.
          assert(isFormulaL (second C4') /\ isFormulaL (second CK') /\ isFormulaL (second CN')).
        assert(isFormulaL (second (C4'++CK'++CN'))).
        
        apply Permutation_map with (f:=snd) in H.
        rewrite <- H;auto.
        CleanContext;SLSolve.
        CleanContext. 
        rename H16 into isFC4'.
        rename H19 into isF_K'.
        rename H20 into isFCN'.
             assert(lt i a /\ m4 a = false /\ SetK i x0).
          { rewrite H4 in H2.
            inversion H2... 
            } CleanContext.
          assert(SetK4 i C4').
          { eapply @SetK4Trans with (i:=a)... }
          assert(SetK i CK').
          { eapply @SetKTrans with (i:=a)... }
            apply simplUnb' in LBD...
          2:{ rewrite H;SLSolve. }
          rewrite LBD in UD.
          rewrite <- H7 in H6.
          rewrite <- H6 in UD.
          rewrite H in UD.
          
          assert(HCK: Permutation CK ((a, P) :: x0)) by auto.
          
          apply Permutation_vs_cons_inv in H4...
          rewrite Permutation_midle in HCK. 
          apply Permutation_cons_inv in HCK. 
          
          assert(isFormulaL (second x0)).
          symmetry in H6.
          srewrite H6 in isFB.
          SLSolve.
          
          
          rename H4 into isFx0. 
          CleanContext.
           eapply @destructClassicSet' with (a:=i) in UD;auto;try SLSolve.
          destruct UD as [K_1 UD].
          destruct UD as [K_2 UD].
          destruct UD as [K_3 UD].
          destruct UD as [K4_1 UD].
          destruct UD as [K4_2 UD].
          destruct UD as [K4_3 UD].
          destruct UD as [N UD]...
         
         
       
          assert(Hd': S n0 |--- PlusT (getU C4') ++ Loc (getU CK'); []; (>> (loc) ! P^)).
          { solveLL;rewrite setUPlusTgetU;auto. 
            HProof.  } 
          
           rewrite cxtDestruct.
          rewrite UB.
          rewrite LBD.
          rewrite <- H6.
          CleanContext.
           rewrite <- HCK.
          assert(SetU (K_3 ++ K4_3 ++ N)).
          rewrite <- H24.
          SLSolve.
           assert(SetU (K_2 ++ K4_2 ++ N)).
          rewrite <- H26.
          SLSolve.
         
          eapply @GenK4Rel' with (C4:=C4++K4_3) (CK:=x1++x2++K_3) (CN:=N);sauto...
          SLSolve.
          apply SetK4Destruct in H12;sauto.
          rewrite H23 in H28...
          SLSolve.
          rewrite app_assoc.
          SLSolve.
          
          apply SetKDestruct in H18;sauto.
          rewrite H22 in H28...
          SLSolve.
          SLSolve.
          
          CleanContext.
          rewrite H24...
          rewrite (cxtDestruct x1).
          rewrite (cxtDestruct x2).
          rewrite (cxtDestruct C4)... 
            CleanContext.
         
          
            assert(Hp: 
      (n - length (C4 ++ x1 ++ x2)- 1) |--- ( (PlusT C4 ++ PlusT K4_3) ++ Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3)) ++ [(loc,P)]; []; (> L ++ second (getL x1) ++ second (getL x2)) ->
      S n0 |---  (PlusT (getU C4) ++ PlusT K4_3) ++ Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3); []; (>> loc ! P ^) -> 
           |--  (PlusT C4 ++ PlusT K4_3) ++ Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3) ; []; (> L ++ second (getL x1) ++ second (getL x2))).
         
        eapply HC with  (m:=n - length (C4 ++ x1 ++ x2) - 1 + S n0) (C:=loc ? P) (dualC:=loc ! P^);sauto.
        lia.
           CleanContext.
           
           SLSolve;SLSolve;SLSolve.
           assert(isFormulaL ( second (K4_1 ++ K4_3))).
           symmetry in H23.
           srewrite H23.
           SLSolve.
           apply isFormulaL_PlusT.
           SLSolve.
           
           apply isFormulaL_Loc;auto.
           apply isFormulaL_getU;auto.
           SLSolve.
           
           apply isFormulaL_Loc;auto.
           apply isFormulaL_getU;auto.
           SLSolve.
           
           assert(isFormulaL ( second (K_1 ++ K_3))).
           symmetry in H22.
           srewrite H22.
           SLSolve.
           apply isFormulaL_Loc;auto.
           apply isFormulaL_getU;auto.
           SLSolve.
           SLSolve;SLSolve.
           
           apply isFormulaL_getL;auto.
           SLSolve.
           apply isFormulaL_getL;auto.
           SLSolve.
           
      
        CleanContext.
        rewrite PlusTgetU...
         CleanContext.
         assert(SetU K4_3). SLSolve.
         
         
          rewrite (getLgetUPlusT' H28)...
         assert(SetU K_3). SLSolve.
        
          rewrite (SetU_then_empty H28)...
          sauto. 
         apply Hp... all: try clear Hp.
        LLPerm((Loc (getU K_3)++ PlusT K4_3) ++ ((PlusT C4 ++ Loc (getU x1) ++ Loc (getU x2) ++ [(loc, P)]))).
        apply weakeningGenN...
        eapply HeightGeqCEx.
        2:{ exact H5. }
        CleanContext. 
        assert(Hp: Permutation (C4 ++ x1 ++ (a, P) :: x2) ((a, P) :: C4 ++ x1 ++ x2)) by perm.
        rewrite Hp. simpl. lia.
        SLSolve.
        apply SetUPlusT.
        SLSolve.
        
        assert(Hp: Permutation ( Loc (getU x1) ++ Loc (getU x2)) (Loc (getU x0))).
        rewrite <- HCK...
        LLPerm(PlusT (getU C4) ++ PlusT K4_3 ++ (Loc (getU x1) ++ Loc (getU x2)) ++ Loc (getU K_3)).
        rewrite Hp.
        rewrite H4.
        rewrite H21.
        CleanContext.
        LLPerm((PlusT K4_2 ++ Loc K_2) ++ (PlusT K4_1 ++ PlusT K4_3 ++ Loc K_1 ++ Loc (getU K_3))).
        apply weakeningGenN...
        LLExact Hd'.
        
        
        rewrite (cxtDestruct C4').
        rewrite H22.
        rewrite H23.
        CleanContext.
        SLSolve.
        rewrite setULocgetU;auto.  perm.
       SLSolve. 
         apply SetUPlusT;auto.
      SLSolve.
       }
        
        { apply InvSubExpPhase in H12;auto.  
          destruct H12 as [C4' H12].
          destruct H12 as [CK' H12].
          destruct H12 as [CN' H12].
          CleanContext.
             assert(isFormulaL (second C4') /\ isFormulaL (second CK') /\ isFormulaL (second CN')).
        assert(isFormulaL (second (C4'++CK'++CN'))).
        
        apply Permutation_map with (f:=snd) in H.
        rewrite <- H;auto.
        CleanContext;
        SLSolve.
        CleanContext.
        rename H14 into isFC4'.
        rename H17 into isF_K'.
        rename H18 into isFCN'.
       
          
             assert(lt i a /\ m4 a = false /\ SetK i x0).
          { rewrite H4 in H2.
            inversion H2... 
            } CleanContext.
          assert(SetK4 i C4').
          { eapply @SetK4Trans with (i:=a)... }
          assert(SetK i CK').
          { eapply @SetKTrans with (i:=a)... }
          
          rewrite UB in UD.
          rewrite <- H7 in H6.
          rewrite <- H6 in UD.
          rewrite H in UD.
          CleanContext.
          assert(isFormulaL (second x0)).
          srewrite H4 in isF_K.
          simpl in isF_K.
          SLSolve.
          rename H19 into isFx0. 
          
          assert(HCK: Permutation CK ((a, P) :: x0)) by auto.
          apply Permutation_vs_cons_inv in H4...
          rewrite Permutation_midle in HCK. 
          apply Permutation_cons_inv in HCK. 
           eapply @destructClassicSet' with (a:=i) in UD;auto;try SLSolve.
          destruct UD as [K_1 UD].
          destruct UD as [K_2 UD].
          destruct UD as [K_3 UD].
          destruct UD as [K4_1 UD].
          destruct UD as [K4_2 UD].
          destruct UD as [K4_3 UD].
          destruct UD as [N UD]...
          
          CleanContext.
          rewrite cxtDestruct.
          rewrite UB.
          rewrite LBD.
          rewrite <- H6.
          rewrite H...
          CleanContext.
          rewrite <- HCK.
          CleanContext.
           assert(SetU (K_3 ++ K4_3 ++ N)).
          rewrite <- H22.
          SLSolve.
           assert(SetU (K_2 ++ K4_2 ++ N)).
          rewrite <- H24.
          SLSolve.
         
          eapply @GenK4Rel' with (C4:=C4++ getL C4' ++ K4_3) (CK:=x1++x2++getL CK'++K_3) (CN:=N);sauto...
          SLSolve.
           apply SetK4Destruct in H12;sauto.
          rewrite H21 in H26...
          SLSolve.
          rewrite app_assoc.
          SLSolve.
          
          apply SetKDestruct in H16;sauto.
          rewrite H20 in H26...
          SLSolve.
          SLSolve.
          
          CleanContext.
          rewrite H22...
          rewrite (cxtDestruct x1).
          rewrite (cxtDestruct x2).
          rewrite (cxtDestruct C4)... 
            CleanContext.
         
          assert(SetU K_3). SLSolve.
          assert(SetU K_2). SLSolve.
          assert(SetU K4_3). SLSolve.
          assert(SetU K4_2). SLSolve.
          rewrite (SetU_then_empty H26)...
          CleanContext.
           assert(Hp: 
    (n - length (C4 ++ x1 ++ x2) - 1) |--- 
   (PlusT C4 ++ PlusT K4_3) ++
       Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3);
    []; (>  (L ++ second (getL x1)) ++ [P] ++ second (getL x2)) ->
    
    n0 - length (C4' ++ CK') - 1 |--- 
    (PlusT (getU C4) ++ PlusT (getL C4') ++ PlusT K4_3) ++
       Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3);
     []; (> P ^ :: second (getL CK')) -> 
     
   |--(PlusT C4 ++ PlusT (getL C4') ++ PlusT K4_3) ++
       Loc (getU x1) ++ Loc (getU x2) ++ Loc (getU K_3); []++[];
    (> ((L ++ second (getL x1)) ++ second (getL x2)) ++ second (getL CK')) ).
     eapply WC with (C:=P) (dualC:=P^);sauto.
      
     { CleanContext.
       SLSolve.
       apply isFormulaL_PlusT;auto.
       
       apply isFormulaL_PlusT;auto.
       apply isFormulaL_getL;auto.
          
       apply isFormulaL_PlusT.
       assert(isFormulaL ( second (K4_1 ++ K4_3))).
           symmetry in H21.
           srewrite H21.
           apply isFormulaL_getU;auto.
           SLSolve.
           
           apply isFormulaL_Loc.
           apply isFormulaL_getU;auto.
           symmetry in HCK.
           srewrite HCK in isFx0.
           SLSolve.
           
           apply isFormulaL_Loc.
           apply isFormulaL_getU;auto.
           symmetry in HCK.
           srewrite HCK in isFx0.
           SLSolve.
           
            assert(isFormulaL ( second (K_1 ++ K_3))).
           symmetry in H20.
           srewrite H20.
           apply isFormulaL_getU;auto.
            apply isFormulaL_Loc.
           apply isFormulaL_getU;auto.
          
           SLSolve. }
     { SLSolve.
           apply isFormulaL_getL;auto.
           symmetry in HCK.
           srewrite HCK in isFx0.
           SLSolve.
           apply isFormulaL_getL;auto.
           symmetry in HCK.
           srewrite HCK in isFx0.
           SLSolve.
           apply isFormulaL_getL;auto. }
           
           CleanContext.
           CleanContext.
           rewrite PlusTgetU...
           CleanContext.
      rewrite (app_assoc L).
       rewrite (app_assoc (L ++ second (getL x1))).
     apply Hp. all: try clear Hp. 
     
     LLPerm((Loc (getU K_3) ++ PlusT K4_3) ++ (PlusT C4 ++ Loc (getU x1) ++ Loc (getU x2))).
     apply weakeningGenN...
     eapply HeightGeqCEx.
        2:{ rewrite app_assoc_reverse. exact H5. }
        CleanContext. 
        
        assert(Hp: Permutation (C4 ++ x1 ++ (a, P) :: x2) ((a, P) :: C4 ++ x1 ++ x2)) by perm.
        rewrite Hp. simpl. lia.
        SLSolve.
        apply SetUPlusT;auto.
        assert(Hp: Permutation ( Loc (getU x1) ++ Loc (getU x2)) (Loc (getU x0))).
        rewrite <- HCK...
        LLPerm(PlusT (getU C4) ++ PlusT (getL C4') ++ PlusT K4_3 ++ (Loc (getU x1) ++ Loc (getU x2)) ++ Loc (getU K_3)).
        rewrite Hp. clear Hp.
        rewrite H4.
        rewrite H19...
        CleanContext.
        LLPerm((Loc K_2 ++ PlusT K4_2) ++ (PlusT K4_1 ++ PlusT K4_3) ++
                PlusT (getL C4') ++ (Loc K_1 ++ Loc (getU K_3))). 
        apply weakeningGenN...
        LLExact H15.
        
        rewrite (cxtDestruct C4').
        CleanContext.
        rewrite H21...
        rewrite H20...
        CleanContext.
        rewrite setULocgetU...
        SLSolve.
        apply SetUPlusT;auto.
        
         } }
     assert(SetU x0).
       rewrite H4 in H3. SLSolve.
       assert(SetU D).
       apply BangUnb in Hj...
         rewrite H4 in H3. SLSolve.
       
        eapply @GenK4Rel' with (C4:=C4) (CK:=CK) (CN:= x0)...
        rewrite cxtDestruct.
        rewrite UB.
        rewrite LBD.
        rewrite H7.
        rewrite <- H6.
        rewrite (SetU_then_empty H8). 
        CleanContext.
        symmetry.
       rewrite (cxtDestruct C4).
       rewrite (cxtDestruct x).
       CleanContext.
       apply seqNtoSeq in H5...  }
 Qed.       

             
Theorem UCutDwC a j n w h P F L BD B D:
    CutH w h -> CutW w -> S h = n + j -> complexity P = w ->
    u a = true -> isFormulaL (second BD) -> isFormulaL L -> isFormula F -> isFormula P -> isFormula (dual P) ->
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    j |--- D; []; (>> a ! P ^) -> 
    n |--- B ++ [(a,P)]; L; (>> F) -> 
    |-- BD; L; (> [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc Hut isFBD isFL isFF isFP isFDP HP1 HP2 HP3 Hj Hn.
 assert(isFormulaL (second B)) by SLSolve.
 rename H into isFB.
 
 
     assert(SetU D).
     eapply BangUnb in Hj;auto.
     rewrite cxtDestruct in Hj.
     rewrite (SetU_then_empty H) in *.
    
     CleanContext.
    clear H.
    rewrite cxtDestruct.
    rewrite HP2.
    rewrite HP3.
    assert(Permutation (getU D) (getU B)).
    rewrite <- HP1.
    rewrite <- HP2;auto.
    clear HP1 HP2 HP3.
    rewrite H.
    rewrite H in Hj. clear H isFBD.   
    rewrite <- cxtDestruct.
    inversion Hn...
    * 
      store.
      decide1 (perp A).
   * checkPermutationCases H5.
      { 
       store.
        decide1 (perp A). 
          } 
      { inversion H2...
        simpl in Hj.
        rewrite H3.
        rewrite H3 in Hj.
        rewrite cxtDestruct.
        rewrite (SetU_then_empty H0).
        CleanContext.
        apply (InvBangT Hut H1 Hj). } 
     * 
      store. decide1 one.    
  * 
      CleanContext.
      CleanContext.
      assert(isFormulaL (second B0)).
      
 eapply @isFormulaSecondSplit1 with (D:=D0) (BD:=B) (X:=[(a,P)]) (Y:=[]);sauto.
 SLSolve.
 rename H into isFB0.
     assert(isFormulaL (second D0)).
 eapply @isFormulaSecondSplit2 with (D:=D0) (BD:=B) (X:=[(a,P)]) (Y:=[]);sauto.
 SLSolve.
 rename H into isFD0.
 
      
      assert(n0 |--- (getU B ++ getL B0)  ++ [(a, P)]; M; (>> F0) ->
             j |--- getU B; []; (>> a ! P ^) ->
             |-- getU B ++ getL B0 ; M; (> [F0])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[F0])...
        SLSolve;SLSolve.
        SLSolve. 
        SLSolve.
     
      assert(n0 |--- (getU B ++ getL D0)  ++ [(a, P)]; N; (>> G) ->
             j |--- getU B; []; (>> a ! P ^) ->
             |-- getU B ++ getL D0 ; N; (> [G])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[G])...
      SLSolve;SLSolve.
        SLSolve. 
        SLSolve.
        rewrite H0.
        solveLL.
        rewrite <- (app_nil_r []).
        eapply @InvTensor with (B:=getU B ++ getL B0) (D:=getU B ++ getL D0)...
        CleanContext.  
        apply H;auto.
        LLPerm ((getU B ++ [(a, P)]) ++ getL B0 ).
        rewrite H1.
        rewrite <- cxtDestruct;auto.
        apply H5;auto.
        LLPerm ((getU B ++ [(a, P)]) ++ getL D0 ).
        rewrite H2.
        rewrite <- cxtDestruct;auto.
    *   assert(n0 |--- B ++ [(a, P)]; L; (>> F0) ->
             j |--- getU B; []; (>> a ! P ^) ->
             |-- B ; L; (> [F0])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[F0])...
        SLSolve.
        solveLL.
        rewrite <- (app_nil_r []).
        apply InvPlus...
    *   assert(n0 |--- B ++ [(a, P)]; L; (>> G) ->
             j |--- getU B; []; (>> a ! P ^) ->
             |-- B ; L; (> [G])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[G])...
                SLSolve.
        solveLL.
        rewrite <- (app_nil_r []).
        apply InvPlusComm...

    *   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (> [F]) ->
             j |--- getU B; []; (>> a !  P ^) -> 
               |-- B; L; (> [F])).
                                       
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j) (L:=[F])...
        
        apply Hc...
   *    
   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (>> (FX t)) ->
             j |--- getU B; []; (>> a !  P ^) -> 
               |-- B; L; (> [FX t])).
                                       
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j) (L:=[FX t])...
        SLSolve.
        solveLL.
        rewrite <- (app_nil_l []).
        eapply InvEx with (t0:=t)...
    *   
        assert(Hc:
            n0 |--- B ++ [(a,P)]; []; (> [F0]) ->
             j |--- getU B; []; (>> a !  P ^) -> 
               |-- B; []; (> [F0])).
         
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j) (L:=[F0])...
        1-5:exact nil.
        SLSolve.
        solveLL. decide1.
    * solveLL. decide1. 
      eapply @CutK4SubCase with (n:=n0) (j:=j) (h:=h) (P:=P) (a:=a) (w:=complexity P) (B:=B) (D:=getU B)...
      SLSolve. 
       
  Qed. 
 
 

 Theorem LCutDwC a j n w h P F L B D BD:
    CutH w h -> CutW w -> S h = n + j -> complexity P = w ->
    u a = false -> 
    isFormulaL (second BD) -> isFormulaL L -> isFormula F -> isFormula P -> isFormula (dual P) ->
     Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) -> 
     j |--- D; []; (>> a ! P ^) -> 
    n |--- B ++ [(a,P)]; L; (>> F) -> 
    |-- BD; L; (> [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc Hut isFBD isFL isFF isFP isFDP HP1 HP2 HP3 Hj Hn.
  assert(isFormulaL (second B)) by SLSolve.
  assert(isFormulaL (second D)) by SLSolve.
  rename H into isFB.
  rename H0 into isFD.
 
  inversion Hn...
   
    + assert(SetU [(a, P)]).
      SLSolve...
      inversion H...
   +
   checkPermutationCases H5.
      { assert(SetU [(a, P)]).
        rewrite <- H3 in H0.
        SLSolve...
        inversion H... }
      {
       inversion H2...
     inversion Hj... SLSolve.
     apply InvSubExpPhase in H7;auto.  
     destruct H7 as [C4 H7].
     destruct H7 as [CK H7].
     destruct H7 as [CN H7].
     CleanContext.
     assert(SetT C4).     
     { eapply (SetTK4Closure H1 H2). } 
     assert(SetT CK).     
     { eapply (SetTKClosure H1 H5). }
     rewrite cxtDestruct.
     rewrite HP2.
     rewrite HP3.
     CleanContext.
     rewrite SetU_then_empty. 
     2:{ rewrite H3... }
     rewrite H.
     CleanContext.
     LLPerm(getU CN ++(getL CK ++ (getU C4 ++ getL C4)) ++ getU CK).
     apply weakeningGen;SLSolve.
     apply Loc_Unb';SLSolve...
     rewrite cxtDestruct in H9.
     SLSolve.
     eapply @AbsorptionLinearSet with (C:=getL CK) (B':=(getU C4 ++ getL C4) ++  Loc (getU CK) );SLSolve...
     rewrite cxtDestruct in H9.
     SLSolve.
     
     rewrite <- cxtDestruct.
     rewrite <- (SetTPlusT H7).
     CleanContext.
     HProof. }
      + 
      assert(SetU [(a, P)]).
      SLSolve...
      inversion H...    
  + 
      CleanContext.
      CleanContext.
      checkPermutationCases H3.
      -
      assert(SetL x).
      assert(SetL (x ++ getL D0)).
      rewrite H5;SLSolve. 
      SLSolve...
      rewrite (cxtDestruct x) in H5.
       rewrite (cxtDestruct x) in H3.
      rewrite (SetL_then_empty H) in H5...
      rewrite (SetL_then_empty H) in H3...
      
      rewrite cxtDestruct.
      rewrite HP3.
      rewrite <- H5.
      rewrite HP2.
      destruct (PositiveOrRelease G).
     assert(|-- getU D ++ (getL x ++ getL D0) ++ getL D; F0 ** G::M++N; UP ([]++[])).
      eapply @InvTensor with (B:=getL x ++ getL D ++ getU D) (D:=getU D++ getL D0)...
     CleanContext.
     CleanContext...
     CleanContext.
     assert(n0 |--- (getU D ++ getL x)  ++ [(a, P)]; M; (>> F0) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- getL x ++ getL D ++ getU D ; M; (> [F0])).
      { 
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[F0])...
        SLSolve.
        assert(isFormulaL (second (getL B))).
        SLSolve.
        symmetry in H5.
        srewrite H5 in H7.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        }
     apply H7...
     rewrite <- HP2.
     rewrite HP1.
     rewrite H1.
     rewrite app_assoc_reverse.
     rewrite <- H3.
     rewrite <- cxtDestruct;auto.
     rewrite <- HP2.
     rewrite HP1.
     rewrite H2.
     rewrite <- cxtDestruct;auto.
     store. inversion H6...
     decide1 G. inversion H6...
     apply seqNtoSeq in H8;auto.
     store.
     rewrite H0.
      CleanContext.
     assert(|-- getU D ++ (getL x ++ getL D0) ++ getL D; F0 ** G::M++N; UP ([]++[])).
      eapply @InvTensor with (B:=getL x ++ getL D ++ getU D) (D:=getU D++ getL D0)...
     CleanContext.
     CleanContext...
     CleanContext.
     assert(n0 |--- (getU D ++ getL x)  ++ [(a, P)]; M; (>> F0) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- getL x ++ getL D ++ getU D ; M; (> [F0])).
      {
      eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[F0])...
        SLSolve.
        assert(isFormulaL (second (getL B))).
        SLSolve.
        symmetry in H5.
        srewrite H5 in H7.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        }
     apply H7...
     rewrite <- HP2.
     rewrite HP1.
     rewrite H1.
     rewrite app_assoc_reverse.
     rewrite <- H3.
     rewrite <- cxtDestruct;auto.
     rewrite <- HP2.
     rewrite HP1.
     rewrite H2.
     rewrite <- cxtDestruct;auto.
     inversion H8;CleanContext...
     apply seqNtoSeq in H13;auto.
     store.
     rewrite H0.
      CleanContext.
  -    
      assert(SetL x).
      assert(SetL (getL B0 ++ x)).
      rewrite H5. apply getLtoSetL.
      SLSolve...
      rewrite (cxtDestruct x) in H5.
       rewrite (cxtDestruct x) in H3.
      rewrite (SetL_then_empty H) in H5...
      rewrite (SetL_then_empty H) in H3...
      
      rewrite cxtDestruct.
      rewrite HP3.
      rewrite <- H5.
      rewrite HP2.
      destruct (PositiveOrRelease F0).
     assert(|-- getU D ++ (getL x ++ getL B0) ++ getL D; F0 ** G::M++N; UP ([]++[])).
     eapply @InvTensor with (D:=getL x ++ getL D ++ getU D) (B:=getU D++ getL B0)...
     CleanContext.
     CleanContext...
     CleanContext.
     rewrite <- HP2.
     rewrite HP1.
     rewrite H1.
     rewrite <- cxtDestruct;auto.
     store. inversion H6...
     decide1 F0. inversion H6...
     apply seqNtoSeq in H4;auto.
     assert(n0 |--- (getU D ++ getL x)  ++ [(a, P)]; N; (>> G) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- getL x ++ getL D ++ getU D ; N; (> [G])).
      { 
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[G])...
        SLSolve.
        assert(isFormulaL (second (getL B))).
        SLSolve.
        symmetry in H5.
        srewrite H5 in H7.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
         }
     apply H7...
     rewrite <- HP2.
     rewrite HP1.
     rewrite H2.
     rewrite app_assoc_reverse.
     rewrite <- H3.
     rewrite <- cxtDestruct;auto.
     store.
     rewrite H0.
      CleanContext.
      LLExact H7.
           assert(|-- getU D ++ (getL x ++ getL B0) ++ getL D; F0 ** G::M++N; UP ([]++[])).
      eapply @InvTensor with (D:=getL x ++ getL D ++ getU D) (B:=getU D++ getL B0)...
 
     CleanContext.
     CleanContext...
     CleanContext.
     rewrite <- HP2.
     rewrite HP1.
     rewrite H1.
     rewrite <- cxtDestruct;auto.
     inversion H4;CleanContext...
     solveLinearLogic.
     assert(n0 |--- (getU D ++ getL x)  ++ [(a, P)]; N; (>> G) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- getL x ++ getL D ++ getU D ; N; (> [G])).
      {
      eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[G])...
        SLSolve.
        assert(isFormulaL (second (getL B))).
        SLSolve.
        symmetry in H5.
        srewrite H5 in H7.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        SLSolve.
        }
     apply H7...
     rewrite <- HP2.
     rewrite HP1.
     rewrite H2.
     rewrite app_assoc_reverse.
     rewrite <- H3.
     rewrite <- cxtDestruct;auto.
     store.
     rewrite H0.
      CleanContext.
      LLExact H7.
      + 
       assert(n0 |--- B  ++ [(a, P)]; L; (>> F0) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- BD ; L; (> [F0])).
      { 
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[F0])... SLSolve. }
        assert(|-- BD; F0 op G::L; UP ([]++[])).
        apply InvPlus...
        store... 
    + 
      assert(n0 |--- B  ++ [(a, P)]; L; (>> G) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- BD ; L; (> [G])).
      { 
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[G])... SLSolve. }
        assert(|-- BD; F0 op G::L; UP ([]++[])).
        apply InvPlusComm...
        store... 
     +    
        assert(Hc:
            n0 |--- B ++ [(a,P)]; L; (> [F]) ->
             j |--- D; []; (>> a !  P ^) -> 
               |-- BD; L; (> [F])).
                                       
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (L:=[F])...
        apply Hc...
        +
         assert(n0 |--- B  ++ [(a, P)]; L; (>> (FX t)) ->
             j |--- D; []; (>> a ! P ^) ->
             |-- BD ; L; (> [FX t])).
      { 
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P) (L:=[FX t])... SLSolve. }
        assert(|-- BD; E{ FX}::L; UP ([]++[])).
        eapply InvEx with (t0:=t)...
        store. 
     +   
       assert(SetU [(a, P)]).
      SLSolve...
      inversion H...    
     + store. decide1.
       eapply @CutK4SubCase with (n:=n0) (j:=j) (h:=h) (P:=P) (a:=a) (w:=complexity P) (B:=B) (D:=D)...
       SLSolve.
   Qed.  
    
 Theorem CutDwC a j n w h P F L B D BD:
    CutH w h -> CutW w -> S h = n + j -> complexity P = w ->
      isFormulaL (second BD) -> isFormulaL L -> isFormula F -> isFormula P -> isFormula (dual P) ->
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    j |--- D; []; (>> a ! P ^) -> 
    n |--- B ++ [(a,P)]; L; (>> F) -> 
    |-- BD; L; (> [F]).
  Proof with sauto.
  intros.
  destruct (uDec a).
  -  eapply UCutDwC with (w:=w) (h:=h) (n:=n) (j:=j) (a:=a) (P:=P) (D:=D) (B:=B)...
  -  eapply LCutDwC with (w:=w) (h:=h) (n:=n) (j:=j) (a:=a) (P:=P) (D:=D) (B:=B)...
   Qed.
 
 Theorem CutUPC  i j w h a A L M BD B D : CutH w h -> CutW w -> complexity A = w -> S h = i + j ->
 Permutation (getU BD) (getU B) ->
 Permutation (getU BD) (getU D) ->
 Permutation (getL BD) (getL B ++ getL D) ->
 isFormulaL (second BD) -> isFormulaL M -> isFormulaL L -> isFormula A -> isFormula (dual A) ->
  
  i |--- B++[(a,A)]; M; (> L) ->
  j |--- D; []; (>> a ! A ^) ->
  |-- BD; M; (> L).
Proof with sauto;solveLL.  
  intros CH CW compA hH HP1 HP2 HP3 isFBD isFM isFL isFA isFDA Hi Hj.
   assert(isFormulaL (second B)) by SLSolve.
  assert(isFormulaL (second D)) by SLSolve.
  rename H into isFB.
  rename H0 into isFD.
 
  inversion Hi...  
  --  assert( n |--- B ++ [(a,A)]; M; (> M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD; M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... SLSolve.
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (> F :: G :: M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD; M; (> F :: G ::M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... SLSolve. inversion H1... inversion H1...
              SLSolve. 
              apply Cut...
  --  assert( n |--- B ++ [(a,A)]; M; (> F :: M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD; M; (> F :: M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve. inversion H2...
              SLSolve. 
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (> G :: M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD; M; (> G ::M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve.
              inversion H2...
              SLSolve. 
              apply Cut...
  --  destruct (uDec i0).
      assert( n |--- ((i0, F)::B) ++ [(a,A)]; M; (> M0) ->
              j |--- (i0, F)::D; []; (>>  a ! A ^) -> |-- (i0, F)::BD; M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve.
              inversion H1...
              SLSolve. 
              rewrite e. 
              CleanContext...
              rewrite e. 
              CleanContext...
              rewrite e. 
              CleanContext...
              apply Cut...
              apply weakeningN...
      assert( n |--- ((i0, F)::B) ++ [(a,A)]; M; (> M0) ->
              j |--- D ; []; (>>  a ! A ^) -> |-- (i0, F)::BD; M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve.
              inversion H1...
              SLSolve. 
              rewrite e. 
              CleanContext...
              rewrite e. 
              CleanContext...
              rewrite e. 
              CleanContext...
              apply Cut...
  --  assert( n |--- B ++ [(a,A)]; F::M; (> M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD ; F::M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve.
              inversion isFL...
              SLSolve. 
              apply Cut...
  -- destruct (PositiveOrRelease F).
     assert( n |--- B ++ [(a,A)]; L'; (>> F) ->
             j |--- D; []; (>>  a ! A ^) -> |-- BD ; L'; (> [F])) as Cut.
     eapply CH with (C:=a ? A ) (dualC:=a ! A ^) (L:=[F])...
     apply Remove_Permute in H1...
     SLSolve.
     apply Remove_Permute in H1...
     rewrite H1 in isFM.
     inversion isFM...
     assert( |-- BD ; L'; (> [F])).
     apply Cut...
     inversion H2;subst;try solve [inversion H]. 
     apply Remove_Permute in H1...
     rewrite H1.
     LLExact H9.
     
     inversion H5;CleanContext...
     apply Remove_Permute in H1...
     rewrite H1.
     decide1 F.
     assert( n0 |--- B ++ [(a,A)]; L'; (> [F]) ->
             j |--- D; []; (>>  a ! A ^) -> |-- BD ; L'; (> [F])) as Cut.
     eapply CH with (m:=n0+j) (C:=a ? A ) (dualC:=a ! A ^) (L:=[F])...
     rewrite H1 in isFM.
     inversion isFM...
     rewrite H1 in isFM.
     inversion isFM...
     apply Cut...
  --  apply in_app_or in H3...
      +   assert( n |--- B ++ [(a,A)]; M; (>> F) ->
          j |--- D; []; (>>  a ! A ^) -> |-- BD ; M; (> [F])) as Cut.
          eapply CH with (C:=a ? A ) (dualC:=a ! A ^) (L:=[F])...
          SLSolve.
          eapply @AbsorptionClassic with (i:=i0) (F:=F)...
       
          rewrite cxtDestruct. 
          rewrite HP1.
          apply in_or_app. left.
          apply uIngetU...
      + inversion H... 
        
        assert(SetU D).
        apply BangUnb in Hj...
        assert( Permutation BD B).
        eapply (simplUnb _ B HP2 HP1 _ H). 
        rewrite H3 in *. clear H3 HP1 HP3.
        
        assert( n |--- B ++ [(i0,F)]; M; (>> F) ->
          j |--- D; []; (>>  i0 ! F ^) -> |-- B ; M; (> [F])) as Cut.
          eapply CH with (C:=i0 ? F ) (dualC:=i0 ! F ^) (L:=[F])...
          assert(Hs: |-- B; M; (> [F]))...
          clear Cut.
          apply seqtoSeqN in Hs.
          destruct Hs as [x Hs].
          apply InvBangT in Hj...
         apply seqtoSeqN in Hj.
          destruct Hj as [y Hj].
           
            destruct(PositiveOrRelease F).
            assert(release (F ^)).
            apply PositiveDualRelease...
             
            assert( x |--- B; M ; (> [F]) -> 
                    S y |--- D; []; (>> F ^) ->
                      |-- B; M++[] ; > [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            CleanContext. 
           
            assert( y |--- D; [] ; (> [F^]) -> 
                  S x |--- B; M; (>> F) ->
                      |-- B; []++M ; > [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            rewrite <- ng_involutive...
            rewrite DualComplexity.
            rewrite <- ng_involutive...
            CleanContext.
   --  apply Remove_Permute in H3. 
       checkPermutationCases H3... 3:{ exact nil. }
         - 
         rewrite cxtDestruct.
         rewrite HP1.
         rewrite HP3.
         rewrite H3.
         CleanContext.
         assert(Hs:|--getU x ++ getL x ++ getL D ; M; (> [F])).
         eapply CutDwC with (P:=A) (j:=j) (a:=a) (n:= S n) (h:=h) (w:=complexity A) (B:=x) (D:=D)...
         CleanContext. SLSolve.
         apply isFormulaL_getU.
         srewrite H3 in isFB.
         SLSolve.
         apply isFormulaL_getL.
         srewrite H3 in isFB.
         SLSolve.
         SLSolve.
         srewrite H3 in isFB.
         SLSolve.
         inversion isFB...
         CleanContext.
         rewrite <- HP2.
         rewrite HP1.
         rewrite H3.
         CleanContext.
         CleanContext.
         rewrite H4...
         eapply @HeightGeq with (n:=n)...      
            LLPerm ((i0, F) :: (getU x ++ getL x ++ getL D)).
            eapply @AbsorptionLinear with (i:=i0) (F:=F)...
       - 
          inversion H3...  
          rewrite <- H4 in H7.
          clear H4.
          inversion Hj...
          inversion H3.
          solveSubExp.
             apply InvSubExpPhase in H8;auto. 
             destruct H8 as [C4 H8].
             destruct H8 as [CK H8].
             destruct H8 as [CN H8]... 
             assert(SetT C4).
             { eapply (SetTK4Closure H1 H3). }
            assert(SetT CK).
             { eapply (SetTKClosure H1 H5). }
            rewrite cxtDestruct.
            rewrite HP2.
            rewrite HP3.
            rewrite H.
            CleanContext.
            eapply @AbsorptionLinearSet with (C:=getL CK) (B':=(getU C4 ++ getU CK ++ getU CN) ++
   getL B ++ getL C4)...
            rewrite cxtDestruct in H10.
            SLSolve...
            LLPerm ((getU CN ++ getU C4 ++  getL C4 ++ getL B )++ getU CK).
           apply ContractionL'...
           apply getUtoSetU.
           rewrite cxtDestruct in H10.
           SLSolve...
          
           assert(
         n0 - length (C4 ++ CK) - 1  |--- getU CN ++ getU CK ++ getU C4 ++ getL C4 ++ Loc (getU CK); [] ; (> (dual A ::second (getL CK))) -> 
                    n  |--- Loc (getU CK) ++ getU CN ++ getU C4 ++ getL B ++ getU CK; M; (>> A) ->
              |-- (getU CN ++ getU C4 ++ getL C4 ++ getL B) ++ getU CK ++ Loc (getU CK); []++M ; > second (getL CK)) as DCCut.
               eapply CW with (m:=complexity A)...
           CleanContext.
           SLSolve;SLSolve.
           srewrite H in isFD.
           apply isFormulaL_getU.
           SLSolve.
           srewrite H in isFD.
           apply isFormulaL_getU.
           SLSolve.
           srewrite H in isFD.
           apply isFormulaL_getL.
           SLSolve.
           srewrite H in isFD.
           apply isFormulaL_getU.
           SLSolve.
           srewrite H in isFD.
           apply isFormulaL_Loc.
           apply isFormulaL_getU.
           SLSolve.
           srewrite H in isFD.
           apply isFormulaL_getL.
           SLSolve.
               
           rewrite <- ng_involutive...
              
             rewrite DualComplexity . 
                rewrite <- ng_involutive...  
            CleanContext.
            CleanContext.
             CleanContext.
            apply DCCut...
            
            apply weakeningGenN.
            apply weakeningGenN.
            eapply exchangeCCN.
            2:{ exact H11. }
            rewrite (cxtDestruct C4).
            CleanContext.
            SLSolve.
            SLSolve.
            apply weakeningGenN.
             eapply exchangeCCN.
            2:{ exact H7. }
            rewrite (cxtDestruct B).
            CleanContext.
            rewrite <- HP1.
            rewrite HP2.
            rewrite H.
             CleanContext.
             SLSolve.
    --     assert(Hs:|-- BD; M; (> [F])).
              eapply CutDwC with (P:=A) (B:=B) (D:=D) (BD:=BD) (j:=j) (a:=a) (n:=S n) (h:=h) (w:=complexity A)...
            eapply @HeightGeq with (n:=n)...  
             destruct (NegativeAtomDec F).
              2:{  eapply @AbsorptionTheory with (F:=F)... }
             
             inversion H...
             eapply @AbsorptionPerp' with (A:=A0)...
  --  assert( n |--- B ++ [(a,A)]; M; (> FX x ::  M0) ->
              j |--- D; []; (>>  a ! A ^) -> |-- BD ; M; (> FX x :: M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
              SLSolve.
              inversion H2...
              SLSolve. 
              apply Cut...
  -- createWorld i0. 
     eapply @CutK4SubCase with (n:=n) (j:=j) (h:=h) (P:=A) (a:=a) (w:=complexity A) (B:=B) (D:=D)...
     intro... SLSolve.
  Unshelve .
  rewrite HP3...
  Qed.
 
  Theorem CutElimination i j a C dualC A dualA B D BD L L1 L2 L3 S1 S2 M N P: 
    isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL N ->
    isFormulaL L ->
    isFormula C ->
    isFormula dualC ->
    dualC = dual C -> 
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
   (L = L1++L2 -> i |--- B; M ++ [C]; (> L1) -> j |--- D; N; (> dualC::L2) -> |-- BD; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- D; N; (>> dualC) -> |-- BD; M ++ N; (> L)) /\
      (L = (S1++S2)++L3 -> i |--- B; M; (> S1++[C]++S2) -> j |--- D; N; (> dual C::L3) -> |-- BD; M ++ N; (> L)  ) /\
       (dualA = A ^ ->
       dualC = a ! dualA -> L = [P] ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- D; []; (>> a ! dualA) -> |-- BD; M; (> L)). 
     Proof with sauto;solveF;solveLL.
    assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert a i j C dualC A dualA P BD B D L L1 L2 L3 S1 S2 M N.
    
    
    induction w using strongind;intros.
    - assert(complexity C > 0) by apply Complexity0.
      rewrite H in H10. inversion H10.
    - remember (plus i j) as h.
      revert dependent BD.
      revert dependent B.
      revert dependent D.
      revert dependent L.
      revert dependent L1.
      revert dependent L2.
      revert dependent L3. 
      revert dependent S1.
      revert dependent S2.       
      revert dependent M.
      revert dependent N.
      revert dependent P.
      revert dependent dualA.
      
      revert A.
      revert dependent C.
      revert dependent dualC.
      
      revert dependent i.
      revert a j.
      dependent induction h using strongind; intros.
      +
        symmetry in Heqh.
        apply plus_is_O in Heqh.
        destruct Heqh;subst.
        eapply CutElimBase... 
        
      + rename H into CutW.
        rename H0 into CutH.
        rename H1 into compC.
        
        move BD at top.
        move B at top.
        move D at top.
        move M at top.
        move N at top.
        move L at top.
        move L2 at top.
        move L1 at top.
        move S1 at top.
        move S2 at top.
        move C at top.
        move A at top.
        move dualC at top.
        move dualA at top.
        move P at top.
        
        
        subst.
        split;[intros 
              |split;[intros 
                           |split;[intros
                            |split;intros]]].
                            
                            
       *  eapply (@CutUPLStar i j w h C L L1 L2 M N BD B D)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
        * eapply (@CutUP i j w h C L M N BD B D)...     
           unfold CutElimination.CutH; intros.
           eapply CutH with (m:=m)... 
           unfold CutElimination.CutW; intros.
           eapply CutW with (m:=m)...
        * eapply (@CutUPStar i j w h C L S1 S2 L3 M N BD B D)... 
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
        * subst. eapply (@CutDwC a j i w h A P M B D BD)...  
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
           unfold CutElimination.CutW; intros.
          eapply CutW with (m:=m)...
          rewrite DualComplexity in compC...
              rewrite H0 in compC...
              inversion compC...
              apply DualComplexity. 
              all: clear CutH CutW.
              inversion H4...
              assert(C = a ? A).
              rewrite (ng_involutive C).
              rewrite H0;simpl...
              rewrite <- ng_involutive...
              rewrite H in H5.
              inversion H5...
              rewrite H0 in H6.
              inversion H6...
        * 
          assert(C = a ? A).
              rewrite (ng_involutive C).
              rewrite H0;simpl...
              rewrite <- ng_involutive...
              
          eapply (@CutUPC i j w h a A L M BD B D)... 
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
           unfold CutElimination.CutW; intros.
          eapply CutW with (m:=m)...
         rewrite DualComplexity in compC...
              rewrite H0 in compC...
              inversion compC...
               all: clear CutH CutW.
              inversion H5...
              inversion H6...
 Qed.             
     
  Theorem GeneralCut i j C BD B D L M N: 
  isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL N ->
    isFormulaL L ->
    isFormula C ->
    isFormula (C ^) ->
    
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    (i |--- B; M ; UP (C::L) -> 
                   j |--- D; N ; DW (dual C) -> 
                                 |-- BD; M++N ; UP L).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H10 as [w H10].
    specialize CutElimination;intros.
    assert((i |--- B; M ; UP (C::L) -> 
                          j |--- D; N ; DW (dual C) -> 
                                        |-- BD; M++N ; UP L)) as CUT.
    eapply H11;eauto.
    
    clear H11.
    apply CUT;auto.  
  Qed. 
  
  Theorem GeneralCutClassic i j a A BD B D L M: 
    isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL L ->
    isFormula A ->
    isFormula (A ^) ->  
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    (i |--- B ++ [(a,A)] ; M; (> L) -> j |--- D; []; (>> a ! A^) -> |-- BD; M; (> L)).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity A = w). 
    eexists; auto.
    destruct H9 as [w H9].
    specialize CutElimination;intros.
    assert((i |--- B ++ [(a,A)]; M ; UP L -> 
                          j |--- D; [] ; DW (a ! A^) -> 
                                        |-- BD; M ; UP L)) as CUT.
    eapply H10 with (C:=a ? A) (dualC:=(a ? A) ^);eauto.
    clear H5.
    simpl. constructor;auto.
    apply CUT;auto.  
  Qed. 
  
    Theorem GeneralCutClassic' a A BD B D L M: 
    isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL L ->
    isFormula A ->
    isFormula (A ^) ->  
  
    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    (|-- B ++ [(a,A)] ; M; (> L) -> |-- D; []; (>> a ! A^) -> |-- BD; M; (> L)).
  Proof with subst;auto.
    intros. 
    apply seqtoSeqN in H7.
    apply seqtoSeqN in H8.
    CleanContext.
    eapply GeneralCutClassic with (B:= B) (D:=D) (a:=a) (A:=A);eauto.
  Qed.
   
  Theorem GeneralCut' C BD B D L M N: 
   isFormulaL (second BD) ->
    isFormulaL M ->
    isFormulaL N ->
    isFormulaL L ->
    isFormula C ->
    isFormula (C ^) ->

    Permutation (getU BD) (getU B) ->
    Permutation (getU BD) (getU D) ->
    Permutation (getL BD) (getL B ++ getL D) ->
    (|-- B; M ; UP (C::L) -> 
                   |-- D; N ; DW (dual C) -> 
                                 |-- BD; M++N ; UP L).
  Proof with subst;auto.
    intros.
    apply seqtoSeqN in H8.
    apply seqtoSeqN in H9.
    CleanContext.
    eapply GeneralCut with (C:= C) (B:=B);eauto.
  Qed.


    
End CutElimination.
