(** Cut Elimination for Focused Linear Logic

This file proves cut-elimination for the triadic system of linear
logic. The proof uses 5 cut-rules dealing with the negative and
positive phase of proofs (see [CutElimBase]).

It is assumed that the theory only produces well formed LL formulas
(see [TheoryIsFormula]).
 *)


Require Export MMLL.Misc.Hybrid.
Require Export MMLL.SL.FLLTactics.
Require Import Lia.
Require Import MMLL.Misc.Permutations.
Require Import FunInd.
Require Import Coq.Program.Equality.
Require Export MMLL.SL.InvPositivePhase.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.


Section CutElimination.
Context `{OLS: OLSig}.
Context `{SI : Signature}.
Context {USI : UnbSignature}.

Local Hint Resolve allU :core.

  Variable theory : oo -> Prop .
  Notation " n '|---' B ';' L ';' X " := (seqN theory n B L X) (at level 80).
  Notation " '|--' B ';' L ';' X " := (seq theory B L X) (at level 80).


 Lemma simplUnb B D:          
  Permutation (getU B) (getU D) ->
  Permutation B D.
  Proof.   
  intros.
  rewrite (cxtDestruct B).
  rewrite (cxtDestruct D).
  rewrite H.
  rewrite allSeTLEmpty;auto.
  rewrite allSeTLEmpty;auto.
  Qed.
      

 Lemma InvBangTN i j B P : mt i = true ->
           j |--- B; []; (DW (Bang i  P)) -> (j-1) |--- B; []; (UP [P]).
  Proof with sauto.
  intros Hm Hj.
  inversion Hj...
  inversion H0.
  eapply InvSubExpPhaseUT in H4;auto. 
  destruct H4 as [C4 H4].
  destruct H4 as [CK H4].
  destruct H4 as [CN H4]...
  rewrite H.
  rewrite app_assoc. 
  apply weakeningGenN_rev;auto.
  rewrite Permutation_app_comm.
  apply ContractionL...
  LLPerm ((C4 ++ Loc CK) ++ CK).
  apply weakeningGenN_rev;auto.
  eapply @HeightGeq with (n:=n - length (C4 ++ CK) - 1)...
 Qed. 

 Lemma InvBangTNLoc i j A B P : mt i = true -> m4 i = true ->
       j |--- (loc,A)::B; []; (DW (Bang i P)) -> 
       (exists C4 CN, Permutation B (C4++CN) /\ (j - length C4 - 2) |--- C4; []; (UP [P]) /\ SetK4 C4 /\ SetT C4 /\ LtX i C4 ).
  Proof with sauto.
  intros HmT Hm4 Hj.
  assert(i <> loc).
  solveSignature1.
  inversion Hj;subst;auto.
  inversion H1. 
  assert(False).
  apply H... sauto.
  eapply InvSubExpPhaseUTK4 in H5;auto. 
  destruct H5 as [C4 H5].
  destruct H5 as [CN H5]...
  checkPermutationCases H0.
  rewrite H0 in H2.
  inversion H2... solveSignature1.
  exists C4.
  exists x.
  split;sauto. 
  eapply @HeightGeq with (n:=n - length C4 - 1)...
  rewrite NatComp...
 Qed. 
 
  Lemma InvBangT i j B P : mt i = true ->
           j |--- B; []; (DW (Bang i P)) -> |-- B; []; (UP [P]).
  Proof with sauto.
  intros Hm Hj.
  apply InvBangTN in Hj...
  apply seqNtoSeq in Hj...
 Qed. 
  
   
     Lemma LtXPlusT  a K : LtX a K -> LtX (plust a) (PlusT K).
  Proof with sauto.
  induction K;simpl;intros...
  destruct a0 as [b F].
  inversion H...
  apply IHK in H3...
  apply Forall_cons...
   apply plust_mono ...
  Qed.
Lemma BangPlusT n C P a : a <> loc -> SetK4 C -> LtX a C -> n >= length C + 1 -> 
        n - length C - 1 |--- PlusT C; []; (UP [P]) ->
        S n |--- PlusT C; []; (DW (Bang (plust a) P)).
Proof with sauto.
 intros. 
  createWorld.
  apply plust_loc_diff...
  eapply @GenK4Rel with (C4:=PlusT C) (CK:=[]) (CN:=[])...
  apply plust_loc_diff...
  apply SetK4PlusT...
  apply LtXPlusT...
  autounfold.
  rewrite map_length...
  simpl...
  simplFix...
  autounfold.
  rewrite map_length...
Qed.

  Theorem CutElimBase a C dualC A dualA B L M N P: 
    dualC = dual C ->
      (0 |--- B; M ++ [C]; (UP L) -> 0 |--- B; N; (UP [dualC]) -> |-- B; M ++ N; (UP L)) /\
      (0 |--- B; M; (UP (C :: L)) -> 0 |--- B; N; (DW dualC) -> |-- B; M ++ N; (UP L)) /\
      (dualA = A ^ ->
       dualC = Bang a dualA ->
       0 |--- B ++ [(a,A)] ; M; (DW P) -> 0 |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP [P]))  /\
     (dualA = A ^ ->
       dualC = Bang a dualA ->
       0 |--- B ++ [(a,A)] ; M; (UP L) -> 0 |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP L)). 
    
  Proof with sauto;try solveLL.
    intros CDual.
    split;[intros
          |split;[intros
          |split;intros]].
    * inversion H...
    * inversion H...
      inversion H0.
    * inversion H2...
    * inversion H2...
  Qed.
  
   Definition CutW (w: nat) :=  
    forall a m i j C dualC A dualA P M N L B, 
    m <= w ->
    dualC = C ^ ->
    complexity C = m ->
      (i |--- B; M ++ [C]; (UP L) -> j |--- B; N; (UP [dualC]) -> |-- B; M ++ N; (UP L)) /\
      (i |--- B; M; (UP (C :: L)) -> j |--- B; N; (DW dualC) -> |-- B; M ++ N; (UP L)) /\
       (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (DW P) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP [P]))  /\
      (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (UP L) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP L)). 
    
  Definition CutH (w h: nat) :=  
    forall a m i j C dualC A dualA P M N L B, 
    m <= h ->
    m = i + j ->
    dualC = C ^ ->
    complexity C = S w ->
      (i |--- B; M ++ [C]; (UP L) -> j |--- B; N; (UP [dualC]) -> |-- B; M ++ N; (UP L)) /\
      (i |--- B; M; (UP (C :: L)) -> j |--- B; N; (DW dualC) -> |-- B; M ++ N; (UP L)) /\
      (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (DW P) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP [P]))   /\
      (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (UP L) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP L)). 
       
Theorem CutUPLStar  i j w h C L M N B : CutH w h -> complexity C = S w -> S h = i + j ->
  i |--- B; M ++ [C]; (UP L) ->
  j |--- B; N; (UP [C ^]) ->
  |-- B; M ++ N; (UP L ).
Proof with sauto;try solveLL.  
 intros CH compC hH Hi Hj.
 inversion Hi...
 * assert(n |--- B; M ++ [C]; (UP M0) ->
          j |--- B; N; (UP [dual C]) ->
            |-- B; M ++ N; (UP M0)) as Cut.
           eapply CH...
                    
           apply Cut...
 * assert(n |--- B; M ++ [C]; (UP (F :: G :: M0)) ->
          j |--- B; N; (UP [dual C]) ->
            |-- B; M ++ N; (UP (F :: G :: M0))) as Cut.
           eapply CH...
                    
           apply Cut...                                       
 * assert(n |--- B; M ++ [C]; (UP (F  :: M0)) ->
          j |--- B; N; (UP [dual C]) ->
            |-- B; M ++ N; (UP (F :: M0))) as CutF.
           eapply CH...
                    
           apply CutF...             

 * assert(n |--- B; M ++ [C]; (UP (G  :: M0)) ->
          j |--- B; N; (UP [dual C]) ->
            |-- B; M ++ N; (UP (G :: M0))) as CutG.
           eapply CH...
                    
           apply CutG...             

 * assert(n |--- B ++ [(i0, F)]; M ++ [C]; (UP M0) ->
            j |--- B ++ [(i0, F)]; N; (UP [dual C]) ->
              |-- B ++ [(i0, F)]; M ++ N; (UP M0)) as Cut.
           eapply CH...
           rewrite Permutation_cons_append.         
           apply Cut...
           LLExact H3.
           apply weakeningGenN_rev...
 * assert(n |--- B; (M ++ [F]) ++ [C]; (UP M0) ->
          j |--- B; N; (UP [dual C]) ->
            |-- B; (M ++ [F]) ++ N; (UP M0)) as Cut.
           eapply CH...
                    
           LLPerm((M ++ [F]) ++ N).
           apply Cut...
           LLExact H4.
 *checkPermutationCases H1.
   2:{ inversion H1...
       rewrite H2.
       assert(j |--- B; N; (UP [dual C]) ->
              n |--- B; L'; (DW C) ->
                |-- B; N++L'; (UP [])) as Cut.
       eapply CH with (m:=n + j)...
        
       lia.
       rewrite <- ng_involutive...
       rewrite DualComplexity in compC...
       LLPerm(N ++ L')... }
       
   destruct(PositiveOrNegative F).
   2:{ inversion H5;CleanContext... 
       rewrite H1.
       rewrite <- app_comm_cons.
        LFocus. LLRelease.
        assert(S n0 |--- B; x++ [C]; (UP [F]) ->
               j |--- B; N; (UP [dual C]) ->
                 |-- B; x ++ N; (UP [F])) as Cut.
                eapply CH with (m:=S n0 + j)...
                apply Cut... 
                rewrite <- H2 in H9.
                LLExact H9. }
       inversion H5...
            { 
              inversion Hj...
              apply seqNtoSeq in H7... } 
            {  apply simplUnb in H7.
               apply simplUnb in H6.
               clear H8.
              rewrite H4 in H2.
              checkPermutationCases H2.
              - 
              destruct(PositiveOrNegative F0).
              { (* first *) 
              assert(S n0 |--- B; (F0::x0)++[C]; (UP [])).
              LFocus F0 (x0++[C])...
              rewrite <- H2... LLExact H9.
              rewrite H1.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H3.
              LLPerm(MAnd G F0::N0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
              
              apply Derivation1.
              apply seqNtoSeq in H13...
              LLExact H13.
              assert(S n0 |--- B; (F0::x0) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (F0::x0) ++ N; (UP [ ])) as Cut.
                eapply CH... 
                rewrite <- (app_nil_l [F0]).
               apply UpExtension'.
               inversion H2...
               
               LLPerm((F0 :: x0) ++ N)...
               }
             { (* second *) 
              inversion H9;CleanContext...
              rewrite H1.
              rewrite <- app_comm_cons.
              apply TensorComm'.
              rewrite <- H3.
              LLPerm(MAnd G F0::N0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
                apply Derivation1.
                apply seqNtoSeq in H13... LLExact H13.
                 assert(n |--- B; x0 ++ [C]; (UP [F0]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x0 ++ N; (UP [F0])) as Cut.
                eapply CH with (m:=n + j)... 
                apply Cut...
                inversion H9;solveF... 
                LLExact H14. } 
             - 
              destruct(PositiveOrNegative G).
              { (* first *) 
              assert(S n0 |--- B; (G::x0)++[C]; (UP [])).
              LFocus G (x0++[C])...
              rewrite <- H2... LLExact H13.  
              rewrite H1.
              rewrite <- H3.
              LLPerm(MAnd F0 G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
              apply Derivation1.
              apply seqNtoSeq in H9...    LLExact H9.
           
              assert(S n0 |--- B; (G::x0) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (G::x0) ++ N; (UP [ ])) as Cut.
                eapply CH...
                  rewrite <- (app_nil_l [G]).
               
               apply UpExtension'.
               inversion H2...
               
               LLPerm((G :: x0) ++ N)... }
             { (* second *) 
              inversion H13;CleanContext...
              rewrite H1.
              rewrite <- H3.
              LLPerm(MAnd F0 G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
                apply Derivation1.
                apply seqNtoSeq in H9... LLExact H9.
              assert(n |--- B; x0++ [C]; (UP [G ]) ->
                          j |--- B; N; (UP [dual C]) ->
                         |-- B; x0 ++ N; (UP [G])) as Cut.
                 eapply CH with (m:=n + j)... 
                
                inversion H13;solveF...
                apply Cut... LLExact H14. }   
                }
    -   destruct(PositiveOrNegative F0).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 LLStore. 
                assert((S n0) |--- B; (F0::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (F0::x) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus F0. 
               LLExact H8. }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                assert(n |--- B; x ++ [C]; (UP [F0]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [F0])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H10. 
               } 
  -    destruct(PositiveOrNegative G).   
       {         rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                 LLStore. 
                
                assert((S n0) |--- B; (G::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (G::x ) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus G. 
               LLExact H8. }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                assert(n |--- B; x ++ [C]; (UP [G]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [G])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H10. 
               }
   -  apply PositiveNotNegative in H. contradiction. 
   -   destruct(PositiveOrNegative (FX t)).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 LLStore. 
                assert((S n0) |--- B; (FX t::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (FX t::x) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 LFocus (FX t). 
               LLExact H10. }
             {   inversion H10;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert(n |--- B; x ++ [C]; (UP [FX t]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [FX t])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H12. }
*  destruct(PositiveOrNegative F).
   2:{ inversion H7;CleanContext...
       apply @AbsorptionClassic' with (i:=i0) (F:=F)...
        assert(n0 |--- B; M ++ [C]; (UP [F]) ->
                j |--- B; N; (UP [dual C]) ->
                  |-- B; M ++ N; (UP [F])) as Cut.
       eapply CH with (m:=n0 + j)... 
       apply Cut... } 
       inversion H7...
       -  apply @AbsorptionClassic' with (i:=i0) (F:=perp A)...
          inversion Hj...
          apply seqNtoSeq in H12...  
       - apply simplUnb in H6.
         apply simplUnb in H8. clear H9.  
         checkPermutationCases H5.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H9.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'.
                inversion H4...
                
                 assert(S n0 |--- B; (F0::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (F0::x) ++ N; (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. 
               LLExact H10. 
               apply Derivation1.
               apply seqNtoSeq in H14... LLExact H14. }
            { (* first *) 
               rewrite <- H9.
               inversion H10;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
                 assert(n |--- B; x ++ [C]; (UP [F0]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [F0])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H17.
               apply Derivation1.
               apply seqNtoSeq in H14... LLExact H14. } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H9.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H10... LLExact H10.
               
               rewrite <- (app_nil_l [G]).
               apply UpExtension'.
                inversion H4...
                
                 assert(S n0 |--- B; (G::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (G::x) ++ N; (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus G. 
               LLExact H14.  }
            { (* first *) 
               rewrite <- H9.
               inversion H14;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H10... LLExact H10.
               
                 assert(n |--- B; x ++ [C]; (UP [G]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [G])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H17. } }
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (F0::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (F0::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0.  }
                
     {  inversion H9;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        assert( n |--- B; M ++ [C]; (UP [F0]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [F0])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (G::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (G::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus G. }
                
     {  inversion H9;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        assert( n |--- B; M ++ [C]; (UP [G]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [G])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }

  -  apply PositiveNotNegative in H. contradiction. 
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (FX t::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (FX t::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)...
        LLPerm((FX t :: M) ++ N)...
        apply Cut...
        rewrite <- app_comm_cons.
        LFocus (FX t).      }
     {  inversion H11;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        assert( n |--- B; M ++ [C]; (UP [FX t]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [FX t])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
 * rewrite allU in H0... 
 *  destruct(PositiveOrNegative F).
    2:{ inversion H5;CleanContext...
        destruct (NegativeAtomDec F).
        assert(False). 
        inversion H;subst... inversion H3. 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
        assert(n0 |--- B; M ++ [C]; (UP [F]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; M ++ N; (UP [F])) as Cut.
                         
                eapply CH with (m:=n0 + j)...
                 
                apply Cut... }
    inversion H5...
    -   eapply @AbsorptionPerp' with (A:=A)...
        inversion Hj...
        apply seqNtoSeq in H10...  
    -  apply simplUnb in H6.
       apply simplUnb in H4. clear H7.  
       checkPermutationCases H3.
          {  destruct(PositiveOrNegative F0).
             { (* first *) 
               rewrite <- H7.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'.
                inversion H2...
                
                 assert(S n0 |--- B; (F0::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (F0::x) ++ N; (UP [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0. 
               LLExact H8. 
               apply Derivation1.
               apply seqNtoSeq in H12... LLExact H12. }
            { (* first *) 
               rewrite <- H7.
               inversion H8;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
                 assert(n |--- B; x ++ [C]; (UP [F0]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [F0])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H15.
               apply Derivation1.
               apply seqNtoSeq in H12... LLExact H12. } }
          {  destruct(PositiveOrNegative G).
             { (* first *) 
               rewrite <- H7.
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H8... LLExact H8.
               
               rewrite <- (app_nil_l [G]).
               apply UpExtension'.
                inversion H2...
                
                 assert(S n0 |--- B; (G::x) ++ [C]; (UP [ ]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; (G::x) ++ N; (UP [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               LFocus G. 
               LLExact H12.  }
            { (* first *) 
               rewrite <- H7.
               inversion H12;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H8... LLExact H8.
               
                 assert(n |--- B; x ++ [C]; (UP [G]) ->
                       j |--- B; N; (UP [dual C]) ->
                         |-- B; x ++ N; (UP [G])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H15. } }
  -  destruct(PositiveOrNegative F0).   
     {  eapply @InvPlusT with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (F0::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (F0::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus F0.  }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (UP [F0]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [F0])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
  -  destruct(PositiveOrNegative G).   
     {  eapply @InvPlusTComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (G::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (G::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               LFocus G. }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (UP [G]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [G])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }

  -  apply PositiveNotNegative in H. contradiction. 
  -  destruct(PositiveOrNegative (FX t)).   
     {  eapply @InvExT with (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (FX t::M) ++ [C]; (UP [ ]) ->
                  j |--- B; N; (UP [dual C]) ->
                    |-- B; (FX t::M) ++ N; (UP [ ])) as Cut.
                eapply CH with (m:=S n0 + j)...
        LLPerm((FX t :: M) ++ N)...
        apply Cut...
        rewrite <- app_comm_cons.
        LFocus (FX t).      }
     {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: negativeFormula (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExT with (t:=t) (FX:=FX)...
        assert( n |--- B; M ++ [C]; (UP [FX t]) ->
                j |--- B; N; (UP [dual C]) ->
                 |-- B; M ++ N; (UP [FX t])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... } 
  *  assert(n |--- B; M ++ [C]; (UP (FX x :: M0)) ->
           j |--- B; N; (UP [dual C]) ->
             |-- B; M ++ N; (UP (FX x :: M0))) as Cut.
           eapply CH...
              
           apply H4 in properX...
  Qed.         
   
Theorem CutUP  i j w h C L M N B : CutH w h -> CutW w -> complexity C = S w -> S h = i + j ->
  i |--- B; M; (UP (C::L)) ->
  j |--- B; N; (DW (dual C)) ->
  |-- B; M ++ N; (UP L).
Proof with sauto;try solveLL.   
 intros CH CW compC hH Hi Hj.
 inversion Hi;subst. 
 * inversion Hj...
   CleanContext.
 * inversion Hj; CleanContext...
   apply seqNtoSeq  in H3;auto.
 * inversion Hj; CleanContext...
   apply simplUnb in H2.
   apply simplUnb in H4.
   clear H5.
   rewrite <- H2 in H9.
   rewrite <- H4 in H10.
    
   rewrite H1.
   assert( n |--- B; M; (UP (F :: G :: L)) -> 
          n0 |--- B; M0; (DW (dual F)) -> 
             |-- B; M ++ M0 ; (UP (G :: L))) as HcutF.
    eapply CW with (m:=complexity F)...
    inversion compC...
    apply HcutF in H9;auto.
    apply seqtoSeqN in H9.
    destruct H9.
    
    assert( x |--- B; M ++ M0; (UP (G :: L)) -> 
           n0 |--- B; N0; (DW (dual G )) -> 
              |-- B; (M ++ M0) ++ N0; UP L) as HcutG.
      eapply CW with (m:=complexity G)...
       
      inversion compC...
      LLPerm((M ++ M0) ++ N0)...
 * inversion Hj; CleanContext...
   assert( n |--- B; M; (UP (F :: L)) -> 
          n0 |--- B; N; (DW (dual F )) -> 
             |-- B; M ++ N; (UP L)) as HcutF.
    eapply CW with (m:=complexity F)...
     
    inversion compC...
    apply  HcutF ... 
  assert( n |--- B; M; (UP (G :: L)) -> 
          n0 |--- B; N; (DW (dual G )) -> 
             |-- B; M ++ N; (UP L)) as HcutG.
    eapply CW with (m:=complexity G)...
     
    inversion compC...
    apply  HcutG...
 * assert(N=[]).
 simpl in Hj.
   inversion Hj;solveF... 
   subst.
    assert( n |--- B ++ [(i0,F)]; M ; (UP L) -> 
           j |--- B; []; (DW (Bang i0 (dual F))) -> 
             |-- B; M ; (UP L)) as UCCut.
    eapply CH with (m:=h) (C:=Quest i0 F) (dualC:=Bang i0 (dual F));eauto.
    rewrite app_nil_r...
    apply UCCut... LLExact H3.
 *  apply NotAsynchronousPosAtoms in H4...
   apply PositiveDualNegative in H.
     inversion Hj;subst; try match goal with
       [ H: _= dual ?C , H2: negativeFormula (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
    assert( n |--- B; M ++ [C]; (UP L) -> 
            n0 |--- B; N; (UP [dual C]) -> 
             |-- B; M ++ N; (UP L)) as ULCut.
   eapply CH with (m:=n+n0)... 
   apply ULCut...
   LLExact H5.
   inversion H...
   inversion Hj...
   apply seqNtoSeq in H5. LLExact H5. 
   rewrite <- H7.
   assert(n |--- (i, atom A) :: C; M; (UP L)).
   eapply AbsorptionC... 
    LLExact H5.
   apply seqNtoSeq in H0.
   LLExact H0.
   inversion H1.
  * inversion Hj;CleanContext...
   assert( n  |--- B; M; (UP (FX t :: L)) -> 
           n0 |--- B; N; (DW (dual (FX t))) -> 
              |-- B; M++N; (UP L)) as HCut.
   eapply CW with (m:=complexity (FX (VAR con 0%nat)));eauto...
   
   inversion compC...
   inversion compC...
    remember (VAR con 0%nat).
            assert(proper e).
            rewrite Heqe.  
            constructor.
            eapply ComplexityUniformEq...
            
            apply HCut... 
 Qed.
      
Theorem CutK4SubCase (h n j w:nat) i a L B P: CutH w h -> CutW w -> complexity P = w -> S h = S n + j -> i <> loc ->
 tri_bangK4 theory n (B ++ [(a, P)]) i [] [] (UP L) -> 
 j |--- B; []; (DW (Bang a (dual P))) -> tri_bangK4' theory B i [] [] (UP L).
 Proof with sauto;solveF.
 intros HC WC comP hH Hd Hyp Hj.
        apply InvSubExpPhaseU in Hyp;auto.
         
        destruct Hyp as [C4 Hyp];
        destruct Hyp as [CK Hyp];
        destruct Hyp as [CN Hyp].
        CleanContext.
        checkPermutationCases H. 
        { (* P in C4 *)
         rewrite <- Permutation_cons_append in H8. 
         inversion Hj...
         
         { rewrite H8 in H1...
          assert(False).
          inversion H1...
          solveSignature1.
             contradiction. }
           assert(lt i a /\ m4 a = true /\ SetK4 x /\ LtX i x).
          { rewrite H8 in H1. rewrite H8 in H2.
            inversion H1;inversion H2...  } 
          CleanContext.
         finishExponential.    
       
          assert( LtX i CK4).
          { eapply @SetKTrans with (i:=a)... }
          rewrite H in H10.
          change (CK4 ++ CN0) with (CK4 ++ [] ++ CN0) in H10.
          eapply @destructClassicSet' in H10;auto.
          destruct H10 as [K_1 H10].
          destruct H10 as [K_2 H10].
          destruct H10 as [K_3 H10].
          destruct H10 as [K4_1 H10].
          destruct H10 as [K4_2 H10].
          destruct H10 as [K4_3 H10].
          
          destruct H10 as [N H10].
          simpl in *.         
          CleanContext.
          CleanContext.
          
          assert(Hd': S n0 |--- PlusT CK4; []; (DW (Bang (plust a) (dual P)))).
          { apply BangPlusT...  }
          rewrite H.
          rewrite H25.
          rewrite H28.
            eapply @GenK4RelU' with (C4:=CK4++K4_2) (CK:=CK) (CN:=N)...
          apply Forall_app...
          rewrite H23 in H12...
          apply Forall_app in H12...
          apply Forall_app...
          rewrite H23 in H17...
          apply Forall_app in H17...
          rewrite H25. rewrite H21...
          simplEmpty...
          simplCtx...
  assert(Hp: 
 (n - length (C4 ++ CK) - 1) |--- (PlusT CK4 ++ PlusT K4_2 ++ Loc CK) ++ [(plust a,P)]; []; (UP L) ->
   S n0 |--- PlusT CK4 ++ PlusT K4_2 ++ Loc CK; []; (DW (Bang (plust a) (dual P ))) -> 
   |-- PlusT CK4 ++ PlusT K4_2 ++ Loc CK; []; (UP L)).
         
   eapply HC with  (m:=n - length (C4 ++ CK) - 1 + S n0) (C:=Quest (plust a) P) (dualC:=Bang (plust a) (dual P))...
  simpl... 
  
   rewrite app_assoc_reverse...
   apply Hp... all:clear Hp.
   rewrite H25.
   simplCtx...
   repeat rewrite app_assoc_reverse...
   rewrite Permutation_midle_app.
   apply weakeningGenN...
   rewrite app_assoc.
   LLExact H9.
   rewrite <- PlusTApp.
   rewrite <- H23.
   rewrite H8...
   apply weakeningGenN_rev...   }
     checkPermutationCases H8. 
          {
           (* P in CK *)
        rewrite <- Permutation_cons_append in H8.
        inversion Hj...
          { rewrite H8 in H3. 
             assert(False).
            apply locAlone in Hd.
            apply Hd... 
            inversion H3... contradiction. }
        
          apply InvSubExpPhaseU in H16;auto.  
          
          destruct H16 as [C4' H16].
          destruct H16 as [CK' H16].
          destruct H16 as [CN' H16]...
             assert(lt i a /\ m4 a = false /\ SetK x0 /\ LtX i x0).
          { rewrite H8 in H0;rewrite H8 in H3.
            inversion H0;inversion H3... 
            } CleanContext.
          assert(LtX i C4').
          { eapply @SetKTrans with (i:=a)... }
          assert(LtX i CK').
          { eapply @SetKTrans with (i:=a)... }
          
          rewrite <- H11 in H10.
          rewrite H in H10.
          CleanContext.
          eapply @destructClassicSet' in H10;auto.
          destruct H10 as [K_1 H10].
          destruct H10 as [K_2 H10].
          destruct H10 as [K_3 H10].
          destruct H10 as [K4_1 H10].
          destruct H10 as [K4_2 H10].
          destruct H10 as [K4_3 H10].
          
          destruct H10 as [N H10].
          simpl in *.         
          CleanContext.
           
           assert(Hd': S n0 |--- PlusT C4' ++ Loc CK'; []; (DW (Bang loc (dual P)))).
          { apply tri_bangL...
            eapply HeightGeqCEx.
            2:{ exact H23. }
            perm.
            lia.
          }
        
       rewrite H. 
      eapply @GenK4RelU' with (C4:=C4'++K4_2) (CK:=x0++K_3) (CN:=N)...
          apply Forall_app...
          rewrite H29 in H1...
          apply Forall_app in H1...
          apply Forall_app...
          rewrite H30 in H12...
          apply Forall_app in H12...
          apply Forall_app...
          rewrite H29 in H2...
          apply Forall_app in H2...
          apply Forall_app...
          rewrite H30 in H26...
          apply Forall_app in H26...
          rewrite H30. rewrite H34...
          rewrite H28...
       
       assert(Hp: 
 (n - length (C4 ++ CK) - 1) |--- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3) ++ [(loc,P)]; []; (UP L) ->
   S n0 |--- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3); []; (DW (Bang loc  (dual P ))) -> 
   |-- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3); []; (UP L)).
         
   eapply HC with  (m:=n - length (C4 ++ CK) - 1 + S n0) (C:=Quest loc P) (dualC:=Bang loc (dual P))...
   CleanContext. 
   repeat simplCtx...
   rewrite locApp...
   rewrite app_assoc_reverse.
   apply Hp... all:clear Hp.
   LLPerm(Loc K_3++(PlusT C4' ++ PlusT K4_2 ++ Loc x0) ++ [(loc, P)]).
   apply weakeningGenN...
   
   rewrite H31.
   simplCtx... 
   repeat rewrite app_assoc_reverse.
   
   rewrite Permutation_midle_app.
   apply weakeningGenN...
   rewrite app_assoc.
   rewrite <- PlusTApp.
   LLExact H9.
   rewrite  H29.
   rewrite H8...
   LLPerm (PlusT K4_2 ++ Loc x0 ++ PlusT C4' ++ Loc K_3).
   apply weakeningGenN...
   rewrite H28.
   rewrite locApp.
    rewrite app_assoc_reverse.
   rewrite Permutation_midle_app.
   apply weakeningGenN...
   LLExact Hd'.
   rewrite H31... rewrite H30... rewrite locApp...  }
  {
        eapply @GenK4RelU' with (C4:=C4) (CK:=CK) (CN:= x0)...
        rewrite <- H10.
        rewrite <- H11...
        HProof.
         } 
 Qed.       

Theorem CutDwC a j n w h P F L B:
    CutH w h -> CutW w -> S h = n + j -> complexity P = w ->
    j |--- B; []; (DW (Bang a (dual P ))) -> 
    n |--- B ++ [(a,P)]; L; (DW F) -> 
    |-- B; L; (UP [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc Hj Hn.
    inversion Hn...
    * solveLL.
    * checkPermutationCases H5.
      { LLStore. LFocus (perp A). init2 i x. } 
      { inversion H2...
        simpl in Hj.
        apply (InvBangT H1 Hj). } 
     * solveLL.
   * apply simplUnb in H1.
     apply simplUnb in H2.
     clear H3.
     rewrite <- H1 in H4.
     rewrite <- H2 in H8.  
     clear H1 H2.
      assert(CutF: n0 |--- B ++ [(a, P)]; M; (DW F0) ->
             j |--- B; []; (DW (Bang a (dual P ))) ->
             |-- B; M; (UP [F0])).
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P)) (C:=Quest a P)...
      
      assert(CutG: n0 |--- B ++ [(a, P)]; N; (DW G) ->
             j |--- B; []; (DW (Bang a (dual P ))) ->
             |-- B ; N; (UP [G])).
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)...
      LLStore. rewrite H0.
      rewrite <- (app_nil_l []).  
        eapply @InvTensor with (B:=B) (D:=B)...
    *   assert(n0 |--- B ++ [(a, P)]; L; (DW F0) ->
             j |--- B; []; (DW  (Bang a (dual P ))) ->
             |-- B ; L; (UP [F0])).
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)...
        LLStore. 
        apply InvPlus...
    *   assert(n0 |--- B ++ [(a, P)]; L; (DW G) ->
             j |--- B; []; (DW  (Bang a (dual P ))) ->
             |-- B ; L; (UP [G])).
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)... LLStore. 
        apply InvPlusComm...
    *   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (UP [F]) ->
             j |--- B; []; (DW  (Bang a (dual P ))) -> 
               |-- B; L; (UP [F])).
                                       
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)...
        apply Hc...
   *    
   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (DW (FX t)) ->
             j |--- B; []; (DW  (Bang a (dual P ))) -> 
               |-- B; L; (UP [FX t])).
                                       
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)...
       LLStore.
        eapply InvEx with (t:=t)...
    *   
        assert(Hc:
            n0 |--- B ++ [(a,P)]; []; (UP [F0]) ->
             j |--- B; []; (DW  (Bang a (dual P ))) -> 
               |-- B; []; (UP [F0])).
         
        eapply HC with (m:=n0 + j) (dualC:=Bang a (dual P )) (C:=Quest a P)...
        exact nil.
        LLStore.
        LFocus (Bang loc F0). 
    *  LLStore. LFocus (Bang i F0).
       createWorld.
       eapply @CutK4SubCase with (n:=n0) (j:=j) (h:=h) (P:=P) (a:=a) (w:=complexity P) (B:=B)... 
       
  Qed. 

 
 Theorem CutUPC  i j w h a A L M B  : CutH w h -> CutW w -> complexity A = w -> S h = i + j ->
  i |--- B++[(a,A)]; M; (UP L) ->
  j |--- B; []; (DW (Bang a (dual A ))) ->
  |-- B; M; (UP L).
Proof with sauto;try solveLL.  
  intros CH CW compA hH Hi Hj.
  inversion Hi...  
  --  assert( n |--- B ++ [(a,A)]; M; (UP M0) ->
              j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B; M; (UP M0)) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))... 
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (UP (F :: G :: M0)) ->
              j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B; M; (UP (F :: G ::M0))) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))...  
              apply Cut...
  --  assert( n |--- B ++ [(a,A)]; M; (UP (F :: M0)) ->
              j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B; M; (UP (F :: M0))) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))...  
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (UP (G :: M0)) ->
              j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B; M; (UP (G ::M0))) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))...  
              apply Cut...
  --  assert( n |--- (B ++ [(i0, F)]) ++ [(a,A)]; M; (UP M0) ->
              j |--- B ++ [(i0, F)]; []; (DW  (Bang a (dual A ))) -> |-- B ++ [(i0, F)]; M; (UP M0)) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))...  
              LLPerm(B  ++ [(i0, F)])...
              apply Cut...
              LLExact H3.
              apply weakeningGenN_rev...
  --  assert( n |--- B ++ [(a,A)]; F::M ; (UP M0) ->
              j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B ; F::M; (UP M0)) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))...               
              apply Cut...
  -- assert( n |--- B ++ [(a,A)]; L'; (DW F) ->
             j |--- B; []; (DW (Bang a (dual A ))) -> |-- B ; L'; (UP [F])) as Cut.
     eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))... 
     assert( |-- B ; L'; (UP [F])).
     apply Cut... 
     rewrite <- H1.
     inversion H;solveF...
  --  apply in_app_or in H3...
      +   assert( n |--- B ++ [(a,A)]; M; (DW F) ->
          j |--- B; []; (DW  (Bang a (dual A ))) -> |-- B ; M; (UP [F])) as Cut.
          eapply CH with  (C:=Quest a A ) (dualC:=Bang a (dual A))... 
          eapply @AbsorptionClassic with (i:=i0) (F:=F)...
      + inversion H...
        assert( n |--- B ++ [(i0,F)]; M; (DW F) ->
          j |--- B; []; (DW  (Bang i0 (dual F ))) -> |-- B ; M; (UP [F])) as Cut.
          eapply CH with (C:=Quest i0 F ) (dualC:=Bang i0 (dual F))... 
          assert(Hs: |-- B; M; (UP [F]))...
          clear Cut.
          apply seqtoSeqN in Hs.
          destruct Hs as [x Hs].
          apply InvBangT in Hj...
         apply seqtoSeqN in Hj.
          destruct Hj as [y Hj].
           
            destruct(PositiveOrNegative F).
            assert(negativeFormula (F ^)).
            apply PositiveDualNegative...
             
            assert( x |--- B; M ; (UP [F]) -> 
                    S y |--- B; []; (DW (dual F)) ->
                      |-- B; M++[] ; UP [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            CleanContext. 
           
            assert( y |--- B; [] ; (UP [dual F]) -> 
                  S x |--- B; M; (DW F) ->
                      |-- B; []++M ; UP [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            rewrite <- ng_involutive...
            CleanContext.
   -- rewrite allU in H0...
   -- assert(n |--- B ++ [(a, A)]; M; (DW F) ->
                    j |--- B; []; (DW (Bang a (dual A ))) -> 
                      |-- B; M ; UP [F]) as Cut.
            eapply CH with  (C:=Quest a A ) (dualC:=Bang a (dual A))...  
           assert(Hs:|--B; M; (UP [F])).
           apply Cut... 
             destruct (NegativeAtomDec F).
              2:{  eapply @AbsorptionTheory with (F:=F)... }
             
             inversion H...
             eapply @AbsorptionPerp' with (A:=A0)...
  --  assert( n |--- B ++ [(a,A)]; M; (UP (FX x ::  M0)) ->
              j |--- B; []; (DW (Bang a (dual A ))) -> |-- B ; M; (UP (FX x :: M0))) as Cut.
              eapply CH with (C:=Quest a A ) (dualC:=Bang a (dual A))... 
              apply Cut...
  -- createWorld i0.
   eapply @CutK4SubCase with (n:=n) (j:=j) (h:=h) (P:=A) (a:=a) (w:=complexity A) (B:=B)...
   solveSignature1.
  Qed.
  
 
  Theorem CutElimination i j a C dualC A dualA B L M N P: 
    dualC = dual C -> 
      (i |--- B; M ++ [C]; (UP L) -> j |--- B; N; (UP [dualC]) -> |-- B; M ++ N; (UP L)) /\
      (i |--- B; M; (UP (C :: L)) -> j |--- B; N; (DW dualC) -> |-- B; M ++ N; (UP L)) /\
       (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (DW P) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP [P]))  /\
      (dualA = A ^ ->
       dualC = Bang a dualA ->
       i |--- B ++ [(a,A)] ; M; (UP L) -> j |--- B; []; (DW (Bang a dualA)) -> |-- B; M; (UP L)).
  Proof with sauto;solveF;try solveLL.
    assert(exists w, complexity C = w).
    eexists; auto.
    destruct H as [w H].
    revert H.
    revert a i j C dualC A dualA P B L M N.
    
    
    induction w using strongind;intros.
    - assert(complexity C > 0) by apply Complexity0.
      rewrite H in H1. inversion H1.
    - remember (plus i j) as h.
      revert dependent B.
      revert dependent L.
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
        
        move B at top.
        move M at top.
        move N at top.
        move L at top.
        move C at top.
        move A at top.
        move dualC at top.
        move dualA at top.
        move P at top.
        subst.
        split;[intros 
              |split;[intros
              |split;intros]].
       *  eapply (@CutUPLStar i j w h C L M N B)...
          unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
        * eapply (@CutUP i j w h C L M N B)...     
           unfold CutElimination.CutH; intros.
           eapply CutH with (m:=m)... 
           unfold CutElimination.CutW; intros.
           eapply CutW with (m:=m)...
        * eapply (@CutDwC a j i w h A P M B)...  
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
           unfold CutElimination.CutW; intros.
          eapply CutW with (m:=m)...
          rewrite DualComplexity in compC...
              rewrite H0 in compC...
              inversion compC...
        * eapply (@CutUPC i j w h a A L M B)... 
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
           unfold CutElimination.CutW; intros.
          eapply CutW with (m:=m)...
         rewrite DualComplexity in compC...
              rewrite H0 in compC...
              inversion compC...
 Qed.              
     
  Theorem GeneralCut i j C B L M N: 
    (i |--- B; M ; UP (C::L) -> 
                   j |--- B; N ; DW (dual C) -> 
                                 |-- B; M++N ; UP L).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity C = w). 
    eexists; auto.
    destruct H1 as [w H1].
    specialize CutElimination;intros.
    assert((i |--- B; M ; UP (C::L) -> 
                          j |--- B; N ; DW (dual C) -> 
                                        |-- B; M++N ; UP L)) as CUT.
    eapply H2;eauto.
    
    clear H2.
    apply CUT;auto.  
  Qed. 
  
  Theorem GeneralCutClassic i j a A B L M: 
    (i |--- B ++ [(a,A)] ; M; (UP L) -> 
            j |--- B; []; (DW (Bang a (dual A))) -> 
                  |-- B; M; (UP L)).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity A = w). 
    eexists; auto.
    destruct H1 as [w H1].
    specialize CutElimination;intros.
    assert((i |--- B ++ [(a,A)]; M ; UP L -> 
                          j |--- B; [] ; DW (Bang a (dual A)) -> 
                                        |-- B; M ; UP L)) as CUT.
    eapply H2 with (C:=Quest a A) ;eauto.
    clear H2.
    apply CUT;auto.  
  Qed. 
  
    Theorem GeneralCutClassic' a A B L M: 
    (|-- B ++ [(a,A)] ; M; (UP L) -> |-- B; []; (DW (Bang a (dual A))) -> |-- B; M; (UP L)).
  Proof with subst;auto.
    intros. 
    apply seqtoSeqN in H0.
    apply seqtoSeqN in H.
    CleanContext.
    eapply GeneralCutClassic;eauto. 
  Qed.
   
  Theorem GeneralCut' C B L M N: 
    (|-- B; M ; UP (C::L) -> 
                   |-- B; N ; DW (dual C) -> 
                                 |-- B; M++N ; UP L).
  Proof with subst;auto.
    intros.
    apply seqtoSeqN in H0.
    apply seqtoSeqN in H.
    CleanContext.
    eapply GeneralCut;eauto.
  Qed.

End CutElimination.
