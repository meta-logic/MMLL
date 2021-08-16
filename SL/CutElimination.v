(** Cut Elimination for MMLL

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

Class UnbSignature `{Signature}:=
  { 
    allU: forall x, u x = true; }.

Section CutElimination.
Context `{OLS: OLSig}.
Context `{SI : Signature}.
Context {USI : UnbSignature}.

Lemma allSeTU B : SetU B.
Proof with auto.
 induction B...
 apply ForallCons...
 apply allU.
Qed.
Local Hint Resolve allSeTU : core. 

Lemma allSeTLEmpty (B : list TypedFormula) : getL B = (@nil TypedFormula).
Proof with auto.
 rewrite (SetU_then_empty (allSeTU B));auto.
Qed.

Lemma permSeTL (B : list TypedFormula) : Permutation (getL B) (getL B ++ getL B).
Proof with auto.
 rewrite allSeTLEmpty...
Qed.
Local Hint Resolve permSeTL : core. 

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
  do 2 rewrite allSeTLEmpty;auto.
  Qed.
      

 Lemma InvBangTN i j B P : mt i = true ->
           j |--- B; []; (>> i ! P) -> (j-1) |--- B; []; (> [P]).
  Proof with sauto.
  intros Hm Hj.
  inversion Hj...
  inversion H0.
  eapply InvSubExpPhaseU in H4;auto. 
  destruct H4 as [C4 H4].
  destruct H4 as [CK H4].
  destruct H4 as [CN H4]...
  rewrite H.
  rewrite app_assoc. 
  apply weakeningGenN_rev;auto.
  rewrite setUtoGetU in H9;auto.
  rewrite setUtoGetU in H9;auto.
  apply ContractionL...
  eapply (SetTKClosure Hm)...
  rewrite SetTPlusT in H9.
  LLPerm ((C4 ++ Loc CK) ++ CK).
  apply weakeningGenN_rev;auto.
  eapply @HeightGeq with (n:=n - length (C4 ++ CK) - 1)...
  lia.
   eapply (SetTK4Closure Hm)...
   apply allU. 
 Qed. 
 
  Lemma InvBangT i j B P : mt i = true ->
           j |--- B; []; (>> i ! P) -> |-- B; []; (> [P]).
  Proof with sauto.
  intros Hm Hj.
  apply InvBangTN in Hj...
  apply seqNtoSeq in Hj...
 Qed. 
  
   
Lemma BangPlusT n C P a : a <> loc -> SetK4 a C -> n >= length C + 1 -> 
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

  Theorem CutElimBase a C dualC A dualA B L M N P: 
    dualC = dual C ->
      (0 |--- B; M ++ [C]; (> L) -> 0 |--- B; N; (> [dualC]) -> |-- B; M ++ N; (> L)) /\
      (0 |--- B; M; (> C :: L) -> 0 |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       0 |--- B ++ [(a,A)] ; M; (>> P) -> 0 |--- B; []; (>> a ! dualA) -> |-- B; M; (> [P]))  /\
     (dualA = A ^ ->
       dualC = a ! dualA ->
       0 |--- B ++ [(a,A)] ; M; (> L) -> 0 |--- B; []; (>> a ! dualA) -> |-- B; M; (> L)). 
    
  Proof with sauto;solveLL.
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
      (i |--- B; M ++ [C]; (> L) -> j |--- B; N; (> [dualC]) -> |-- B; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
       (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> L)). 
    
  Definition CutH (w h: nat) :=  
    forall a m i j C dualC A dualA P M N L B, 
    m <= h ->
    m = i + j ->
    dualC = C ^ ->
    complexity C = S w ->
      (i |--- B; M ++ [C]; (> L) -> j |--- B; N; (> [dualC]) -> |-- B; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> [P]))   /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> L)). 
       
Theorem CutUPLStar  i j w h C L M N B : CutH w h -> complexity C = S w -> S h = i + j ->
  i |--- B; M ++ [C]; (> L) ->
  j |--- B; N; (> [C ^]) ->
  |-- B; M ++ N; (> L ).
Proof with sauto;solveLL.  
 intros CH compC hH Hi Hj.
 inversion Hi...
 * assert(n |--- B; M ++ [C]; (> M0) ->
          j |--- B; N; (> [dual C]) ->
            |-- B; M ++ N; (> M0)) as Cut.
           eapply CH...
                    
           apply Cut...
 * assert(n |--- B; M ++ [C]; (> F :: G :: M0) ->
          j |--- B; N; (> [dual C]) ->
            |-- B; M ++ N; (> F :: G :: M0)) as Cut.
           eapply CH...
                    
           apply Cut...                                       
 * assert(n |--- B; M ++ [C]; (> F  :: M0) ->
          j |--- B; N; (> [dual C]) ->
            |-- B; M ++ N; (> F :: M0)) as CutF.
           eapply CH...
                    
           apply CutF...             

 * assert(n |--- B; M ++ [C]; (> G  :: M0) ->
          j |--- B; N; (> [dual C]) ->
            |-- B; M ++ N; (> G :: M0)) as CutG.
           eapply CH...
                    
           apply CutG...             

 * assert(n |--- B ++ [(i0, F)]; M ++ [C]; (> M0) ->
            j |--- B ++ [(i0, F)]; N; (> [dual C]) ->
              |-- B ++ [(i0, F)]; M ++ N; (> M0)) as Cut.
           eapply CH...
           rewrite Permutation_cons_append.         
           apply Cut...
           LLExact H3.
           apply weakeningGenN_rev...
 * assert(n |--- B; (M ++ [F]) ++ [C]; (> M0) ->
          j |--- B; N; (> [dual C]) ->
            |-- B; (M ++ [F]) ++ N; (> M0)) as Cut.
           eapply CH...
                    
           LLPerm((M ++ [F]) ++ N).
           apply Cut...
           LLExact H4.
 * apply Remove_Permute in H1...
   checkPermutationCases H1.
   2:{ inversion H1...
       rewrite H2.
       assert(j |--- B; N; (> [dual C]) ->
              n |--- B; L'; (>> C) ->
                |-- B; N++L'; (> [])) as Cut.
       eapply CH with (m:=n + j)...
        
       lia.
       rewrite <- ng_involutive...
       rewrite DualComplexity in compC...
       LLPerm(N ++ L')... }
       
   destruct(PositiveOrRelease F).
   2:{ inversion H5;CleanContext... 
       rewrite H1.
       rewrite <- app_comm_cons.
       LLPerm((x++N)++[F]). 
       eapply UpExtensionInv'... 
        assert(S n0 |--- B; x++ [C]; (> [F]) ->
               j |--- B; N; (> [dual C]) ->
                 |-- B; x ++ N; (> [F])) as Cut.
                eapply CH with (m:=S n0 + j)...
                apply Cut... 
                rewrite <- H2 in H9.
                LLExact H9. }
       inversion H5...
            { 
              inversion Hj...
              apply seqNtoSeq in H9... } 
            {  apply simplUnb in H7.
               apply simplUnb in H6.
               clear H8.
              rewrite H4 in H2.
              checkPermutationCases H2.
              - 
              destruct(PositiveOrRelease F0).
              { (* first *) 
              assert(S n0 |--- B; (F0::x0)++[C]; (> [])).
              decide1 F0...
              inversion H2...  
              rewrite <- H3... LLExact H9.
              rewrite H1.
              rewrite <- app_comm_cons.
              rewrite Permutation_cons_append.
              apply TensorComm'.
              rewrite <- H8.
              LLPerm(G**F0::N0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
              
              apply Derivation1.
              apply seqNtoSeq in H13...
              LLExact H13.
              assert(S n0 |--- B; (F0::x0) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (F0::x0) ++ N; (> [ ])) as Cut.
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
              rewrite Permutation_cons_append.
              apply TensorComm'.
              rewrite <- H8.
              LLPerm(G**F0::N0++(x0++N)).
                rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
                apply Derivation1.
                apply seqNtoSeq in H13... LLExact H13.
                 assert(n |--- B; x0 ++ [C]; (> [F0]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x0 ++ N; (> [F0])) as Cut.
                eapply CH with (m:=n + j)... 
                inversion H9...
                apply Cut...
                LLExact H15. } 
             - 
              destruct(PositiveOrRelease G).
              { (* first *) 
              assert(S n0 |--- B; (G::x0)++[C]; (> [])).
              decide1 G...
              inversion H2... LLExact H13.  
              rewrite H1.
              rewrite <- H8.
              LLPerm(F0**G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
              apply Derivation1.
              apply seqNtoSeq in H9...    LLExact H9.
           
              assert(S n0 |--- B; (G::x0) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (G::x0) ++ N; (> [ ])) as Cut.
                eapply CH...
                  rewrite <- (app_nil_l [G]).
               
               apply UpExtension'.
               inversion H2...
               
               LLPerm((G :: x0) ++ N)... }
             { (* second *) 
              inversion H13;CleanContext...
              rewrite H1.
              rewrite <- H8.
              LLPerm(F0**G::M0++(x0++N)).
              rewrite <- (app_nil_l [ ]).
              eapply @InvTensor with (B:=B) (D:=B)...
                apply Derivation1.
                apply seqNtoSeq in H9... LLExact H9.
              assert(n |--- B; x0++ [C]; (> [G ]) ->
                          j |--- B; N; (> [dual C]) ->
                         |-- B; x0 ++ N; (> [G])) as Cut.
                 eapply CH with (m:=n + j)... 
                
                inversion H13...
                apply Cut... LLExact H15. }   
                }
    -   destruct(PositiveOrRelease F0).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                 store. inversion H3...
                assert((S n0) |--- B; (F0::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (F0::x) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 decide1 F0. inversion H3...
               LLExact H8. }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlus...
                assert(n |--- B; x ++ [C]; (> [F0]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [F0])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H11. 
               } 
  -    destruct(PositiveOrRelease G).   
       {         rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                  store. inversion H3...
                
                assert((S n0) |--- B; (G::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (G::x ) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 decide1 G. inversion H3...
               LLExact H8. }
             {   inversion H8;CleanContext...  
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply InvPlusComm...
                assert(n |--- B; x ++ [C]; (> [G]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [G])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H11. 
               }
   -  apply PositiveNotRelease in H. contradiction. 
   -   destruct(PositiveOrRelease (FX t)).   
       { rewrite H1. 
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                 store. inversion H3...
                assert((S n0) |--- B; (FX t::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (FX t::x) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=(S n0) + j)...
                rewrite app_comm_cons...
                apply Cut...
                 rewrite <- app_comm_cons...
                 decide1 (FX t). inversion H3...
               LLExact H10. }
             {   inversion H10;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end. 
                 rewrite H1.
                 rewrite <- app_comm_cons. 
                 apply @InvEx with (t:=t)...
                assert(n |--- B; x ++ [C]; (> [FX t]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [FX t])) as Cut.
                eapply CH with (m:= n + j)...
               apply Cut... LLExact H13. }
*  destruct(PositiveOrRelease F).
   2:{ inversion H7;CleanContext...
       apply @AbsorptionClassic' with (i:=i0) (F:=F)...
        assert(n0 |--- B; M ++ [C]; (> [F]) ->
                j |--- B; N; (> [dual C]) ->
                  |-- B; M ++ N; (> [F])) as Cut.
       eapply CH with (m:=n0 + j)... 
       apply Cut... } 
       inversion H7...
       -  apply @AbsorptionClassic' with (i:=i0) (F:=perp A)...
          inversion Hj...
          apply seqNtoSeq in H12...  
       - apply simplUnb in H6.
         apply simplUnb in H8. clear H9.  
         checkPermutationCases H5.
          {  destruct(PositiveOrRelease F0).
             { (* first *) 
               rewrite <- H9.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'.
                inversion H4...
                
                 assert(S n0 |--- B; (F0::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (F0::x) ++ N; (> [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               decide1 F0. inversion H4...
               LLExact H10. 
               apply Derivation1.
               apply seqNtoSeq in H14... LLExact H14. }
            { (* first *) 
               rewrite <- H9.
               inversion H10;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
                 assert(n |--- B; x ++ [C]; (> [F0]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [F0])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H17.
               apply Derivation1.
               apply seqNtoSeq in H14... LLExact H14. } }
          {  destruct(PositiveOrRelease G).
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
                
                 assert(S n0 |--- B; (G::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (G::x) ++ N; (> [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               decide1 G. inversion H4...
               LLExact H14.  }
            { (* first *) 
               rewrite <- H9.
               inversion H14;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorC with (F:=F0) (G:=G) (i:=i0) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H10... LLExact H10.
               
                 assert(n |--- B; x ++ [C]; (> [G]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [G])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H17. } }
  -  destruct(PositiveOrRelease F0).   
     {  eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (F0::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (F0::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               decide1 F0. inversion H4... }
                
     {  inversion H9;CleanContext...               
        eapply @InvPlusC with (F:=F0) (G:=G) (i:=i0)...
        assert( n |--- B; M ++ [C]; (> [F0]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [F0])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
  -  destruct(PositiveOrRelease G).   
     {  eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (G::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (G::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               decide1 G. inversion H4... }
                
     {  inversion H9;CleanContext...               
        eapply @InvPlusCComm with (F:=F0) (G:=G) (i:=i0)...
        assert( n |--- B; M ++ [C]; (> [G]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [G])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }

  -  apply PositiveNotRelease in H. contradiction. 
  -  destruct(PositiveOrRelease (FX t)).   
     {  eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'.
        inversion H4... 
        assert(S n0 |--- B; (FX t::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (FX t::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)...
        LLPerm((FX t :: M) ++ N)...
        apply Cut...
        rewrite <- app_comm_cons.
        decide1 (FX t). inversion H4...       }
     {  inversion H11;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExC with  (i:=i0) (t:=t) (FX:=FX)...
        assert( n |--- B; M ++ [C]; (> [FX t]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [FX t])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
 * rewrite allU in H0... 
 *  destruct(PositiveOrRelease F).
    2:{ inversion H5;CleanContext...
        destruct (NegativeAtomDec F).
        assert(False). 
        inversion H;subst... 
        contradiction.
        apply @AbsorptionTheory with (F:=F)...
        assert(n0 |--- B; M ++ [C]; (> [F]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; M ++ N; (> [F])) as Cut.
                         
                eapply CH with (m:=n0 + j)...
                 
                apply Cut... }
    inversion H5...
    -   eapply @AbsorptionPerp' with (A:=A)...
        inversion Hj...
        apply seqNtoSeq in H10...  
    -  apply simplUnb in H6.
       apply simplUnb in H4. clear H7.  
       checkPermutationCases H3.
          {  destruct(PositiveOrRelease F0).
             { (* first *) 
               rewrite <- H7.
               LLPerm((x ++ N) ++ N0).
               rewrite <- (app_nil_r []).
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
               rewrite <- (app_nil_l [F0]).
               apply UpExtension'.
                inversion H2...
                
                 assert(S n0 |--- B; (F0::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (F0::x) ++ N; (> [ ])) as Cut.
                eapply CH...
               LLPerm((F0 :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               decide1 F0. inversion H2...
               LLExact H8. 
               apply Derivation1.
               apply seqNtoSeq in H12... LLExact H12. }
            { (* first *) 
               rewrite <- H7.
               inversion H8;CleanContext...
               LLPerm((x++N)++N0).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
                 assert(n |--- B; x ++ [C]; (> [F0]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [F0])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H15.
               apply Derivation1.
               apply seqNtoSeq in H12... LLExact H12. } }
          {  destruct(PositiveOrRelease G).
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
                
                 assert(S n0 |--- B; (G::x) ++ [C]; (> [ ]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; (G::x) ++ N; (> [ ])) as Cut.
                eapply CH...
               LLPerm((G :: x) ++ N)... apply Cut...
               rewrite <- app_comm_cons.
               decide1 G. inversion H2...
               LLExact H12.  }
            { (* first *) 
               rewrite <- H7.
               inversion H12;CleanContext...
               LLPerm(M0++(x ++ N)).
               rewrite <- (app_nil_r []).
               
               eapply @InvTensorT with (F:=F0) (G:=G) (B:=B) (D:=B)...
               apply Derivation1.
               apply seqNtoSeq in H8... LLExact H8.
               
                 assert(n |--- B; x ++ [C]; (> [G]) ->
                       j |--- B; N; (> [dual C]) ->
                         |-- B; x ++ N; (> [G])) as Cut.
                eapply CH with (m:=n+j)...
                apply Cut...
                LLExact H15. } }
  -  destruct(PositiveOrRelease F0).   
     {  eapply @InvPlusT with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [F0]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (F0::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (F0::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (F0::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               decide1 F0. inversion H2... }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusT with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (> [F0]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [F0])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }
  -  destruct(PositiveOrRelease G).   
     {  eapply @InvPlusTComm with (F:=F0) (G:=G)...
        rewrite <- (app_nil_l [G]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (G::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (G::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)... 
               LLPerm( (G::M) ++ N)...
               apply Cut...
               rewrite <- app_comm_cons.
               decide1 G. inversion H2... }
                
     {  inversion H7;CleanContext...               
        eapply @InvPlusTComm with (F:=F0) (G:=G)...
        assert( n |--- B; M ++ [C]; (> [G]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [G])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... }

  -  apply PositiveNotRelease in H. contradiction. 
  -  destruct(PositiveOrRelease (FX t)).   
     {  eapply @InvExT with (t:=t) (FX:=FX)...
        rewrite <- (app_nil_l [FX t]).
        apply UpExtension'.
        inversion H2... 
        assert(S n0 |--- B; (FX t::M) ++ [C]; (> [ ]) ->
                  j |--- B; N; (> [dual C]) ->
                    |-- B; (FX t::M) ++ N; (> [ ])) as Cut.
                eapply CH with (m:=S n0 + j)...
        LLPerm((FX t :: M) ++ N)...
        apply Cut...
        rewrite <- app_comm_cons.
        decide1 (FX t). inversion H2...       }
     {  inversion H9;subst;auto;
               try match goal with 
               [ H1: _ = FX t, H2: release (FX t) |- _] => rewrite <- H1 in H2;inversion H2
                end.             
        eapply @InvExT with (t:=t) (FX:=FX)...
        assert( n |--- B; M ++ [C]; (> [FX t]) ->
                j |--- B; N; (> [dual C]) ->
                 |-- B; M ++ N; (> [FX t])) as Cut.
                eapply CH with (m:=n + j)...
                apply Cut... } 
  *  assert(n |--- B; M ++ [C]; (> FX x :: M0) ->
           j |--- B; N; (> [dual C]) ->
             |-- B; M ++ N; (> FX x :: M0)) as Cut.
           eapply CH...
              
           apply H4 in properX...
  Qed.         
   
Theorem CutUP  i j w h C L M N B : CutH w h -> CutW w -> complexity C = S w -> S h = i + j ->
  i |--- B; M; (> C::L) ->
  j |--- B; N; (>> dual C) ->
  |-- B; M ++ N; (> L).
Proof with sauto;solveLL.   
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
   assert( n |--- B; M; (> F :: G :: L) -> 
          n0 |--- B; M0; (>> F ^) -> 
             |-- B; M ++ M0 ; (> G :: L)) as HcutF.
    eapply CW with (m:=complexity F)...
    inversion compC...
    apply HcutF in H9;auto.
    apply seqtoSeqN in H9.
    destruct H9.
    
    assert( x |--- B; M ++ M0; (> G :: L) -> 
           n0 |--- B; N0; (>> G ^) -> 
              |-- B; (M ++ M0) ++ N0; > L) as HcutG.
      eapply CW with (m:=complexity G)...
       
      inversion compC...
      LLPerm((M ++ M0) ++ N0)...
 * inversion Hj; CleanContext...
   assert( n |--- B; M; (> F :: L) -> 
          n0 |--- B; N; (>> F ^) -> 
             |-- B; M ++ N; (> L)) as HcutF.
    eapply CW with (m:=complexity F)...
     
    inversion compC...
    apply  HcutF ... 
  assert( n |--- B; M; (> G :: L) -> 
          n0 |--- B; N; (>> G ^) -> 
             |-- B; M ++ N; (> L)) as HcutG.
    eapply CW with (m:=complexity G)...
     
    inversion compC...
    apply  HcutG...
 * assert(N=[]).
   inversion Hj...
   subst.
    assert( n |--- B ++ [(i0,F)]; M ; (> L) -> 
           j |--- B; []; (>> i0 ! F ^) -> 
             |-- B; M ; (> L)) as UCCut.
    eapply CH with (m:=h) (C:=i0 ? F) (dualC:=i0 ! F^);eauto.
    rewrite app_nil_r...
    apply UCCut... LLExact H3.
 *  apply NotAsynchronousPosAtoms in H4...
   apply PositiveDualRelease in H.
     inversion Hj;subst; try match goal with
       [ H: _= dual ?C , H2: release (dual ?C) |- _ ] => rewrite <- H in H2
     end;CleanContext.
    assert( n |--- B; M ++ [C]; (> L) -> 
            n0 |--- B; N; (> [dual C]) -> 
             |-- B; M ++ N; (> L)) as ULCut.
   eapply CH with (m:=n+n0)... 
   apply ULCut...
   LLExact H5.
   inversion H...
   inversion Hj...
   apply seqNtoSeq in H5. LLExact H5. 
   rewrite <- H7.
   assert(n |--- (i, atom A) :: C; M; (> L)).
   eapply AbsorptionC... 
   apply allU. LLExact H5.
   apply seqNtoSeq in H0.
   LLExact H0.
   inversion H1.
  * inversion Hj;CleanContext...
   assert( n  |--- B; M; (> (FX t :: L)) -> 
           n0 |--- B; N; (>> (FX t) ^) -> 
              |-- B; M++N; (> L)) as HCut.
   eapply CW with (m:=complexity (FX (VAR con 0)));eauto...
   
   inversion compC...
   inversion compC...
    remember (VAR con 0).
            assert(proper e).
            rewrite Heqe.  
            constructor.
            eapply ComplexityUniformEq...
            
            apply HCut... 
 Qed.
      
Theorem CutK4SubCase (h n j w:nat) i a L B P: CutH w h -> CutW w -> complexity P = w -> S h = S n + j -> i <> loc ->
 tri_bangK4 theory n (B ++ [(a, P)]) i [] [] (> L) -> 
 j |--- B; []; (>> a ! P ^) -> tri_bangK4' theory B i [] [] (> L).
 Proof with sauto;solveF.
 intros HC WC comP hH Hd Hyp Hj.
        apply InvSubExpPhaseU in Hyp;auto.
        2:{ apply allU. } 
        destruct Hyp as [C4 Hyp];
        destruct Hyp as [CK Hyp];
        destruct Hyp as [CN Hyp].
        CleanContext.
        checkPermutationCases H. 
        { (* P in C4 *)
         rewrite <- Permutation_cons_append in H6. 
         inversion Hj...
         
         { rewrite H6 in H1... 
          assert(False).
            apply locAlone in Hd.
            apply Hd... left. 
          inversion H1...  
             contradiction. }
           assert(lt i a /\ m4 a = true /\ SetK4 i x).
          { rewrite H6 in H1.
            inversion H1...  } 
          CleanContext.
         finishExponential.    
       
          assert(SetK4 i CK4).
          { eapply @SetK4Trans with (i:=a)... }
          rewrite H in H8.
          change (CK4 ++ CN0) with (CK4 ++ [] ++ CN0) in H8.
          eapply @destructClassicSet' with (a:=i) in H8;auto.
          destruct H8 as [K_1 H8].
          destruct H8 as [K_2 H8].
          destruct H8 as [K_3 H8].
          destruct H8 as [K4_1 H8].
          destruct H8 as [K4_2 H8].
          destruct H8 as [K4_3 H8].
          
          destruct H8 as [N H8].
          simpl in *.         
          CleanContext.
          CleanContext.
          
          assert(Hd': S n0 |--- PlusT CK4; []; (>> (plust a) ! P^)).
          { apply BangPlusT...  }
          rewrite H.
          rewrite H21.
          rewrite H24.
            eapply @GenK4Rel' with (C4:=CK4++K4_2) (CK:=CK) (CN:=N)...
          solveSet...  
          rewrite H19 in H6.
          rewrite H6 in H1.
          inversion H1;solveSet...
          rewrite H21.
          rewrite H17...
          rewrite allSeTLEmpty...
          do 2 rewrite setUtoGetU in H7; try apply allSeTU.
          rewrite setUtoGetU; try apply allSeTU.
  assert(Hp: 
 (n - length (C4 ++ CK) - 1) |--- (PlusT CK4 ++ PlusT K4_2 ++ Loc CK) ++ [(plust a,P)]; []; (> L) ->
   S n0 |--- PlusT CK4 ++ PlusT K4_2 ++ Loc CK; []; (>> (plust a) ! P ^) -> 
   |-- PlusT CK4 ++ PlusT K4_2 ++ Loc CK; []; (> L)).
         
   eapply HC with  (m:=n - length (C4 ++ CK) - 1 + S n0) (C:=(plust a) ? P) (dualC:=(plust a) ! P^)...
   CleanContext. 
   unfold PlusT. rewrite map_app... 
   rewrite app_assoc_reverse.
   apply Hp...
   rewrite H21.
   repeat rewrite app_assoc_reverse.
   
   unfold PlusT. rewrite map_app...
   rewrite app_assoc_reverse.
   rewrite Permutation_midle_app.
   apply weakeningGenN;try apply allSeTU.
   rewrite app_assoc.
   rewrite <- map_app.
   LLExact H7.
   rewrite <- H19.
   rewrite H6...
   apply weakeningGenN_rev; try apply allSeTU. 
   LLExact Hd'. }
     checkPermutationCases H6. 
          {
           (* P in CK *)
        rewrite <- Permutation_cons_append in H6.
        inversion Hj...
          { rewrite H6 in H0. 
             assert(False).
            apply locAlone in Hd.
            apply Hd... 
            inversion H0... contradiction. }
        
          apply InvSubExpPhaseU in H14;auto.  
          2:{ apply allU. }
          destruct H14 as [C4' H14].
          destruct H14 as [CK' H14].
          destruct H14 as [CN' H14].
          CleanContext.
             assert(lt i a /\ m4 a = false /\ SetK i x0).
          { rewrite H6 in H0.
            inversion H0... 
            } CleanContext.
          assert(SetK4 i C4').
          { eapply @SetK4Trans with (i:=a)... }
          assert(SetK i CK').
          { eapply @SetKTrans with (i:=a)... }
          
          rewrite <- H9 in H8.
          rewrite H in H8.
          CleanContext.
          eapply @destructClassicSet' with (a:=i) in H8;auto.
          destruct H8 as [K_1 H8].
          destruct H8 as [K_2 H8].
          destruct H8 as [K_3 H8].
          destruct H8 as [K4_1 H8].
          destruct H8 as [K4_2 H8].
          destruct H8 as [K4_3 H8].
          
          destruct H8 as [N H8].
          simpl in *.         
          CleanContext.
          CleanContext.
           rewrite setULocgetU in H19; try apply allSeTU.
            rewrite setUtoGetU in H19; try apply allSeTU...
           rewrite setULocgetU in H7; try apply allSeTU.
            rewrite setUtoGetU in H7; try apply allSeTU...
           
           assert(Hd': S n0 |--- PlusT C4' ++ Loc CK'; []; (>> loc ! P^)).
          { apply tri_bangL...
            eapply HeightGeqCEx.
            2:{ exact H19. }
            perm.
            lia.
          }
        
       rewrite H. 
      eapply @GenK4Rel' with (C4:=C4'++K4_2) (CK:=x0++K_3) (CN:=N)...
      solveSet...  
       rewrite H24 in  H1.
       solveSet... 
      solveSet...
      solveSet.  
       rewrite H25 in  H20.
      
 
      rewrite H23.
      rewrite H25. 
      rewrite H26. 
      rewrite H29...
      
       assert(Hp: 
 (n - length (C4 ++ CK) - 1) |--- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3) ++ [(loc,P)]; []; (> L) ->
   S n0 |--- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3); []; (>> (loc) ! P ^) -> 
   |-- (PlusT C4' ++ PlusT K4_2 ++ Loc x0 ++ Loc K_3); []; (> L)).
         
   eapply HC with  (m:=n - length (C4 ++ CK) - 1 + S n0) (C:=loc ? P) (dualC:=loc ! P^)...
   CleanContext. 
   do 2 rewrite allSeTLEmpty...
   rewrite setULocgetU; try apply allSeTU.
   rewrite setUtoGetU ; try apply allSeTU...
           
   unfold PlusT. rewrite map_app... 
   rewrite app_assoc_reverse.
   apply Hp...
   LLPerm(Loc K_3++(PlusT C4' ++ PlusT K4_2 ++ Loc x0) ++ [(loc, P)]).
   apply weakeningGenN;try apply allSeTU.
   
   rewrite H26.
   repeat rewrite app_assoc_reverse.
   
   unfold PlusT. rewrite map_app...
   rewrite app_assoc_reverse.
   rewrite Permutation_midle_app.
   apply weakeningGenN;try apply allSeTU.
   rewrite app_assoc.
   rewrite <- map_app.
   LLExact H7.
   rewrite <- H24.
   rewrite H6...
   LLPerm (PlusT K4_2 ++ Loc x0 ++ PlusT C4' ++ Loc K_3).
   apply weakeningGenN;try apply allSeTU.
   rewrite H23.
   unfold Loc. rewrite map_app...
    rewrite app_assoc_reverse.
   rewrite Permutation_midle_app.
   apply weakeningGenN;try apply allSeTU.
   LLExact Hd'.
   rewrite H25...
   unfold Loc. rewrite map_app...
   fold (Loc K_1).
   rewrite Permutation_midle_app... }
  {
        eapply @GenK4Rel' with (C4:=C4) (CK:=CK) (CN:= x0)...
        rewrite <- H8.
        rewrite <- H9...
        rewrite allSeTLEmpty...
            rewrite setUtoGetU in H7; try apply allSeTU...
        apply seqNtoSeq in H7...  } 
 Qed.       

Theorem CutDwC a j n w h P F L B:
    CutH w h -> CutW w -> S h = n + j -> complexity P = w ->
    j |--- B; []; (>> a ! P ^) -> 
    n |--- B ++ [(a,P)]; L; (>> F) -> 
    |-- B; L; (> [F]).
  Proof with sauto;solveF.
  intros HC WC Hh Hc Hj Hn.
    inversion Hn...
    * store. decide1 (perp A).
    * checkPermutationCases H5.
      { store. decide1 (perp A). } 
      { inversion H2...
        simpl in Hj.
        apply (InvBangT H1 Hj). } 
     * 
      store. decide1 one.    
   * apply simplUnb in H1.
     apply simplUnb in H2.
     clear H3.
     rewrite <- H1 in H4.
     rewrite <- H2 in H8.  
     clear H1 H2.
      assert(CutF: n0 |--- B ++ [(a, P)]; M; (>> F0) ->
             j |--- B; []; (>> a ! P ^) ->
             |-- B; M; (> [F0])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P)...
      
      assert(CutG: n0 |--- B ++ [(a, P)]; N; (>> G) ->
             j |--- B; []; (>> a ! P ^) ->
             |-- B ; N; (> [G])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P)...
      store. rewrite H0.
      rewrite <- (app_nil_l []).  
        eapply @InvTensor with (B:=B) (D:=B)...
    *   assert(n0 |--- B ++ [(a, P)]; L; (>> F0) ->
             j |--- B; []; (>> a ! P ^) ->
             |-- B ; L; (> [F0])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P)...
        store. 
        apply InvPlus...
    *   assert(n0 |--- B ++ [(a, P)]; L; (>> G) ->
             j |--- B; []; (>> a ! P ^) ->
             |-- B ; L; (> [G])).
        eapply HC with (m:=n0 + j) (dualC:=a ! P ^) (C:=a ? P)...
        store. 
        apply InvPlusComm...
    *   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (> [F]) ->
             j |--- B; []; (>> a !  P ^) -> 
               |-- B; L; (> [F])).
                                       
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j)...
        apply Hc...
   *    
   assert(Hc:
              n0 |--- B ++ [(a,P)]; L; (>> (FX t)) ->
             j |--- B; []; (>> a !  P ^) -> 
               |-- B; L; (> [FX t])).
                                       
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j)...
        store.
        eapply InvEx with (t0:=t)...
    *   
        assert(Hc:
            n0 |--- B ++ [(a,P)]; []; (> [F0]) ->
             j |--- B; []; (>> a !  P ^) -> 
               |-- B; []; (> [F0])).
         
        eapply HC with (C:=a ? P) (dualC:=a ! P ^) (m:=n0 + j)...
        exact nil.
        store.
        decide1 (loc ! F0). 
    *  store. decide1 (i ! F0).
       eapply @CutK4SubCase with (n:=n0) (j:=j) (h:=h) (P:=P) (a:=a) (w:=complexity P) (B:=B)... 
       
  Qed. 

 
 Theorem CutUPC  i j w h a A L M B  : CutH w h -> CutW w -> complexity A = w -> S h = i + j ->
  i |--- B++[(a,A)]; M; (> L) ->
  j |--- B; []; (>> a ! A ^) ->
  |-- B; M; (> L).
Proof with sauto;solveLL.  
  intros CH CW compA hH Hi Hj.
  inversion Hi...  
  --  assert( n |--- B ++ [(a,A)]; M; (> M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B; M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (> F :: G :: M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B; M; (> F :: G ::M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut...
  --  assert( n |--- B ++ [(a,A)]; M; (> F :: M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B; M; (> F :: M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut... 
  --  assert( n |--- B ++ [(a,A)]; M; (> G :: M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B; M; (> G ::M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut...
  --  assert( n |--- (B ++ [(i0, F)]) ++ [(a,A)]; M; (> M0) ->
              j |--- B ++ [(i0, F)]; []; (>>  a ! A ^) -> |-- B ++ [(i0, F)]; M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              LLPerm(B  ++ [(i0, F)])...
              apply Cut...
              LLExact H3.
              apply weakeningGenN_rev...
  --  assert( n |--- B ++ [(a,A)]; F::M ; (> M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B ; F::M; (> M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut...
  -- destruct (PositiveOrRelease F).
     assert( n |--- B ++ [(a,A)]; L'; (>> F) ->
             j |--- B; []; (>>  a ! A ^) -> |-- B ; L'; (> [F])) as Cut.
     eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
     assert( |-- B ; L'; (> [F])).
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
             j |--- B; []; (>>  a ! A ^) -> |-- B ; L'; (> [F])) as Cut.
     eapply CH with (m:=n0+j) (C:=a ? A ) (dualC:=a ! A ^)...
     apply Cut...
  --  apply in_app_or in H3...
      +   assert( n |--- B ++ [(a,A)]; M; (>> F) ->
          j |--- B; []; (>>  a ! A ^) -> |-- B ; M; (> [F])) as Cut.
          eapply CH with (C:=a ? A ) (dualC:=a ! A ^)...
          eapply @AbsorptionClassic with (i:=i0) (F:=F)...
      + inversion H...
        assert( n |--- B ++ [(i0,F)]; M; (>> F) ->
          j |--- B; []; (>>  i0 ! F ^) -> |-- B ; M; (> [F])) as Cut.
          eapply CH with (C:=i0 ? F ) (dualC:=i0 ! F ^)...
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
                    S y |--- B; []; (>> F ^) ->
                      |-- B; M++[] ; > [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            CleanContext. 
           
            assert( y |--- B; [] ; (> [F^]) -> 
                  S x |--- B; M; (>> F) ->
                      |-- B; []++M ; > [ ]) as Cut.
            eapply CW with (m:=complexity F)...
            rewrite <- ng_involutive...
            rewrite DualComplexity.
            rewrite <- ng_involutive...
            CleanContext.
   -- rewrite allU in H0...
   -- assert(n |--- B ++ [(a, A)]; M; (>> F) ->
                    j |--- B; []; (>> a ! A ^) -> 
                      |-- B; M ; > [F]) as Cut.
            eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
           assert(Hs:|--B; M; (> [F])).
           apply Cut... 
             destruct (NegativeAtomDec F).
              2:{  eapply @AbsorptionTheory with (F:=F)... }
             
             inversion H...
             eapply @AbsorptionPerp' with (A:=A0)...
  --  assert( n |--- B ++ [(a,A)]; M; (> FX x ::  M0) ->
              j |--- B; []; (>>  a ! A ^) -> |-- B ; M; (> FX x :: M0)) as Cut.
              eapply CH with (C:=a ? A ) (dualC:=a ! A ^)... 
              apply Cut...
  -- createWorld i0.
   eapply @CutK4SubCase with (n:=n) (j:=j) (h:=h) (P:=A) (a:=a) (w:=complexity A) (B:=B)...
   intro... 
  Qed.
  
 
  Theorem CutElimination i j a C dualC A dualA B L M N P: 
    dualC = dual C -> 
      (i |--- B; M ++ [C]; (> L) -> j |--- B; N; (> [dualC]) -> |-- B; M ++ N; (> L)) /\
      (i |--- B; M; (> C :: L) -> j |--- B; N; (>> dualC) -> |-- B; M ++ N; (> L)) /\
       (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (>> P) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> [P]))  /\
      (dualA = A ^ ->
       dualC = a ! dualA ->
       i |--- B ++ [(a,A)] ; M; (> L) -> j |--- B; []; (>> a ! dualA) -> |-- B; M; (> L)).
  Proof with sauto;solveF;solveLL.
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
              apply DualComplexity. 
        * eapply (@CutUPC i j w h a A L M B)... 
           unfold CutElimination.CutH; intros.
          eapply CutH with (m:=m)...
           unfold CutElimination.CutW; intros.
          eapply CutW with (m:=m)...
         rewrite DualComplexity in compC...
              rewrite H0 in compC...
              inversion compC...
              apply DualComplexity. 
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
    (i |--- B ++ [(a,A)] ; M; (> L) -> 
            j |--- B; []; (>> a ! A^) -> 
                  |-- B; M; (> L)).
  Proof with subst;auto.
    intros. 
    assert(exists w, complexity A = w). 
    eexists; auto.
    destruct H1 as [w H1].
    specialize CutElimination;intros.
    assert((i |--- B ++ [(a,A)]; M ; UP L -> 
                          j |--- B; [] ; DW (a ! A^) -> 
                                        |-- B; M ; UP L)) as CUT.
    eapply H2 with (C:=a ? A) ;eauto.
    clear H2.
    apply CUT;auto.  
  Qed. 
  
    Theorem GeneralCutClassic' a A B L M: 
    (|-- B ++ [(a,A)] ; M; (> L) -> |-- B; []; (>> a ! A^) -> |-- B; M; (> L)).
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
