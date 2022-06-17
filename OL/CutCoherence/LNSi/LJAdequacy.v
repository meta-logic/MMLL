(** * System LJ for intuitionistic logic encoded as an LL theory

This file encodes the inference rules of the system LJ. Since the
rules used are cut-coherent, the cut-elimination theorem applies for
this system.
 *)


Require Import MMLL.OL.CutCoherence.OLTactics.
Require Import MMLL.OL.CutCoherence.OLPosNeg.
Require Import MMLL.OL.CutCoherence.LNSi.LJBipoles.
Require Import MMLL.SL.FLLReasoning.

Require Import Coq.Init.Nat.
Require Import MMLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

Section LJAdequacy.
Context {SI : Signature}.
Context {USI : UnbSignature}.
Context {USInoD : UnbNoDSignature}.  


(** An inductive definition for LJ. This will be used to prove that
the LL encoding is sound and complete *)

Inductive LJSeq : list uexp -> list uexp -> Prop :=
| LJTRUE : forall L L', LJSeq L ((t_cons TT)::L')
| LJFALSE : forall L L', LJSeq (t_cons FF :: L) L' 
| LJinit : forall L L' F,  LJSeq (F:: L) (F::L')

| LJAndL1 : forall L F G L', LJSeq (F :: L) L' -> LJSeq ( (t_bin AND F G) :: L) L'
| LJAndL2 : forall L F G L', LJSeq (G :: L) L' -> LJSeq ( (t_bin AND F G) :: L) L'
| LJAndR : forall L F G L', LJSeq L (F::L') -> LJSeq L (G::L') -> LJSeq L (t_bin AND F G :: L')

| LJOrL : forall L F G L',  LJSeq (F :: L) L' -> LJSeq (G :: L) L' -> LJSeq ( (t_bin OR F G) :: L) L'
| LJOrR1 : forall L F G L', LJSeq L (F::L') -> LJSeq L (t_bin OR F G :: L')
| LJOrR2 : forall L F G L', LJSeq L (G::L') -> LJSeq L (t_bin OR F G :: L')

(* Explicit exchange *)
| LJExL : forall L L' Delta, Permutation L L' -> LJSeq L Delta -> LJSeq L' Delta
| LJExR : forall L L' Delta, Permutation L L' -> LJSeq Delta L -> LJSeq Delta L'
(* Explicit contraction *)
| LJCtL : forall L L' F, LJSeq (F :: F :: L)  L' -> LJSeq (F :: L)  L'
| LJCtR : forall L L' F, LJSeq L (F :: F :: L')   -> LJSeq L (F :: L')

| LJWkL : forall L L' F, LJSeq L L' -> LJSeq (F :: L)  L'
| LJWkR : forall L L' F, LJSeq L L' -> LJSeq L (F :: L')

                 
| LJImpL : forall F G L1 L2 L1' L2', LJSeq L1 (F::L1') -> LJSeq (G:: L2) L2' -> LJSeq (t_bin IMP F G ::L1++L2) (L1'++L2')
| LJImpR : forall L F G L', LJSeqT L L' [F] [G] ->  LJSeq L (t_bin IMP F G :: L')
    with
      LJSeqT : list uexp -> list uexp -> list uexp -> list uexp -> Prop :=
       | LJLift : forall L F L' D D' T, Permutation (F::D') D -> LJSeqT D' T (F::L) L' ->  LJSeqT D T L L'                                  
       | LJRelease : forall L L' D T, LJSeq L L' -> LJSeqT D T L L'
.

Hint Constructors LJSeq : core .
Hint Constructors LJSeqT : core .

  Theorem LJSeqPerm1 D1  : forall D2 L R T,
  Permutation D1 D2 -> LJSeqT D2 T L R -> LJSeqT D1 T L R .
  Proof with  CleanContext.
   intros *.
  intros Hp Hseq.
  generalize dependent D1.
  induction Hseq;intros;eauto using Permutation_in.
  symmetry in Hp.
  eapply LJLift with (F:=F) (D':=D')...
  Qed.
  
  Theorem LJSeqPerm2 L1  : forall D L2 R T,
  Permutation L1 L2 -> LJSeqT D T L2 R -> LJSeqT D T L1 R .
  Proof with  CleanContext.
   intros *.
  intros Hp Hseq.
  generalize dependent L1.
  induction Hseq;intros;eauto using Permutation_in.
  apply LJRelease...
  eapply LJExL.
  exact (symmetry Hp).
  auto.
  Qed.

  Theorem LJSeqPerm3 R1  : forall D L R2 T,
  Permutation R1 R2 -> LJSeqT D T L R2 -> LJSeqT D T L R1.
  Proof with  CleanContext.
   intros *.
  intros Hp Hseq.
  generalize dependent R1.
  induction Hseq;intros;eauto using Permutation_in.
  apply LJRelease...
  eapply LJExR.
  exact (symmetry Hp).
  auto.
  Qed.
      
  Global Instance LJT_morph : 
  Proper ((@Permutation uexp) ==> eq ==> (@Permutation uexp) ==>  (@Permutation uexp)  ==> iff) (LJSeqT).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  - symmetry in H.
    symmetry in H1.
    symmetry in H2.
    eapply LJSeqPerm1;eauto.
    eapply LJSeqPerm2;eauto.
    eapply LJSeqPerm3;eauto.
  - eapply LJSeqPerm1;eauto.
    eapply LJSeqPerm2;eauto.
    eapply LJSeqPerm3;eauto.
Qed.

  Global Instance LJ_morph : 
  Proper ((@Permutation uexp) ==> (@Permutation uexp) ==> iff) (LJSeq).
Proof.
  unfold Proper; unfold respectful. 
  intros.
  split;intros;subst.
  - eauto. 
  - symmetry in H. 
    symmetry in H0.
    eauto. 
Qed.

  Theorem LJSeqTWkL D : forall F L R T, LJSeqT D T L R -> LJSeqT D T (F::L) R .
  Proof with  CleanContext.
   intros.
   induction H;intros...
     rewrite <- H.
     apply LJLift with (F:=F0) (D':=D')...
     eapply LJSeqPerm2.
     2:{ exact IHLJSeqT. }
     perm.
 Qed.      
 
  Theorem LJSeqTWkL' D : forall F L R T, LJSeqT D T L R -> LJSeqT (F::D) T L R .
  Proof with  CleanContext.
   intros.
   induction H;intros...
     rewrite <- H.
     rewrite perm_swap.
     apply LJLift with (F:=F0) (D':=F::D')...
 Qed.      
 
 
  Theorem LJSeqTWkR D : forall F L R T, LJSeqT D T L R -> LJSeqT D T L (F::R) .
  Proof with  CleanContext.
   intros.
   induction H;intros...
     rewrite <- H.
     apply LJLift with (F:=F0) (D':=D')...
 Qed.
   
 Theorem ImpGenInv D L R T : 
    LJSeqT D T L R ->  
    exists A B, Permutation D (A++B) /\ LJSeq (L++A) R.
  Proof with  CleanContext.
   intros.
   induction H;intros...
   - exists (F::x).
     exists x0.
     split...
     rewrite <- H...
     rewrite H2...
     eapply LJExL.
     2:{ exact H3. }
     perm.
   - exists [].
     exists D.
     split...
 Qed.    
   
 
 Theorem ImpGen D : forall A B L R T , 
    Permutation D (A++B) -> LJSeq (L++A) R ->
    LJSeqT D T L R.  
  Proof with  CleanContext.
     induction D;intros...
   checkPermutationCases H.
   2:{ eapply IHD with (T:=T) (B:=x) in H0...
       apply LJSeqTWkL'... }
   rewrite H1 in H0.    
   rewrite Permutation_midle in H0.
   rewrite app_comm_cons in H0.
   eapply IHD with (B:=B) (T:=T) in H0...
   eapply LJLift with (D':=D) (F:=a)...  
Qed.
  
Theorem LJCtLGen C : forall L L', LJSeq (C ++ C ++ L)  L' -> LJSeq (C ++ L) L'.
Proof with sauto.
  induction C;intros...
  rewrite <- app_comm_cons.
  apply LJCtL.
  rewrite Permutation_cons_append.
  rewrite Permutation_cons_append.
  do 2 rewrite app_assoc_reverse.
  eapply IHC.
  assert(Hs: Permutation (C ++ C ++ L ++ [a] ++ [a]) ((a :: C) ++ (a :: C) ++ L)) by perm.
  rewrite Hs...
Qed.


Theorem LJCtRGen C : forall L L', LJSeq L (C ++ C ++ L') -> LJSeq L (C ++ L').
Proof with sauto.
  induction C;intros...
  rewrite <- app_comm_cons.
  apply LJCtR.
  rewrite Permutation_cons_append.
  rewrite Permutation_cons_append.
  do 2 rewrite app_assoc_reverse.
  eapply IHC.
  assert(Hs: Permutation (C ++ C ++ L' ++ [a] ++ [a]) ((a :: C) ++ (a :: C) ++ L')) by perm.
  rewrite Hs...
Qed.

Theorem LJWkLGen C : forall L L', LJSeq L  L' -> LJSeq (C ++ L) L'.
Proof with sauto.
  induction C;intros...
  rewrite <- app_comm_cons.
  apply LJWkL...
Qed.

Theorem LJWkRGen C : forall L L', LJSeq L  L' -> LJSeq L (C++L').
Proof with sauto.
  induction C;intros...
  rewrite <- app_comm_cons.
  apply LJWkR...
Qed.

Lemma ContLoc
     : forall (theory : oo -> Prop) (n : nat) 
         (i : subexp) (F : oo) (B : list (subexp * oo))
         (L : multiset oo) (X : Arrow),
       mt i = true ->
       u i = true ->
       seqN theory n ((loc, F) :: B) L X ->
       seqN theory n ((i, F) :: B) L X.
 Proof.
        intros. 
        eapply ContractionLoc;auto.
        LLSwap.
        apply weakeningN;auto.
 Qed.
 
      Theorem destructSets {A:Set} (C4 C4' CN CN': list A): 
    Permutation (C4 ++ CN) (C4' ++ CN') -> 
    exists K4_1 K4_2 K4_3 N, Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
                    Permutation CN (K4_3 ++ N) /\ Permutation CN' (K4_2 ++ N). 
  Proof with sauto.
    intros.
    revert dependent C4'.
    revert dependent CN.
    revert dependent CN'.
    induction C4;intros.
    * 
      eexists []. 
      eexists []. 
      eexists C4'.
      eexists CN'. 
      simpl.
      split;auto.
    *
      checkPermutationCases H.
      - symmetry in H1. 
         eapply IHC4 in H1... 
           eexists (a::x0).
           eexists x1.
           eexists x2.
           eexists x3...
           rewrite <- app_comm_cons.
           apply Permutation_cons...
           rewrite H0.
           rewrite H3...
      - symmetry in H1. 
         eapply IHC4 in H1... 
           eexists x0.
           eexists (a::x1).
           eexists x2.
           eexists x3...
           apply Permutation_cons_app...
           rewrite H0. 
           rewrite H5... 
  Qed.
  
  
Theorem SoundenessLJT j L L' D D' 
     (Mj: mt j = true) (Fj: m4 j = true)
     (isFL: isOLFormulaL L) (isFL': isOLFormulaL L')
     (isFD: isOLFormulaL D) (isFD': isOLFormulaL D') 
     : 
     forall  (Hyp: LJSeqT D D' L L') ,
     tri_bangK4' (LJ j) (CEncode j (LEncode D)) 
                j (CEncode j (LEncode L) ++ CEncode loc (REncode L')) [] (UP []) with
     SoundenessLJ j L L' 
     (Mj: mt j = true) (Fj: m4 j = true)
     (isFL: isOLFormulaL L) (isFL': isOLFormulaL L') : 
     forall (Hyp: LJSeq L L') , seq (LJ j) (CEncode j (LEncode L) ++ CEncode loc (REncode L')) [] (UP []).
Proof with CleanContext;SLSolve;OLSolve.
* intros. 
  clear SoundenessLJT.
  induction Hyp.
  2:{
     eapply SoundenessLJ with (j:=j) in H...
    finishExp... }
    
    eapply exchangeCCK4 with (CC:=(CEncode j (LEncode (F :: D')))).
    apply CEncodePerm .
    apply Permutation_map;auto.

    simpl.
    copyK4 j (d| F |) (CEncode j (LEncode D')).
     reflexivity.
    assert(Hs:tri_bangK4' (LJ j) (CEncode j (LEncode D')) j
          (CEncode j (LEncode (F :: L)) ++ CEncode loc (REncode L')) []
          (UP [])).
    apply IHHyp...       
    rewrite <- H in isFD .
    OLSolve.
    eapply exchangeCCKK4.
    2:{ exact Hs. }
    rewrite plustpropT...

*   intros.
   clear SoundenessLJ. 
  induction Hyp;intros.
     + (* True on the right *)
    TFocus (CteBipole TT_BODY Right).
    constructor;constructor;auto.
    inversion H.
    LLTensor.
    simpl...
    rewrite  Permutation_cons_append...
    rewrite !app_assoc...
    apply weakeningGen...
    init2 loc (@nil TypedFormula).
    solveSignature1.
    simpl... 
   + (* false on the left *)
       TFocus (CteBipole FF_BODY Left).
        constructor;constructor;auto.
        inversion H.
        LLTensor;simpl...
        solveLL. 
   +
    TFocus (RINIT F)...
    apply ooth_initC...
    inversion H.
    LLTensor; simpl...
    rewrite  Permutation_cons_append...
    rewrite !app_assoc_reverse...
    apply weakeningGen...
    apply weakeningGen_rev...
    init2 loc (CEncode loc (REncode L')).
    solveSignature1.
    rewrite  Permutation_cons_append...
    apply weakeningGen...
    solveLL.
   +
     TFocus (BinBipole AND_BODY Left F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor; 
    simpl...
    rewrite Permutation_cons_append...
    apply weakeningGen...
    solveLL.
   
    LLPlusL. LLRelease. LLStore.
    rewrite Permutation_cons_append...
    apply weakeningGen_rev...
    apply PosF with (a:=j)...
    eapply IHHyp in isFL' as Hs...
   +
    TFocus (BinBipole AND_BODY Left F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor; 
    simpl...
    rewrite Permutation_cons_append...
    apply weakeningGen...
    solveLL.
   
    LLPlusR. LLRelease. LLStore.
    rewrite Permutation_cons_append...
    apply weakeningGen_rev...
    apply PosF with (a:=j)...
    eapply IHHyp in isFL' as Hs...
    +
    TFocus (BinBipole AND_BODY Right F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor;
    simpl...
    rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen...
    init2 loc (@nil TypedFormula).
    solveSignature1.
    
    LLRelease. LLWith; LLStore.
    1-2: simpl; rewrite Permutation_cons_append...
    1-2: rewrite !app_assoc.
    1-2: apply weakeningGen_rev...
   
    1-2: apply NegF with (a:=loc)...
    1: eapply IHHyp1 in isFL...
    2: eapply IHHyp2 in isFL...
    1-2:simpl in isFL.
    1-2:simpl...
    1-2: LLExact isFL.
    +
    TFocus (BinBipole OR_BODY Left F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor;
    simpl...
    rewrite Permutation_cons_append...
    apply weakeningGen...
    solveLL.
    
    LLRelease. LLWith; LLStore.
    1-2: simpl; rewrite Permutation_cons_append...
    1-2: apply weakeningGen_rev...
   
    1-2: apply PosF with (a:=j)...
    eapply IHHyp1 in isFL'...
    eapply IHHyp2 in isFL'...
   + 
    TFocus (BinBipole OR_BODY Right F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor;
    simpl...
    rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen...
    init2 loc (@nil TypedFormula).
    solveSignature1.
    
    LLPlusL. LLRelease. LLStore.
    simpl; rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen_rev...
   
    apply NegF with (a:=loc)...
    eapply IHHyp in isFL...
    simpl; simpl in isFL.
    LLExact isFL.
   + 
    TFocus (BinBipole OR_BODY Right F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor;
    simpl...
    rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen...
    init2 loc (@nil TypedFormula).
    solveSignature1.
    
    LLPlusR. LLRelease. LLStore.
    simpl; rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen_rev...
   
    apply NegF with (a:=loc)...
    eapply IHHyp in isFL...
    simpl; simpl in isFL.
    LLExact isFL.
  +  rewrite <- H in isFL.
       apply LEncodePerm in H.
       apply CEncodePerm with (i:=j) in H. 
       rewrite <- H...
  +  rewrite <- H in isFL'.
       apply REncodePerm in H.
       apply CEncodePerm with (i:=loc) in H. 
       rewrite <- H...
 +   assert(isOLFormulaL (F :: F :: L)). 
       OLSolve. OLSolve.
       simpl.    eapply contraction with (F:=(j, d| F |))...
          solveSignature1.
 +   assert(isOLFormulaL (F :: F :: L')). 
       OLSolve. OLSolve.
       simpl.    eapply contraction with (F:=(loc, u| F |))...
          solveSignature1.
       apply IHHyp in H...
       simpl in H. LLExact H.
 +      
          simpl...
          eapply weakening... 
          solveSignature1.
          apply IHHyp...
 +      
       simpl...
      LLPerm ((loc, u| F |) :: (CEncode j (LEncode L) ++
   CEncode loc (REncode L'))).
          eapply weakening... 
          solveSignature1.
     apply IHHyp... 
   + 
    TFocus (BinBipole (IMP_BODY j) Left F G)...
    apply ooth_rulesC...
    constructor...
    inversion H.
    LLTensor; 
    simpl...
    rewrite Permutation_cons_append...
    apply weakeningGen...
    solveLL.
   
    LLTensor;LLRelease; LLStore.
    1-2: rewrite Permutation_cons_append...
    1-2: apply weakeningGen_rev...
    1: apply NegF with (a:=loc)...
    2: apply PosF with (a:=j)...
    1-2: rewrite !REncodeApp.
    1-2: rewrite !LEncodeApp.
    1-2: rewrite !CEncodeApp.
    
  LLPerm((CEncode j (LEncode L1) ++ CEncode loc (REncode (F::L1')))++(
 CEncode j (LEncode L2)  ++ CEncode loc (REncode L2')
  )).
    apply weakeningGen_rev...
    apply IHHyp1...    
    inversion isFL...
 
  LLPerm((CEncode j (LEncode (G::L2)) ++ CEncode loc (REncode L2'))++(
 CEncode j (LEncode L1)  ++ CEncode loc (REncode L1')
  )).
    apply weakeningGen_rev...
    apply IHHyp2...    
    inversion isFL...
  + apply SoundenessLJT with (j:=j) in H...
      TFocus (BinBipole (IMP_BODY j)  Right F G)...
    apply ooth_rulesC...
    constructor...
    inversion H0.
    LLTensor; simpl...
rewrite Permutation_cons_append...
    rewrite !app_assoc.
    apply weakeningGen...
    init2 loc (@nil TypedFormula).
    solveSignature1.
   createWorld. solveSignature1.
   apply InvSubExpPhaseUTK4' in H;solveSignature1...
    
   eapply @GenK4RelUT' with (C4:=x ) (CK:=[]) (CN:=x0 ++
   (loc, u| t_bin (IMP_BODY j).(con) F G |) :: CEncode loc (REncode L'))...
   solveSignature1.
   rewrite H0...
   simpl...
   LLPar. do 2 LLStore.
   apply NegF with (a:=loc)...
   apply PosF with (a:=j)...
 Qed.   


(* Require Import Coq.Program.Equality. *)
Theorem Soundeness': forall a L L' D D', 
      isOLFormulaL L ->
      isOLFormulaL L' ->
      isOLFormulaL D ->
      isOLFormulaL D' ->
      mt a = true ->
      m4 a = true ->
      LJSeq (L++D) (L'++D') ->
      seq (LJ a) (CEncode a (LEncode L) ++ CEncode loc (REncode L')) (LEncode D ++ REncode D') (UP []).
Proof with solveSE;OLSolve.
  intros *.
  intros isFL isFL' isFD isFD' Ha Ha' Hyp.
 eapply PosNegSetT with (a:=a) (b:=loc)...
  eapply SoundenessLJ with (j:=a) in Hyp...
  eapply exchangeCC'.
  2:{ exact Hyp. }
  rewrite LEncodeApp.
  rewrite REncodeApp.
  rewrite !CEncodeApp... perm.
  Qed.  
  
  
  Lemma PermSecond (L1 L2: list TypedFormula): 
     Permutation L1 L2 ->
     Permutation (second L1) (second L2) .
  Proof.
  eapply Permutation_map.   
  Qed.
 

  (** Completeness theorem *)
Theorem Completeness: forall n a L L' D D', 
    isOLFormulaL L ->
    isOLFormulaL L' ->
    isOLFormulaL D ->
    isOLFormulaL D' ->
    mt a = true ->
    m4 a = true ->
    seqN (LJ a) n (CEncode a (LEncode L) ++ CEncode loc (REncode L')) (LEncode D ++  REncode D') (UP []) ->
    LJSeq (L++D) (L'++D') .
Proof with CleanContext;solveSE;OLSolve.
  induction n using strongind; intros *; 
  intros HisL HisL' HisD HisD' Ha Ha' Hseq; 
  inversion Hseq...
  * apply RemoveNotPos1 in H2;sauto...
    inversion H0; inversion H1...
    OLSolve. OLSolve.
  * apply InUNotPos in H4;sauto...
     rewrite secondApp. 
     rewrite !secCEncode...
    OLSolve. OLSolve.
  * apply RemoveNotPos2 in H4;sauto...
     rewrite secondApp. 
     rewrite !secCEncode...
    OLSolve. OLSolve.
  * inversion H1...
  + inversion H0...
  ++ (* Constant right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesU in H8... 
      apply OLInPermutation' in H5...
      rewrite H5...
      rewrite <- perm_takeit_2...
      -
      simpl in H9.
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesU in H9...
      apply OLInPermutation' in H5...
      rewrite H5...
      rewrite <- app_comm_cons...
    ++ (* constant left *)
      apply BipoleReasoning in H3...
      - simpl in H7.  
         inversion H7...
      - simpl in H7.  
         inversion H7...

    ++ (* constant left *)
      apply BipoleReasoning in H3...
      - simpl in H7.  
         inversion H7...
      - simpl in H7.  
         inversion H7...
  ++ (* Constant right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesD in H8... 
      apply OLInPermutationL' in H5...
      rewrite H5...
      rewrite <- perm_takeit_2...
      -
      simpl in H9.
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesD in H9...
      apply OLInPermutationL' in H5...
      rewrite H5...
      rewrite <- app_comm_cons...
         
  + inversion H0... 
    ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesU in H8...
      apply FocusingWith in H7...
      apply OLInPermutation' in H5...
        rewrite H5 in HisD'.
        rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJAndR...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H9.
        rewrite <- H6...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H10.
        rewrite <- H6...
       -
      apply FocusingWith in H7...
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesU in H9...
      apply OLInPermutation' in H5...
      rewrite H5 in HisL'.
      rewrite H5...
      rewrite <- app_comm_cons.
      apply LJCtR.
      rewrite app_comm_cons.
      rewrite <- H5...
      apply LJAndR.
      rewrite <- Permutation_midle.
      eapply H with (m:=x2) (a:=a)...
      LLExact H8.
      simpl...
      rewrite <- Permutation_midle.
      eapply H with (m:=x2) (a:=a)...
      LLExact H10.
      simpl...
    ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesD in H8...
      apply OLInPermutationL' in H5...
     apply FocusingPlus in H7...
      rewrite H5 in HisD.
      rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJAndL1...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H8.
        rewrite <- H6...
        
      rewrite H5 in HisD.
      rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJAndL2...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H8.
        rewrite <- H6...
       -
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesD in H9...
      apply OLInPermutationL' in H5...
      rewrite H5 in HisL.
      rewrite H5...
      rewrite <- app_comm_cons.
      apply LJCtL.
      rewrite app_comm_cons.
      rewrite <- H5...
      
      apply FocusingPlus in H7...
      
      apply LJAndL1.
      rewrite <- Permutation_midle.
      eapply H with (m:=x3) (a:=a)...
      
      apply LJAndL2.
      rewrite <- Permutation_midle.
      eapply H with (m:=x3) (a:=a)...
    ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesU in H8...
      apply OLInPermutation' in H5...
     apply FocusingPlus in H7...
      rewrite H5 in HisD'.
      rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJOrR1...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H8.
        rewrite <- H6...
        
      rewrite H5 in HisD'.
      rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJOrR2...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H8.
        rewrite <- H6...
       -
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesU in H9...
      apply OLInPermutation' in H5...
      rewrite H5 in HisL'.
      rewrite H5...
      rewrite <- app_comm_cons.
      apply LJCtR.
      rewrite app_comm_cons.
      rewrite <- H5...
      
      apply FocusingPlus in H7...
      
      apply LJOrR1.
      rewrite <- Permutation_midle.
      eapply H with (m:=x3) (a:=a)...
      LLExact H9.
      simpl...
      apply LJOrR2.
      rewrite <- Permutation_midle.
      eapply H with (m:=x3) (a:=a)...
      LLExact H9.
      simpl...
    ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesD in H8...
      apply FocusingWith in H7...
      apply OLInPermutationL' in H5...
        rewrite H5 in HisD.
        rewrite H5...
      rewrite <- perm_takeit_2...
      apply LJOrL...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H9.
        rewrite <- H6...
        
        rewrite perm_takeit_2...
        eapply H with (m:=x2) (a:=a)...
        LLExact H10.
        rewrite <- H6...
       -
      apply FocusingWith in H7...
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesD in H9...
      apply OLInPermutationL' in H5...
      rewrite H5 in HisL.
      rewrite H5...
      rewrite <- app_comm_cons.
      apply LJCtL.
      rewrite app_comm_cons.
      rewrite <- H5...
      apply LJOrL.
      rewrite <- Permutation_midle.
      eapply H with (m:=x2) (a:=a)...
      rewrite <- Permutation_midle.
      eapply H with (m:=x2) (a:=a)...

    ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesU in H8...
      apply OLInPermutation' in H4...
     apply FocusingBangPar in H7...
      rewrite H4 in HisD'.
      rewrite H4...
      rewrite <- perm_takeit_2...
      apply LJImpR...
      apply map_eq_nil in H3, H5...
      apply destructEncode2 in H8...
      symmetry in H4.
      apply Loc_no4 in H4...
      apply destructLEncode in H5...
       eapply ImpGen with (A:=x0) (B:=x6)...
      assert(LJSeq ( x0++[F0]) ([]++[G])).
        eapply H with (m:=x2) (a:=a)...
      simpl...  
        LLExact H14.
        rewrite <- H3...
      apply CEncodePerm...  
      simpl...
      
      rewrite Permutation_cons_append...
       -
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesU in H9...
      apply OLInPermutation' in H4...
      rewrite H4 in HisL'.
      rewrite H4...
      rewrite <- app_comm_cons.
      apply LJCtR.
      rewrite app_comm_cons.
      rewrite <- H4...
      
      apply FocusingBangPar in H7...
      apply map_eq_nil in H3, H10...
      apply destructEncode2 in H9...
      symmetry in H7.
      apply Loc_no4 in H7...
      apply destructLEncode in H9...
      apply LJImpR.
       eapply ImpGen with (A:=x6) (B:=x9)...
      assert(LJSeq ( x6++[F0]) ([]++[G])).
        eapply H with (m:=x3) (a:=a)...
      simpl...  
        LLExact H15.
        rewrite <- H3...
      apply CEncodePerm...  
      simpl...
      rewrite Permutation_cons_append...
     ++ (* binary connective right *)
      apply BipoleReasoning in H3...
      -
      simpl in H8.
      apply checkEncodeCasesD in H8...
      apply OLInPermutationL' in H5...
        rewrite H5 in HisD.
      rewrite H5...
      rewrite <- perm_takeit_2...
    
       apply FocusingTensor in H7...
       rewrite H9 in H6.
       apply destructEncode in H6...
       assert(LJSeq (L++x) (L'++F0 :: x5)).
        eapply H with (m:=x2) (a:=a)...
        assert(isOLFormulaL x1) by OLSolve.
        OLSolve.
      LLExact H8.
      rewrite H6...
      assert(LJSeq (L++G :: x6) (L'++x7)).
        eapply H with (m:=x2) (a:=a)...
         assert(isOLFormulaL x1) by OLSolve.
        OLSolve.
      LLExact H11.
      rewrite H10...
      assert(LJSeq (t_bin IMP F0 G :: (L++x) ++ (L++x6)) ((L'++x5) ++ (L' ++ x7))).
      apply LJImpL...
      rewrite <- Permutation_midle...
      rewrite <- Permutation_midle...
      rewrite <- Permutation_midle...
      apply LJCtLGen.
      apply LJCtRGen.
      eapply LJExR with (L:=(L' ++ x5) ++ L' ++ x7)...
      rewrite H13...
      eapply LJExL with (L:=t_bin (IMP_BODY a).(con) F0 G :: (L ++ x) ++ L ++ x6)...
      rewrite H7...
      -
      apply PermSecond in H9.
      rewrite !secondApp in H9.
      rewrite !secCEncode in H9.
      simpl in H9...
      symmetry in H9.
      apply checkEncodeCasesD in H9...
      apply OLInPermutationL' in H5...
        rewrite H5 in HisL.
      rewrite H5...
      
      rewrite <- app_comm_cons.
      
       apply FocusingTensor in H7...
       apply destructEncode in H10...
       assert(LJSeq (L++x) (L'++F0 :: x6)).
        eapply H with (m:=x3) (a:=a)...
      LLExact H9.
      rewrite H7...
      assert(LJSeq (L++G :: x7) (L'++x8)).
        eapply H with (m:=x3) (a:=a)...
      LLExact H12.
      rewrite H11...
      
      assert(LJSeq (t_bin IMP F0 G :: (L++x) ++ (L++x7)) ((L'++x6) ++ (L' ++ x8))).
      apply LJImpL...
      1-2: rewrite <- Permutation_midle...
      apply LJCtL.
      rewrite app_comm_cons.
      rewrite <- H5...
      rewrite <- Permutation_midle...
      apply LJCtLGen.
      apply LJCtRGen.
      eapply LJExR with (L:=(L' ++ x6) ++ L' ++ x8)...
      rewrite H14...
      eapply LJExL with (L:=t_bin (IMP_BODY a).(con) F0 G :: (L ++ x) ++ L ++ x7)...
      rewrite H10...
   + apply FocusingInitRuleU in H3;sauto.
    ++   
      change [u| OO |; d| OO |] with ([u| OO |] ++ [d| OO |]) in H4. 
      apply destructEncode in H4...
      apply map_eq_cons in H9...
      apply map_eq_cons in H9...
      apply map_eq_cons in H10...
      apply map_eq_cons in H7...
      apply map_eq_nil in H9...
      apply map_eq_nil in H6...
      inversion H11... inversion H10...
      
      rewrite Permutation_app_comm.
      simpl.
      rewrite Permutation_app_comm.
      simpl...
      
      apply map_eq_cons in H7...
      apply map_eq_cons in H6...
   ++  CleanContext.
        apply map_eq_cons in H8...
        apply map_eq_nil in H5...
        inversion H9...
        
        apply PermSecond in H6.
      rewrite !secondApp in H6.
      rewrite !secCEncode in H6.
      simpl in H6...
      symmetry in H6.
      apply checkEncodeCasesD in H6...
      apply OLInPermutationL' in H4...
      rewrite Permutation_app_comm.
      rewrite H4;simpl...
    ++ apply map_eq_cons in H5...
    ++ apply map_eq_cons in H8...
    ++  CleanContext.
        apply map_eq_cons in H5...
        apply map_eq_nil in H8...
        inversion H9...
        
        apply PermSecond in H6.
      rewrite !secondApp in H6.
      rewrite !secCEncode in H6.
      simpl in H6...
      symmetry in H6.
      apply checkEncodeCasesU in H6...
      apply OLInPermutation' in H4...
      rewrite Permutation_app_comm.
      rewrite H4;simpl...
     ++ 
      apply map_eq_nil in H3, H8...
         apply PermSecond in H6.
      rewrite !secondApp in H6.
      rewrite !secCEncode in H6.
      simpl in H6...
      symmetry in H6.
      apply checkEncodeCasesU in H6...
      
         apply PermSecond in H4.
      rewrite !secondApp in H4.
      rewrite !secCEncode in H4.
      simpl in H4...
      symmetry in H4.
      apply checkEncodeCasesD in H4...
      
      apply OLInPermutationL' in H4...
     apply OLInPermutation' in H6...
     rewrite H6, H4...
  + apply BipoleReasoning in H3...
     ++  
        apply FocusingQuest in H6...
        apply checkEncodeCasesD in H7... 
        apply OLInPermutationL' in H4...
        rewrite H4.
         rewrite <- perm_takeit_2...
       rewrite app_comm_cons.
        eapply H with (m:=x1) (a:=a)...
        LLExact H5.
    ++ 
      apply PermSecond in H8.
      rewrite !secondApp in H8.
      rewrite !secCEncode in H8.
      simpl in H8...
      symmetry in H8.
      apply checkEncodeCasesD in H8...
      apply OLInPermutationL' in H4...
      
      rewrite H4...
      rewrite <- app_comm_cons.
      apply LJCtL.
      rewrite app_comm_cons.
      rewrite <- H4...
        apply FocusingQuest in H6...
      rewrite app_comm_cons.
        eapply H with (m:=x3) (a:=a)...
  + apply BipoleReasoning in H3...
     ++  
        apply FocusingQuest in H6...
        apply checkEncodeCasesU in H7... 
        apply OLInPermutation' in H4...
        rewrite H4.
         rewrite <- perm_takeit_2...
       rewrite app_comm_cons.
        eapply H with (m:=x1) (a:=a)...
        LLExact H5. simpl...
    ++ 
      apply PermSecond in H8.
      rewrite !secondApp in H8.
      rewrite !secCEncode in H8.
      simpl in H8...
      symmetry in H8.
      apply checkEncodeCasesU in H8...
      apply OLInPermutation' in H4...
      
      rewrite H4...
      rewrite <- app_comm_cons.
      apply LJCtR.
      rewrite app_comm_cons.
      rewrite <- H4...
        apply FocusingQuest in H6...
      rewrite app_comm_cons.
        eapply H with (m:=x3) (a:=a)...
   
        LLExact H8. simpl...
    * solveSignature1.
Qed.
 
Theorem AdequacyLJ:  forall a L L' D D', 
   isOLFormulaL L ->
   isOLFormulaL L' ->
   isOLFormulaL D ->
   isOLFormulaL D' ->
   mt a = true -> 
   m4 a = true -> 
   (LJSeq (L ++ D) (L' ++ D') <->
          seq (LJ a)
         (CEncode a (LEncode L) ++ CEncode loc (REncode L'))
         (LEncode D ++ REncode D') (UP []) ).
Proof with sauto.
  intros.
  split;intros.
  + apply Soundeness'... 
  + apply seqtoSeqN in H5... 
    apply Completeness in H5...
Qed.

End LJAdequacy.


