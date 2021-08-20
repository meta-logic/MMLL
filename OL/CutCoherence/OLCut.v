(** * OL-Cut Elimination  *)

(** The procedure formalized here is tailored to the case of
object-logics (OL) where formulas on both the left and the right side
of the sequent can be weakened and contacted. Then, we assume that all
of them are stored into the classical context of LL. *)

Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.OLTactics.
Require Export MMLL.SL.CutElimination.
Import MMLL.Misc.Permutations.
Export ListNotations.
Export LLNotations.

Set Implicit Arguments.
  
  Class UnbNoDSignature `{UnbSignature}:=
  { 
    allNoD: forall x, md x = false; }.

(** ** Rules of the encoded proof system *)
Section OLInferenceRules.
Context {SI : Signature}.
Context {USI : UnbSignature}.
Context {USInoD : UnbNoDSignature}.  
  
(** ** Syntax *)
  
Inductive Constants := .
Inductive Connectives := AND.
Inductive UConnectives := BOX.
Inductive Quantifiers := .

Instance SimpleOLSig : OLSyntax:=
  {|
    OLType := nat;
    constants := Constants;
    uconnectives := UConnectives;
    connectives := Connectives ;
    quantifiers := Quantifiers
  |}.


   (** INIT and CUT rules *)
  Definition RINIT (F:uexp) : oo := (perp (up  F) )  ** (perp (down F) ) .
  Definition CUTL F :=  d| F | ** u| F |.
  Definition CUTC F := (loc ? d| F |) ** (loc ? u| F |).

  (** Allowing contraction and weakening on the left side of the sequent *)
  Definition POS F a := (perp (down F)) ** (a ? (atom (down F))).
  (** Allowing contraction and weakening on the right side of the sequent *)
  Definition NEG F a := (perp (up F)) ** (a ? atom (up F)).

  Inductive Side := Left | Right .
  
  Definition ConjunctionDefs (lab : connectives) (s:Side) (A B : uexp)  :=
       match s with
      | Left => (d^| t_bin lab A B|) ** (d|A| op d|B|)
      | Right => (u^| t_bin lab A B|) ** (u|A| & u|B|)
   end.
  
  Definition ModalDefs (lab : uconnectives)  (s:Side) (A : uexp) (i: subexp)  :=
       match s with
      | Left => (d^| t_ucon lab A|) ** (i ? (d|A|))
      | Right => (u^| t_ucon lab A|) ** (i ! (u|A|))
     end.
   
  (** The cut rule applied on object level terms of a given size  *)
  Inductive RCUTcN (n:nat) : oo -> Prop :=
  | ltn : forall (F:uexp) m, isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              RCUTcN n (CUTL F)
  | ctn : forall (F:uexp) m, isOLFormula F ->
                              lengthUexp F m -> m <= n ->
                              RCUTcN n (CUTC F).                              
 
 Theorem ConjunctionIsFormula : forall T S A B,
      isFormula ((ConjunctionDefs T S A B) ).
    intros.
    destruct T;destruct S;repeat constructor;auto. 
  Qed.
 
 Theorem ConjunctionIsFormulaPerp : forall T S A B,
      isFormula ((ConjunctionDefs T S A B) ^ ).
    intros.
    destruct T;destruct S;repeat constructor;auto. 
  Qed.
  
Theorem RINITIsFormula : forall F,
      isFormula (RINIT F).
    intros.
    repeat constructor;auto.
  Qed.

  Theorem MRulesIsFormula : forall T S A i,
    isFormula ((ModalDefs T S A i) ).
    intros.
    destruct T; destruct S;simpl;sauto;
    repeat constructor;auto. 
  Qed.
  
 Theorem MRulesIsFormulaPerp : forall T S A i,
    isFormula ((ModalDefs T S A i) ^ ).
    intros.
    destruct T;destruct S;simpl;sauto;
    repeat constructor;auto. 
  Qed.
  
  
  
  (** This is the FLL logical theory including the right and left
    rules for the connectives and constants *)
  
  Inductive buildTheory {i: subexp} : oo ->  Prop := 
  | bconnR : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (ConjunctionDefs C Right F G)  
  | bconnL : forall C F G, isOLFormula ( t_bin C F G) -> buildTheory  (ConjunctionDefs C Left F G)
  | bmR : forall C A, mt i = true -> m4 i = true -> isOLFormula (t_ucon C A) -> buildTheory  (ModalDefs C Right A i)
  | bmL : forall C A, mt i = true -> m4 i = true -> isOLFormula (t_ucon C A) -> buildTheory (ModalDefs C Left A i).
  
  (** A theory containing only the logical rules and init *)
  Inductive OLTheory  {i:subexp} {a:subexp} {b:subexp} : oo -> Prop :=
  | ooth_rules : forall OO, buildTheory (i:=i) OO ->  OLTheory OO
  | ooth_init : forall OO, isOLFormula OO -> OLTheory (RINIT OO)
  | ooth_pos : forall OO , u a = true -> mt a = true -> isOLFormula OO -> OLTheory (POS OO a) 
  | ooth_neg : forall OO , u b = true -> mt b = true -> isOLFormula OO -> OLTheory (NEG OO b) 
.

  (** The theory [RCUTcN m] is weaker than [RCUTcN n] whenever [m <= n]. *)
  Lemma CuteRuleNBound : forall h n B L X ,  seqN (RCUTcN n) h B L X ->
                                             forall m, n<=m -> seq (RCUTcN m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (RCUTcN n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (RCUTcN m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveF 
                   );clear Hs
             end;solveLL;auto.
    -         
    rewrite H3. tensor M N B0 D.
    -
    decide1 F ;eauto.
    -
    decide2u i F;eauto ...
    -
    decide2l i F;eauto ...
    -
    decide3 F;eauto ...
    inversion H3...
    apply @ltn with (m:= m0)...
    apply @ctn with (m:= m0)...
   
    -
    existential t.
    -
    apply H4 in properX.
    eapply H with (m0:=m) in properX...
    - 
    finishExponential.
    eapply @GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
    eapply H with (m0:=m) in H10...
    - 
    finishExponential.
    createWorld i.
    eapply @GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
    intro... SLSolve.
    eapply H with (m0:=m) in H10...
    intro... SLSolve.
  Qed.

 Lemma CuteRuleN : forall n F, RCUTcN n F ->
                                             forall m, n<=m -> RCUTcN m F.
  Proof with sauto.
    intros.
    inversion H...
    econstructor;eauto.
    (transitivity n);auto.
    econstructor;eauto.
    (transitivity n);auto.
  Qed.


  Lemma CuteRuleNBound' : forall n B L X ,
      seq (RCUTcN n)  B L X ->
      forall m, n<=m -> seq (RCUTcN m) B L X .
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  
  (** There are no (object logic) formulas of size 0 *)
  Lemma CuteRuleN0 : forall F, ~ (RCUTcN 0 F).
  Proof with solveF.
    intros F Hn.
    inversion Hn...
    generalize (LengthFormula H H0); intro.
    lia.
    generalize (LengthFormula H H0); intro.
    lia.
  Qed.

  (** A theory including cuts of size [n] *)
  Inductive OLTheoryCut (n:nat) {i:subexp} {a:subexp} {b:subexp} : oo -> Prop :=
  | oothc_theory : forall OO, buildTheory (i:=i) OO ->  OLTheoryCut n OO
  | oothc_init : forall OO, isOLFormula OO -> OLTheoryCut n (RINIT OO) 
  | oothc_pos : forall OO , u a = true -> mt a = true -> isOLFormula OO -> OLTheoryCut n (POS OO a) 
  | oothc_neg : forall OO , u b = true -> mt b = true -> isOLFormula OO -> OLTheoryCut n (NEG OO b) 
  | oothc_cutln : forall OO, RCUTcN n (CUTL OO) -> OLTheoryCut n (CUTL OO)
  | oothc_cutcn : forall OO, RCUTcN n (CUTC OO) -> OLTheoryCut n (CUTC OO)
  .
  
  
  Local Hint Constructors  OLTheoryCut OLTheory  : core.
  Local Hint Unfold RINIT CUTL CUTC  : core.
 
Lemma CutRuleNBound : forall h n a b i B L X ,  seqN (OLTheoryCut (i:=i)  (a:=a) (b:=b) n) h B L X ->
                         forall m, n<=m -> seq (OLTheoryCut (i:=i)  (a:=a) (b:=b) m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i0 C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (OLTheoryCut (i:=i)  (a:=a) (b:=b) n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (OLTheoryCut (i:=i)  (a:=a) (b:=b) m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (m0:=m) (B:= B1);solveF 
                   );clear Hs
             end;solveLL;auto.
    - init2 i0 C. 
             
    -         
    rewrite H3. tensor M N B0 D.
    -
    decide1 F ;eauto.
    -
    decide2u i0 F;eauto ...
    -
    decide2l i0 F;eauto ...
    -
    decide3 F;eauto ...
    inversion H3...
    apply oothc_cutln.
    eapply CuteRuleN;eauto.
    apply oothc_cutcn.
    eapply CuteRuleN;eauto.
    -
    existential t.
    -
    apply H4 in properX.
    eapply H with (m0:=m) in properX...
    - 
    finishExponential.
    eapply @GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
    eapply H with (m0:=m) in H10...
    - 
    finishExponential.
    createWorld i0.
    eapply @GenK4Rel' with (C4:=CK4) (CK:=CK) (CN:=CN)...
    intro... SLSolve.
    eapply H with (m0:=m) in H10...
    intro... SLSolve.
  Qed.

  Lemma CutRuleNBound' :  forall n a b i B L X ,  
  seq (OLTheoryCut (i:=i)  (a:=a) (b:=b) n)  B L X ->
                         forall m, n<=m -> seq (OLTheoryCut (i:=i)  (a:=a) (b:=b) m) B L X .
  Proof with solveF.
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CutRuleNBound;eauto.
  Qed.
  
  (** Some easy equivalences on the  above theories *)
 Lemma OOTheryCut0 : forall i F, 
 (OLTheory (a:=i) (b:=i) (i:=i)) F <-> (OLTheoryCut (a:=i) (b:=i) (i:=i) 0) F.
    intros.
    split;intro H ;inversion H;subst;auto.
    *
    inversion H0;subst.
    assert (m =  0) by lia;subst.
    generalize (LengthFormula H3 H4);intro.
    lia.
 *
    inversion H0;subst.
    assert (m =  0) by lia;subst.
    generalize (LengthFormula H3 H4);intro.
    lia.
  Qed.
   
  Lemma TheoryEmb1 : forall a b i n F  ,  
  (OLTheory (a:=a) (b:=b) (i:=i)) F -> 
  (OLTheoryCut (a:=a) (b:=b) (i:=i) n) F.

    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.

  
  
  Lemma TheoryEmb2 : forall i n F  , ((RCUTcN n) F) -> (OLTheoryCut (a:=i) (b:=i) (i:=i) n) F.
    intros.
    inversion H;subst.
    apply oothc_cutln;auto.
    apply oothc_cutcn;auto.
  Qed.


  (** ** Invertibility lemmas *)
  (** In the following we prove that, when focusing on the bipole
  representing an OL rule, the derivation necessary has a specific
  shape *)

  Lemma Init_inversion1 : forall h F D th,
      seqN th h [] D (>> RINIT F) -> Permutation D ([u| F |] ++ [d| F |]) .
  Proof with sauto.
    intros.
    FLLInversionAll...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct B) in H1.
    rewrite H3 in H1.
    rewrite H in H1.
    simpl in H1...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct D0) in H11.
    rewrite H4 in H11.
    rewrite H0 in H11.
    simpl in H11...
    simpl in *. 
    CleanContext.
    rewrite (cxtDestruct D0) in H13.
    rewrite H4 in H13.
    rewrite H0 in H13.
    simpl in H13...
  Qed.  
    
   
 (*  Theorem TENSORPARInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
    LLExact H0.
  Qed.

  Theorem TENSORPARInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAR Right A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem TENSORPAREXCHInv : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (u| A |:: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
    LLExact H0.
  Qed.

  Theorem TENSORPAREXCHInv' : forall A B Gamma  n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs TENSORPAREXCH Right A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem PARTensorInv : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (d| A | :: d| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Left A B ) .
    intros;simpl;solveLL.
    LLExact H.
  Qed.

  Theorem PARTensorInv' : forall A B Gamma n,
      ( seq (OLTheoryCut (pred n)) (u| A | :: Gamma) [] (> [])) ->
      ( seq (OLTheoryCut (pred n)) (u| B | :: Gamma) [] (> [])) ->
      seq (OLTheoryCut (pred n)) Gamma [] (>> RulesDefs PARTENSOR Right A B ) .
    intros;simpl;solveLL;
      rewrite Permutation_app_comm;simpl;auto.
  Qed.
*)

Lemma emptyContext C : getU C = [] -> getL C =[] -> C = [].
Proof.
 intros.
 apply Permutation_nil.
 rewrite (cxtDestruct C).
 rewrite H; rewrite H0;auto. 
 Qed.
 
 
    Lemma FocusingInitRuleU : forall h F D B th,
      seqN th h B D (>> RINIT F) -> 
      Permutation D ([u| F |] ++ [d| F |]) \/ 
      (exists i, D = [u| F |] /\ In (i,d| F |) B /\ mt i = true /\ u i = true ) \/ 
      (exists i, D = [d| F |] /\ In (i,u| F |) B  /\ mt i = true ) \/
      (exists i j, In (i,d| F |) B /\ In (j,u| F |) B/\ mt i = true /\mt j = true /\ D=[]).
  Proof with sauto.
    intros.
    inversion H...
    apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.
    - inversion H9; 
      inversion H10...
      + CleanContext.
        right.
        left.
        exists i.
        split;auto.
        split;auto.
        rewrite <- H14...
        CleanContext. apply allU.
      + inversion H7.
      + right.
        right.
        left.
        exists i.
        split;auto.
        split;auto.
        rewrite <- H7...
       + CleanContext. 
         do 3 right.
          exists i0.
          exists i.
         split...
         rewrite <- H16...
         rewrite <- H7...
        + inversion H11.
        + inversion H1.
        + inversion H1.
        + inversion H8.
    - inversion H1. 
  Qed.  
  
  Theorem FocusingRightRuleU : forall n C D B F G th,
      (seqN th n B D (>> ConjunctionDefs C Right F G)) ->
 (exists m N, n = S m /\ Permutation D ((u|t_bin C F G|)::N) /\
                seqN th m B N  (>> u| F | & u| G |)) \/
   (exists m i, n = S m /\ In (i,u| t_bin C F G |) B /\ mt i = true /\
                seqN th m B D  (>> (u| F | & u| G |))).
  Proof with sauto.
  intros.
  inversion H... 
    -     apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
     right.  
      exists n0. exists i.
      split;auto.
      split;auto.
      rewrite <- H7...
      split;auto.
      LLExact H10.
      inversion H1.
    - inversion H1.
  Qed.      

  Theorem FocusingLeftRuleU : forall n C D B F G th,
      (seqN th n B D (>> ConjunctionDefs C Left F G)) ->
 (exists m N, n = S m /\ Permutation D ((d|t_bin C F G|)::N) /\
                seqN th m B N  (>> d| F | op d| G |)) \/
   (exists m i, n = S m /\ In (i,d| t_bin C F G |) B /\ mt i = true /\
                seqN th m B D  (>> (d| F | op d| G |))).
  Proof with sauto.
  intros.
  inversion H... 
    -     apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9...
      left.
      exists n0. exists N.
      split;auto.
     right.  
      exists n0. exists i.
      split;auto.
      split;auto.
      rewrite <- H7...
      split;auto.
      LLExact H10.
      inversion H1.
    - inversion H1.
  Qed.      

  Theorem FocusingRightMU : forall n a C D B A th,
      (seqN th n B D (>> ModalDefs C Right A a)) ->
     (exists m, n = S m /\ D = [u|t_ucon C A|] /\
                seqN th m B []  (>> (a ! u| A |))) \/
    (exists m i, n = S m  /\ In (i,u| t_ucon C A |) B /\ D = [] /\ mt i = true /\
                seqN th m B D (>> (a ! u| A |))).
  Proof with sauto.
      intros.
    inversion H...
    
    *  apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9...
      - 
      assert(N=[]).
      inversion H10...
      inversion H1.
      subst...
      
            left.
      exists n0. 
      split;auto.
      -
      right.
      exists n0. exists i.
      split;auto.
      split;auto.
      rewrite <- H7...
      CleanContext.
      inversion H10...
      inversion H4.
      rewrite H2...
    - inversion H1.
    * inversion H1.
  Qed.      

 
  Theorem FocusingLeftMU : forall n a C D B A th,
      (seqN th n B D (>> ModalDefs C Left A a)) ->
     (exists m N, n = S (S (S m)) /\ Permutation D ((d|t_ucon C A|)::N) /\
                seqN th m (B++[(a,d|A|)]) N (> [] )) \/
    (exists m i, n = S (S (S m))  /\ In (i,d| t_ucon C A |) B /\ mt i = true /\
                seqN th m (B++[(a,d|A|)]) D (> [])).
  Proof with sauto.
      intros.
    inversion H...
    
    *  apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9...
      -
       left.
      inversion H10...
      inversion H7...
      
      exists n0. exists N.
      split;auto.
      split;auto.
      LLExact H8.
      
      solveLL.
      -
      right.
      inversion H10;solveLL...
      inversion H11;solveLL...
       
      exists n0. exists i.
      split;sauto.
      rewrite <- H7...
       LLExact H12.
     - inversion H1. 
    * inversion H1.
  Qed.      

 
  Theorem FocusingPOSU : forall n a D B OO th,
   seqN th n B D (>> POS OO a) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((d| OO |)::N) /\
                seqN th m ((a, d| OO |)::B) N  (> [] )) \/
    (exists m i, n = S (S (S m))  /\ In (i,d| OO |) B /\ mt i = true /\
                seqN th m ((a, d| OO |)::B) D  (> [] )).            
   Proof with sauto.
    intros.
    inversion H...
    
    *  apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9... 
      inversion H10...
      inversion H7...
      left.
      exists n0. exists N.
      split;auto.
      solveLL.
     
      right.
      inversion H10...
      inversion H11...
      exists n0. exists i.
      split;sauto.
      rewrite <- H7...
      rewrite H2...
      solveLL. 
      inversion H1.
      * inversion H1.
 Qed.
 
  Theorem FocusingNEGU : forall n a D B OO th,
   seqN th n B D (>> NEG OO a) ->
   (exists m N, n = S (S (S m)) /\  Permutation D ((u| OO |)::N) /\
                seqN th m ((a, u| OO |)::B) N  (> [] )) \/
    (exists m i, n = S (S (S m))  /\ In (i,u| OO |) B /\ mt i = true /\
                seqN th m ((a, u| OO |)::B) D  (> [] )).            
   Proof with sauto.
    intros.
    inversion H...
    
    *  apply simplUnb in H3.
    apply simplUnb in H4.
    rewrite <- H3 in H9.
    rewrite <- H4 in H10.
    clear H3 H4 H5.

      inversion H9... 
      inversion H10...
      inversion H7...
      left.
      exists n0. exists N.
      split;auto.
      solveLL.
     
      right.
      inversion H10...
      inversion H11...
      exists n0. exists i.
      split;sauto.
      rewrite <- H7...
      rewrite H2...
      solveLL. 
      inversion H1.
      * inversion H1.
 Qed.
 
  Theorem AppPARTENSORRight :
    forall n  A B D G th,
    (seqN th n G D (>> u| A | & u| B |)) ->
      exists m , n = S(S(S m))  /\
                 (seqN th m G (u| A |::D) (> []) ) /\
                 (seqN th m G (u| B |::D) (> []) ) .
  Proof with sauto;solveLL.
    intros.
    FLLInversionAll...
    eexists.
    split;eauto.
  Qed.

  Theorem AppPARTENSORLeft:
    forall n  A B D G th,
    (seqN th n G D (>> d| A | op d| B |)) ->
     ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| A |::D) (> []) )) \/
    ( exists m , n = (S(S (S m)))  /\
                 (seqN th m G (d| B |::D) (> []) ))              .
  Proof with sauto.
    intros.
    FLLInversionAll...
    left.
    eexists.
    split;eauto.
    right.
    eexists.
    split;eauto.
  Qed.
  
  Theorem AppQUESTBANGRight :
    forall n a A D G th, mt a = true ->
    seqN th n G D (>> (a ! u| A |)) ->
      exists m, n =  (S(S m))  /\
                  ( seqN th m G (u| A |::D) (> [])).
  Proof with sauto;solveLL.
    intros.
    assert(D=[]).
    { inversion H0... }
    subst.
    apply InvBangTN in H0...
    inversion H0...
    eexists n0. 
    split;auto. lia.
 Qed.

  Theorem AppQUESTBANGRightLoc :
    forall n a A C D G th, mt a = true -> m4 a =true ->
    seqN th n ((loc,C)::G) D (>> (a ! u| A |)) ->
      exists m X1 X2, n = (S m) + length X1 +2 /\ Permutation G (X1++X2) /\ SetT X1 /\ SetK4 a X1 /\ 
                  ( seqN th m X1 (u| A |::D) (> [])).
  Proof with sauto;solveLL.
    intros.
    assert(D=[]).
    { inversion H1... }
    subst.
    apply InvBangTNLoc in H1...
    inversion H4...
    eexists n0.
    exists x.
    exists x0. 
    split;auto.
    lia.
 Qed.
 

Theorem AppQUESTBANGLeft :
    forall n a A D G th, 
    seqN th n G D (>> (a ? d| A |)) ->
      exists m, n =  (S(S m))  /\
                  ( seqN th m ((a,d| A |)::G) D (> [])).
  Proof with sauto;solveLL.
    intros.
    inversion H...
    inversion H5...
    eexists;split;eauto. 
 Qed.


  
          
Ltac CutTacPOSNEG := sauto;
  try
    match goal with
    | [ |- isFormula _] => constructor;auto
    | [ |- IsPositiveAtomFormula _] =>  constructor;auto
    | [ |- OLTheoryCut _ _] =>  solve[constructor;constructor;auto]
    | [ H: ~ IsPositiveAtom ?F, H': In ?F (atom _ :: _) |-_] => 
      solve [apply PositiveAtomIn in H';auto;contradiction]
    | [ H: seqN _ _ _ _ (>> zero) |- _] => invTri H
    | [ H: seq  _ _ _ (>> zero) |- _] => invTri' H
    | [ |- OLTheoryCut _ _ ]=> solve [repeat (constructor;auto)]
    | [ |- OLTheory _ ]=> solve [repeat (constructor;auto)]
    | [|- IsPositiveAtomFormulaL (d| _ | :: _)] => solve[repeat (constructor;auto)]
    end; OLSolve.

(** ** Cut-Elimination theorem *)
Section OLCutElimination.

  Theorem TheoryCutIsFormula n i F:
    OLTheoryCut n (a:=i) (b:=i) (i:=i) F -> isFormula F.
  Proof with CutTacPOSNEG.
    intros.
    inversion H...
    inversion H0...
 Qed.   
  
  Local Hint Resolve TheoryCutIsFormula: core.
 
Lemma PosSetP L : forall a (th : oo -> Prop) D M, 
SetU D -> isOLFormulaL L -> (forall OO: uexp, isOLFormula OO -> th (POS OO a)) ->
mt a = true -> u a = true -> 
seq th (CEncode a (LEncode L)++D ) (M) (> []) -> 
seq th D (M++LEncode L) (> []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H0...
  simpl in *...
  
  decide3 (POS a a0)...
  tensor [d| a |] (M ++ LEncode L)...
    eapply IHL with (a:=a0)...
    LLExact H4.
 Qed.    

Lemma NegSetP L : forall a (th : oo -> Prop) D M, 
SetU D -> isOLFormulaL L -> (forall OO: uexp, isOLFormula OO -> th (NEG OO a)) ->
mt a = true -> u a = true -> 
seq th (CEncode a (REncode L)++D ) (M) (> []) -> 
seq th D (M++REncode L) (> []).
Proof with sauto.
  induction L;intros...
  simpl in *...
  inversion H0...
  simpl in *...
  
  decide3 (NEG a a0)...
  tensor [u| a |] (M ++ REncode L)...
    eapply IHL with (a:=a0)...
    LLExact H4.
 Qed.
 
Theorem PosNegSetT : forall a b (th:oo->Prop) D L1 L2,  
SetU D -> isOLFormulaL L1 -> isOLFormulaL L2 ->
(forall OO: uexp, isOLFormula OO -> th (NEG OO b)) ->
(forall OO: uexp, isOLFormula OO -> th (POS OO a)) ->
mt a = true -> u a = true ->
mt b = true -> u b = true ->
seq th (D ++ CEncode a (LEncode L1) ++ CEncode b (REncode L2)) [] (> []) ->
seq th D (LEncode L1++REncode L2) (> []).
Proof with sauto.
  intros.
  apply NegSetP with (a:=b)...
  rewrite <- (app_nil_l (LEncode L1)).
  apply PosSetP with (a:=a)...
  LLExact H8. 
Qed.  
 

Lemma PosNegSetT' : forall (th:oo->Prop) D L1 L2,  
(forall OO: uexp, isOLFormula OO -> th (NEG OO loc)) -> (forall OO: uexp, isOLFormula OO -> th (POS OO loc)) ->
SetU D -> IsPositiveAtomFormulaL L1 -> IsPositiveAtomFormulaL L2 ->
seq th (CEncode loc L1++CEncode loc L2 ++D) [] (> []) ->
seq th D (L1++L2) (> []).
Proof with sauto.
  intros.
  assert(IsPositiveAtomFormulaL L1) by auto.
  assert(IsPositiveAtomFormulaL L2) by auto.
  apply posDestruct' in H2.
  apply posDestruct' in H3...
  assert(isOLFormulaL x1).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x).
  apply PositiveAtomLEOLFormula.
  OLSolve.
  assert(isOLFormulaL x2).
  apply PositiveAtomREOLFormula.
  OLSolve.
  assert(isOLFormulaL x0).
  apply PositiveAtomREOLFormula.
  OLSolve. 
 
  rewrite H2.
   
  LLPerm((L2++LEncode x1) ++ REncode x2).
  apply NegSetP with (a:=loc)...
  SLSolve. SLSolve.
  apply PosSetP with (a:=loc)...
  SLSolve. SLSolve.
  
  rewrite H3.
  apply NegSetP with (a:=loc)...
  SLSolve. SLSolve.
  rewrite <- (app_nil_l (LEncode x)).
  apply PosSetP with (a:=loc)...
  SLSolve. SLSolve.
  eapply exchangeCC.
  2:{ exact H4. }
  srewrite H2.
  srewrite H3.
  OLfold.
  rewrite !CEncodeApp.
  perm.
Qed.  


 Definition TH i := OLTheory (a:=loc) (b:=loc) (i:=i).
 Definition THC i n := OLTheoryCut (a:=loc) (b:=loc) (i:=i) n.
 
 Definition CutC (h: nat) (a:subexp) := forall m n i j FC M N L,
    m <= h ->
    m = i + j ->
    isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL N ->
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second L) ->
    SetU L ->
    (seqN (TH a) i ((loc,u|FC|)::L) M (> []) ->
     seqN (TH a) j ((loc,d|FC|)::L) N (> []) -> seq (THC a n) L (M ++ N) (> [])).
 
  Definition CutL (h: nat) (a:subexp) := forall m n i j FC M N L,
    m <= h ->
    m = i + j ->
    isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL N ->
   IsPositiveAtomFormulaL M ->
   IsPositiveAtomFormulaL (second L) ->
    SetU L ->
    (seqN (TH a) i L (u| FC | :: M) (> []) ->
     seqN (TH a) j L (d| FC | :: N) (> []) -> seq (THC a n) L (M ++ N) (> [])).

     
 Lemma aux_cut a x C L N A: 
 m4 a = true -> mt a = true ->
 isOLFormula (t_ucon C A) ->
 IsPositiveAtomFormulaL (second L) ->
 IsPositiveAtomFormulaL N ->
 seqN (TH a) x (L ++ [(a, d| A |)] ++ Loc [(a, d| t_ucon C A |)]) N (> []) ->
 seq (TH a) (L ++ [(a, d| A |)]) N (> []).
 Proof with CleanContext.
 revert a C L N A.
 induction x using strongind;intros a C L N A mtA m4A isF isFL isFN Hp...
 inversion Hp.
 inversion Hp...
 apply RemoveNotPos1 in H2;sauto...
 apply InUNotPos in H4;sauto...
 OLSolve.       
 apply RemoveNotPos2 in H4;sauto...
 OLSolve. 
 2:{ rewrite allNoD in H2;CleanContext. }
 
 inversion H1...
 - inversion H0...
   --
    apply FocusingRightRuleU in H3...
   apply AppPARTENSORRight in H8...
   eapply H in H8 ...
   eapply H  in H9...
   decide3((ConjunctionDefs C0 Right F0 G)).
   tensor [u| t_bin C0 F0 G |] x1.
   OLSolve. OLSolve.
   
   apply AppPARTENSORRight in H9...
   apply in_app_or in H7...
   apply H in H9...
   apply H in H10...
   decide3((ConjunctionDefs C0 Right F0 G)).
   tensor (@nil oo) N...
   apply InPermutation in H3...
   init2 x1  ((a, d| A |)::x0).
   rewrite H3...
   OLSolve. OLSolve.
   --
   apply FocusingLeftRuleU in H3...
   apply AppPARTENSORLeft in H8...
   apply H in H6...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor [d| t_bin C0 F0 G |] x1...
   oplus1.
   OLSolve. 
   apply H in H6...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor [d| t_bin C0 F0 G |] x1...
   oplus2.
   OLSolve.
   apply in_app_or in H7;CleanContext.
   apply AppPARTENSORLeft in H9...
   apply H in H8...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor (@nil oo) N...
   apply InPermutation in H3...
   init2 x1  ((a, d| A |)::x0).
   rewrite H3...
   oplus1. 
   OLSolve. 
   apply H in H8...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor (@nil oo) N...
   apply InPermutation in H3...
   init2 x1  ((a, d| A |)::x0).
   rewrite H3...
   oplus2. 
   OLSolve.
   apply AppPARTENSORLeft in H9...
   apply H in H7...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor (@nil oo) N...
   init2 x1 L.
   oplus1. OLSolve.
   apply H in H7...
   decide3((ConjunctionDefs C0 Left F0 G)).
   tensor (@nil oo) N...
   init2 x1 L.
   oplus2. OLSolve.
   --
   assert(a <> loc).
   intro... SLSolve.
   apply FocusingRightMU in H3...
   decide3(ModalDefs C0 Right A0 a).
   tensor [u| t_ucon C0 A0 |] (@nil oo).
   simpl in H11.
   LLPermH H11 (Loc [(loc, d| t_ucon C A |)]++ (L ++ [(a, d| A |)])).
   apply AppQUESTBANGRightLoc in H11...
   checkPermutationCases H10.
   apply GenK4Rel' with (C4:=[(a, d| A |)]++x0) (CK:=[]) (CN:=x2)...
   rewrite <- Permutation_cons_append in H8.
   rewrite H8 in H11...
   rewrite <- H10... 
  solveLL.
  rewrite H8 in H13.
  apply seqNtoSeq in H13.
  
  rewrite plustpropT...
  rewrite SetTPlusT...
  LLExact H13.
  SLSolve.
 
   apply GenK4Rel' with (C4:=x1) (CK:=[]) (CN:=[(a, d| A |)]++x0)...
   rewrite <- H10...
  solveLL.
  apply seqNtoSeq in H13.
  LLExact H13.
  
  apply in_app_or in H10;CleanContext.
  decide3(ModalDefs C0 Right A0 a).
   tensor (@nil oo) (@nil oo).
   apply InPermutation in H3...
   init2 x1 ((a, d| A |)::x).
   rewrite H3...
   
   LLPermH H13 ([(loc, d| t_ucon C A |)]++ (L ++ [(a, d| A |)])).
   apply AppQUESTBANGRightLoc in H13...
   checkPermutationCases H12.
   apply GenK4Rel' with (C4:=[(a, d| A |)]++x0) (CK:=[]) (CN:=x3)...
   rewrite <- Permutation_cons_append in H9.
   rewrite H9 in H13...
   rewrite <- H12...
   solveLL.
  rewrite plustpropT...
  rewrite SetTPlusT...
  rewrite H9 in H15.
  apply seqNtoSeq in H15.
  LLExact H15.
  SLSolve.
  
   apply GenK4Rel' with (C4:=x2) (CK:=[]) (CN:=[(a, d| A |)]++x0)...
   rewrite <- H12...
  solveLL.
  apply seqNtoSeq in H15.
  LLExact H15.
  -- apply FocusingLeftMU in H3...
     decide3(ModalDefs C0 Left A0 a).
     tensor [d| t_ucon C0 A0 |] x1.
     LLPermH H10 ((L ++ [(a, d| A0 |)]) ++ [(a, d| A |); (loc, d| t_ucon C A |)]).
     apply H in H10...
     LLExact H10.
     OLSolve. OLSolve.
     OLSolve.
      
     apply in_app_or in H9;CleanContext.
     
     decide3(ModalDefs C0 Left A0 a).
     tensor (@nil oo) N.
     apply InPermutation in H3...
     init2 x1 ((a, d| A |)::x).
     rewrite H3... 
     LLPermH H11 ((L ++ [(a, d| A0 |)]) ++ [(a, d| A |); (loc, d| t_ucon C A |)]).
     apply H in H11...
     LLExact H11.
     OLSolve. OLSolve.
     
     decide3(ModalDefs C0 Left A0 x1).
     tensor (@nil oo) N.
     init2 x1 L.
     rewrite app_comm_cons.
     eapply H with (C:=C)... OLSolve.
     LLExact H11.
     
     apply contraction with (F:=(a, d| A0 |))...
     SLSolve.
     rewrite app_comm_cons.
     eapply H with (C:=C0)... OLSolve.
     LLExact H11.
  - apply FocusingInitRuleU in H3...
    decide3(RINIT OO).
    tensor [u| OO|] [d| OO|].
    apply in_app_or in H6;CleanContext.
    decide3(RINIT OO).
    tensor [u| OO|] (@nil oo).
    apply InPermutation in H3...
    init2 x0 ((a, d| A |)::x1).
    rewrite H3...
    decide3(RINIT OO).
    tensor [u| OO|] (@nil oo).
    init2 x0 L.
    assert(a <> loc).
    intro... SLSolve.
    decide3(ModalDefs C Right A a).
    constructor;constructor;auto.
    tensor [u| t_ucon C A |] (@nil oo).
    apply GenK4Rel' with (C4:= [(a, d| A |)]) (CK:=[]) (CN:=L)...
    SLSolve.
    simpl;split;SLSolve. assumption.
    solveLL.
    rewrite plustpropT...
    decide3(RINIT A).
    apply ooth_init...
    OLSolve.
    tensor [u| A |] (@nil oo).  
    rewrite (allU a)...
    init2 a (@nil (subexp*oo)).
    
    apply in_app_or in H6;CleanContext.
    
    decide3(RINIT OO).
    tensor (@nil oo) [d| OO |] .
    apply InPermutation in H3...
    init2 x0  ((a, d| A |)::x1).
    rewrite H3...
    
    apply in_app_or in H6;CleanContext.
    apply in_app_or in H4;CleanContext.
     
    decide3(RINIT OO).
    tensor (@nil oo) (@nil oo).
    apply InPermutation in H3...
    init2 x1  ((a, d| A |)::x2).
    rewrite H3...
    
    apply InPermutation in H6...
    init2 x0  ((a, d| A |)::x2).
    rewrite H4...
    
    decide3(RINIT OO).
    tensor (@nil oo) (@nil oo).
    apply InPermutation in H3...
    init2 x1  ((x0, d| OO |)::x2).
    rewrite H3...
    init2 x0 L.
    assert(a <> loc).
    intro... SLSolve.
    decide3(ModalDefs C Right A a).
    constructor;constructor;auto.
    tensor (@nil oo) (@nil oo).
    apply InPermutation in H3...
    init2 x1 ((a, d| A |)::x0).
    rewrite H3...
    
    apply GenK4Rel' with (C4:= [(a, d| A |)]) (CK:=[]) (CN:=L)...
    SLSolve.
    simpl;split;SLSolve. assumption.
    solveLL.
    rewrite plustpropT...
    decide3(RINIT A).
    apply ooth_init...
    OLSolve.
    tensor [u| A |] (@nil oo).  
    rewrite (allU a)...
    init2 a (@nil (subexp*oo)).
 - apply FocusingPOSU in H3...
   rewrite app_comm_cons in H9.
   apply H in H9...
   decide3(POS OO loc).
   tensor [d| OO |] x1.
   OLSolve.
   apply in_app_or in H8;CleanContext.
   
   rewrite app_comm_cons in H10.
   apply H in H10...
   decide3(POS OO loc).
   tensor (@nil oo) N.
   apply InPermutation in H3...
   init2 x1 ((a, d| A |)::x).
   rewrite H3...
   rewrite app_comm_cons in H10.
   apply H in H10...
   apply ContractionL'...
   LLExact H10.
   
   assert(seqN (TH a) x0 (L ++ [(a, d| A |); (loc, d| t_ucon C A |)]) N (> [])).
   apply contractionN with (F:=(loc, d| t_ucon C A |))...
   apply in_or_app.
   right. firstorder. 
   apply H in H3...
 - apply FocusingNEGU in H3...
   rewrite app_comm_cons in H9.
   apply H in H9...
   decide3(NEG OO loc).
   tensor [u| OO |] x1.
   OLSolve.
   apply in_app_or in H8;CleanContext.
   
   rewrite app_comm_cons in H10.
   apply H in H10...
   decide3(NEG OO loc).
   tensor (@nil oo) N.
   apply InPermutation in H3...
   init2 x1 ((a, d| A |)::x).
   rewrite H3...
 Qed.  
  

  Theorem CutElimination:
    forall n a i j FC L M N,
    isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    SetU L ->
    mt a = true -> u a = true -> 
    (seqN  (TH a) i L (u|FC|::M)  (> []) -> 
    seqN  (TH a) j L (d|FC|::N)  (> []) ->
    seq   (THC a n) L (M ++ N)  (> [])) /\
   ( seqN  (TH a) i ((loc,u|FC|)::L) M  (> []) -> 
    seqN  (TH a) j ((loc,d|FC|)::L) N  (> []) ->
    seq   (THC a n) L (M++N)  (> [])).
  Proof with CutTacPOSNEG.
    intros.
    remember (plus i j) as h.
    revert dependent L.
    revert dependent M.
    revert dependent N.
    revert dependent FC.
    revert dependent i.
    revert j n.
    
      induction h using strongind;intros *.
   -  intros... 
      -- intros;sauto.
         symmetry in Heqh.
         apply plus_is_O in Heqh.
         destruct Heqh;subst.
         inversion H7.
      -- intros;sauto.
         symmetry in Heqh.
         apply plus_is_O in Heqh.
         destruct Heqh;subst.
         inversion H7.
    -   intros Heqh FC isFFC lngF N isFN M isFM L isFL sUL.
        split;intros Hi Hj.
    + (* First CUT *)        
        move L at top.
        move M at top.
        move N at top.
        move FC at top.
       assert(CutL h a).
       unfold CutL;intros.
       
       assert((seqN (TH a) i0 L0 (u| FC0 | :: M0) (> []) ->
       seqN (TH a) j0 L0 (d| FC0 | :: N0) (> []) -> seq (THC a n0) L0 (M0 ++ N0) (> []))).
       eapply H with (m:=m)...
       apply H12...
       assert(CutC h a).
       unfold CutC;intros.
       
       assert((seqN (TH a) i0 ((loc, u| FC0 |) :: L0) M0 (> []) ->
       seqN (TH a) j0((loc, d| FC0 |) :: L0) N0 (> []) -> seq (THC a n0) L0 (M0 ++ N0) (> []))).
       eapply H with (m:=m)...
       apply H13...
       
        clear H.
                 
        rename H0 into CutHL.
        rename H1 into CutHC.
        inversion Hi;sauto.
        apply RemoveNotPos1 in H0;sauto...
        apply InUNotPos in H2;sauto...
        apply RemoveNotPos2 in H2;sauto...
        inversion Hj;sauto.
        
        apply RemoveNotPos1 in H3;sauto...
        apply InUNotPos in H7;sauto...
        apply RemoveNotPos2 in H7;sauto...
  
        inversion H;sauto.
     
     * inversion H7;sauto.
      ** apply FocusingRightRuleU in H1;sauto.
      2:{   
       apply AppPARTENSORRight in H13;sauto.
       decide3 (ConjunctionDefs C Right F1 G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       ---
       rewrite app_comm_cons.
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x1) (m:=x1 + (S n1))...
       LLExact H13.
      ---
      rewrite app_comm_cons.
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x1) (m:=x1 + (S n1))...
      LLExact H14. } 
   
        checkPermutationCases H11.
        
       2:{  rewrite H10.
       apply AppPARTENSORRight in H12;sauto.
       decide3 (ConjunctionDefs C Right F1 G).
       constructor;sauto.
       tensor [u| t_bin C F1 G |] (x1 ++ N).
       CleanContext.
       ---
        rewrite app_comm_cons. 
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x2) (m:=x2 + (S n1))... 
       LLExact H13. 
       rewrite H9... 
       ---
       rewrite app_comm_cons.
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x2) (m:=x2 + (S n1))... 
       LLExact H14.
       rewrite H9...   }
       
       { (* AND PRINCIPAL ON THE LEFT *)
       inversion H9;sauto.
       inversion H2;sauto.
       - inversion H1;sauto.
         --
        apply FocusingRightRuleU in H4;sauto.
        { checkPermutationCases H14.
          apply AppPARTENSORRight in H15;sauto.
          decide3 (ConjunctionDefs C0 Right F G0).
       constructor;sauto.
       tensor [u| t_bin C0 F G0 |] (M ++ x3).
       rewrite H13;sauto.
       ---
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x4) (m:=S (S x) + x4) ...
       OLSolve.
       LLExact H16.
       rewrite H11... 
       ---
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x4) (m:=S (S x) + x4)...
        OLSolve.
       LLExact H17.
       rewrite H11...  } 
      {  
       apply AppPARTENSORRight in H16;sauto.
           decide3 (ConjunctionDefs C0 Right F G0).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       ---
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x3) (m:=S (S x) + x3) ;sauto...
       OLSolve.
       LLExact H16.
       ---
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x3) (m:=S (S x) + x3) ;sauto...
       OLSolve.
       LLExact H17. } 
      --
      apply FocusingLeftRuleU in H4;sauto.
        {
        checkPermutationCases H14.
        
       2:{
       apply AppPARTENSORLeft in H15;sauto.
       ---
       decide3 (ConjunctionDefs C0 Left F G0).
       constructor;sauto.
       tensor [d| t_bin C0 F G0 |] (M ++ x3).
       rewrite H13. perm.
       oplus1.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x4) (m:=S (S x) + x4) ;sauto...
       OLSolve.
       LLExact H15.
       rewrite  H11...
       ---
       decide3 (ConjunctionDefs C0 Left F G0).
       constructor;sauto.
       tensor [d| t_bin C0 F G0 |] (M ++ x3).
       rewrite H13. perm.
       oplus2.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x4) (m:=S (S x) + x4) ;sauto...
       OLSolve. LLExact H15.
       rewrite H11... }
      {  
     inversion H11;sauto.
     apply AppPARTENSORRight in H12;sauto.
     apply AppPARTENSORLeft in H15;sauto.
    inversion lngF;sauto.
    
     assert(seq (THC a n1) L (M ++ N) (> [])).
    eapply CutHL with (FC:=F) (i:=x3) (j:=x) (m:=x3+x);sauto...
    OLSolve.
    LLExact H12.
    LLExact H11.
    eapply CutRuleNBound' with (n:=n1)...
    inversion lngF;sauto.
    
     assert(seq (THC a n2) L (M ++ N) (> [])).
    eapply CutHL with (FC:=G0) (i:=x3) (j:=x) (m:=x3+x);sauto...
    OLSolve.
    LLExact H14.
    LLExact H11.
    eapply CutRuleNBound' with (n:=n2)... } }
    ---
       apply AppPARTENSORLeft in H16;sauto.
    {
       decide3 (ConjunctionDefs C0 Left F G0).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       oplus1.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x3) (m:=S (S x) + x3) ;sauto...
       OLSolve.
       LLExact H15. }
    {
       decide3 (ConjunctionDefs C0 Left F G0).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       oplus2.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
       eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x3) (m:=S (S x) + x3) ;sauto...
       OLSolve.
       LLExact H15. }
    --
    apply FocusingRightMU in H4; sauto.
    --
    apply FocusingLeftMU in H4; sauto.
    {
        checkPermutationCases H15.
         decide3 (ModalDefs C0 Left A a).
       constructor;sauto.
       tensor [d| t_ucon C0 A |] (M ++ x3).
       rewrite H14;perm.
        simpl;solveLL.
     eapply CutHL with (FC:= t_bin C F1 G) (j:=x1) (i:=S (S x) ) (m:= S (S x)+x1) ;sauto...
     OLSolve.
     apply weakeningN;sauto.
          LLExact H16;simpl;sauto. }
    {   
     decide3 (ModalDefs C0 Left A a).
       constructor;sauto.
       tensor (@nil oo)(M ++ N).
     eapply CutHL with (FC:= t_bin C F1 G) (j:=x1) (i:=S (S x) ) (m:= S (S x)+x1) ;sauto...
     OLSolve.
     apply weakeningN;sauto.
          LLExact H17;simpl;sauto. } 
     - 
      apply FocusingInitRuleU in H4;sauto.    
       -- checkPermutationCases H9. inversion H9;sauto.
       eapply WeakTheory with (th:=(TH a)).
       apply TheoryEmb1.
       apply seqNtoSeq in Hi.
       LLExact Hi.
       -- inversion H9;sauto.
      apply InPermutation in H13;sauto.
       rewrite H4.
       eapply @seqNtoSeq with (n:=(S (S x))).
       apply AbsorptionC;sauto.
       apply allU.
       rewrite <- H4.
       LLExact Hi.
         eapply WeakTheoryN with (th:=(TH a)).
      apply TheoryEmb1.
       LLExact Hi.
     -  apply FocusingPOSU in H4;sauto.    
       -- checkPermutationCases H15.
          2:{ 
            decide3 (POS OO loc).
           apply oothc_pos;sauto. 
        
       tensor [d| OO|] (M++ x3).
       rewrite H14;perm.
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x1) (m:=S (S x) + x1) ;sauto...
        OLSolve.
       apply weakeningN;sauto.
       LLExact H16. }
       { inversion H13;sauto.
         eapply CutHC with (FC:=t_bin C F1 G) (i:=S (S x)) (j:=x1) (m:=S (S x) + x1);sauto...
       apply AbsorptionL;sauto.
       LLExact H16. }
    --   decide3 (POS OO loc).
           apply oothc_pos;sauto. 
        
       tensor (@nil oo) (M ++ N).
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x1) (m:=S (S x) + x1) ;sauto...
        OLSolve.
       apply weakeningN;sauto.
  -  apply FocusingNEGU in H4;sauto.    
       -- checkPermutationCases H15.
            decide3 (NEG OO loc).
           apply oothc_neg;sauto. 
        
       tensor [u| OO|] (M ++ x3).
      rewrite H14;perm.
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x1) (m:=S (S x) + x1) ;sauto...
        OLSolve.
       apply weakeningN;sauto.
       LLExact H16.
       -- 
      decide3 (NEG OO loc).
           apply oothc_neg;sauto. 
        
       tensor (@nil oo) (M ++ N).
      
        eapply CutHL with (FC:=t_bin C F1 G) (i:=S (S x)) (j:= x1) (m:=S (S x) + x1) ;sauto...
        OLSolve.
       apply weakeningN;sauto. }   
  ** apply FocusingLeftRuleU in H1;sauto.
      2:{   
      apply AppPARTENSORLeft in H13;sauto.
      --
       decide3 (ConjunctionDefs C Left F1 G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       simpl;oplus1.
       rewrite app_comm_cons. 
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x1) (m:=x1 + (S n1)) ;sauto...
       OLSolve.
      LLExact H12.
      --
       decide3 (ConjunctionDefs C Left F1 G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       simpl;oplus2.
      rewrite app_comm_cons. 
        eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x1) (m:=x1 + (S n1)) ;sauto...
        OLSolve.
      LLExact H12. } 
   
        checkPermutationCases H11.
       apply AppPARTENSORLeft in H12;sauto.
       ---
       decide3 (ConjunctionDefs C Left F1 G).
       constructor;sauto.
       tensor [d| t_bin C F1 G |] (x1 ++ N).
       CleanContext.
       rewrite H10;perm.
       simpl;oplus1.
       rewrite app_comm_cons. 
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x2) (m:=x2 + (S n1)) ;sauto...
       OLSolve.
       LLExact H12.
       rewrite H9. perm.
     ---  
       decide3 (ConjunctionDefs C Left F1 G).
       constructor;sauto.
       tensor [d| t_bin C F1 G |] (x1 ++ N).
       CleanContext.
       rewrite H10;perm.
       simpl;oplus2.
       rewrite app_comm_cons. 
       eapply CutHL with (FC:=FC) (j:=(S n1)) (i:= x2) (m:=x2 + (S n1)) ;sauto...
       OLSolve.
       LLExact H12.
       rewrite H9. perm.
  ** inversion H2;sauto. 
     -- inversion H5;sauto. 
     --- 
        apply FocusingRightRuleU in H4;sauto.
        ----
         checkPermutationCases H14.
       apply AppPARTENSORRight in H15;sauto.
       decide3 (ConjunctionDefs C0 Right F G).
       constructor;sauto.
       tensor [u| t_bin C0 F G |] (M ++ x1).
       rewrite H13;perm.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
    eapply CutHL with (FC:=FC) (i:=S n0) (j:= x2) (m:=(S n0)+x2);sauto...
    OLSolve.
      LLExact H16.
      rewrite H12. perm.
      rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
   
    eapply CutHL with (FC:=FC) (i:=S n0) (j:= x2) (m:=(S n0)+x2);sauto...
    OLSolve.
      LLExact H17.
      rewrite H12. perm.
     ---- 
      apply AppPARTENSORRight in H16;sauto.
      
        decide3 (ConjunctionDefs C0 Right F G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
     eapply CutHL with (FC:=FC) (i:=S n0) (j:= x1) (m:=(S n0)+x1);sauto...
     OLSolve.
      LLExact H16.
     rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
   
    eapply CutHL with (FC:=FC) (i:=S n0) (j:= x1) (m:=(S n0)+x1);sauto...
    OLSolve.
      LLExact H17.
  ---   apply FocusingLeftRuleU in H4;sauto.
         checkPermutationCases H14.
        2:{
           apply AppPARTENSORLeft in H15;sauto.
       -
       decide3 (ConjunctionDefs C0 Left F G).
       constructor;sauto.
       tensor [d| t_bin C0 F G |] (M ++ x1).
       rewrite H13. perm.
       simpl;oplus1.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
   
   eapply CutHL with (FC:=FC) (i:=S n0) (j:= x2) (m:=(S n0)+x2);sauto...
   OLSolve.
      LLExact H15. 
      rewrite H12. perm.
       -
       decide3 (ConjunctionDefs C0 Left F G).
       constructor;sauto.
       tensor [d| t_bin C0 F G |] (M ++ x1).
       rewrite H13. perm.
       simpl;oplus2.
       rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
   
   eapply CutHL with (FC:=FC) (i:=S n0) (j:= x2) (m:=(S n0)+x2);sauto...
      OLSolve.
      LLExact H15. 
      rewrite H12. perm. }
    
   { inversion H12;sauto.
      apply FocusingRightMU in H1;sauto. }
   {   decide3 (ConjunctionDefs C0 Left F G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
      apply AppPARTENSORLeft in H16;sauto.
       
       simpl;oplus1.
     rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
    eapply CutHL with (FC:=FC) (j:=x1) (i:= S n0) (m:=(S n0)+x1) ;sauto...
    OLSolve.
      LLExact H15.
      simpl;oplus2.
      rewrite Permutation_cons_append.
       rewrite app_assoc_reverse.
      eapply CutHL with (FC:=FC) (j:=x1) (i:= S n0) (m:=(S n0)+x1) ;sauto...
      OLSolve.
      LLExact H15.  }
   --- apply FocusingRightMU in H1;sauto.
       apply FocusingRightMU in H4;sauto.
   ---  apply FocusingLeftMU in H4;sauto.
        checkPermutationCases H14. 
      2:{ decide3 (ModalDefs C0 Left A0 a).
       constructor;sauto.
       tensor [d| t_ucon C0 A0 |] (M ++ x1).
       rewrite H9. perm.
      eapply CutHL with (FC:=FC) (i:=S n0) (j:= x) (m:=(S n0)+x);sauto...
      OLSolve.
      apply weakeningN;sauto.
      LLExact H15. }
      
      inversion H8;CleanContext.
      apply FocusingRightMU in H1;CleanContext.
      inversion H14;sauto.
      rewrite <- (app_nil_r N).
      eapply @GeneralCut' with (C:=((a ! u| A |))^);sauto.
      2:{ rewrite  <- ng_involutive;auto.
          eapply WeakTheory.
          2:{ apply seqNtoSeq in H16. exact H16. }
          apply TheoryEmb1. }
          rewrite <- (app_nil_l N).
       eapply @GeneralCut' with (C:=((a ? d| A |))^);sauto.
      2:{ rewrite  <- ng_involutive;auto.
          solveLL.
          rewrite H9.
          eapply WeakTheory.
          2:{ rewrite Permutation_cons_append. apply seqNtoSeq in H15.  exact H15. }
          apply TheoryEmb1. }
          
      (* CUT COHERENCE *)
      { simpl;solveLL.
      decide1.
      intro;subst;SLSolve.
      copyK4 a (u^| A |) L.
      finishExp.
      inversion lngF;sauto.
      assert(seq (THC a n1) [(plust a, u^| A |)] [d^| A |] (> [])).
      { decide3(CUTL A).
      apply oothc_cutln;auto.
      eapply ltn with (m:=n1)...
      tensor [d^| A |] (@nil oo).
      rewrite allU.
      CleanContext.
      decide1 (d^| A |).
      decide2u (plust a) (u^| A |)...
      SLSolve. SLSolve. }
       eapply CutRuleNBound'.
      exact H1. lia. }
      (* END COHERENCE *)
      
     decide3 (ModalDefs C0 Left A0 a).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
       simpl;solveLL.
    eapply CutHL with (FC:=FC) (j:=x) (i:= S n0) (m:=(S n0)+x) ;sauto...
       apply weakeningN...
      LLExact H16.
-- apply FocusingInitRuleU in H4;sauto.
   --- checkPermutationCases H11.
       inversion H11;sauto.
       eapply WeakTheory with (th:=(TH a)).
       apply TheoryEmb1.
       apply seqNtoSeq in Hi.
       LLExact Hi.
   --- inversion H11;sauto.
       apply InPermutation in H13;sauto.
       rewrite H4.
       eapply @seqNtoSeq with (n:=S n0).
       apply AbsorptionC;sauto.
       apply allU.
       rewrite <- H4.
       eapply WeakTheoryN with (th:=(TH a)).
      apply TheoryEmb1.
       LLExact Hi.
 --  apply FocusingPOSU in H4;sauto.    
      --- checkPermutationCases H15.
      inversion H13;sauto.
      eapply CutHC with (FC:=OO) (i:=S n0) (j:=x) (m:=S n0 + x);sauto.
       apply AbsorptionL;sauto.
       LLExact H16.
       
       decide3 (POS OO loc).
       apply oothc_pos;sauto. 
        
       tensor [d| OO|] (M++ x1).
       rewrite H14;perm.
        eapply CutHL with (FC:=FC) (i:=S n0) (j:= x) (m:=S n0 + x) ;sauto...
       apply weakeningN;sauto.
       LLExact H16. 
       --- 
       decide3 (POS OO loc).
           apply oothc_pos;sauto. 
        
       tensor (@nil oo) (M ++ N).
        eapply CutHL with (FC:=FC) (i:=S n0) (j:= x) (m:=S n0 + x) ;sauto...
       apply weakeningN;sauto. 
  --  apply FocusingNEGU in H4;sauto.    
      --- checkPermutationCases H15.
    
       decide3 (NEG OO loc).
       apply oothc_neg;sauto. 
        
       tensor [u| OO|] (M++ x1).
       rewrite H14;perm.
        eapply CutHL with (FC:=FC) (i:=S n0) (j:= x) (m:=S n0 + x) ;sauto...
       apply weakeningN;sauto.
       LLExact H16. 
       --- 
       decide3 (NEG OO loc).
           apply oothc_neg;sauto. 
        
       tensor (@nil oo) (M ++ N).
        eapply CutHL with (FC:=FC) (i:=S n0) (j:= x) (m:=S n0 + x) ;sauto...
       apply weakeningN;sauto.    
 **  apply FocusingLeftMU in H1;sauto.
     checkPermutationCases H12.
     decide3(ModalDefs C Left A a).
     constructor;auto.
     tensor [d| t_ucon C A |] (x1++N).
     rewrite H11;perm.
     eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
     LLExact H13.
     apply weakeningN;sauto.
     decide3(ModalDefs C Left A a).
     constructor;auto.
     tensor (@nil oo) (M++N).
     eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
     LLExact H14.
     apply weakeningN;sauto.
  *  apply FocusingInitRuleU in H1;sauto.
     -- checkPermutationCases H8.
       inversion H9;sauto.
       decide3 F0.
       apply  TheoryEmb1. exact H2.
       eapply WeakTheory with (th:=(TH a)).
       apply TheoryEmb1.
       apply seqNtoSeq in H4.
       LLExact H4.
    -- inversion H8;sauto.
       apply InPermutation in H10;sauto.
       rewrite H1.
       eapply @seqNtoSeq with (n:=S n1).
       apply AbsorptionC;sauto.
       rewrite <- H1.
       eapply WeakTheoryN with (th:=(TH a)).
      apply TheoryEmb1.
       LLExact Hj.
  *   apply FocusingPOSU in H1;sauto.    
      --- checkPermutationCases H12.
      decide3(POS OO loc).
      apply oothc_pos;auto.
      tensor [d| OO |] (x1++N).
     rewrite H11;perm.
     eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
     LLExact H13.
     apply weakeningN;sauto.
     ---
       decide3(POS OO loc).
      apply oothc_pos;auto.
     tensor (@nil oo) (M++N).
     eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
     apply weakeningN;sauto.    
  *   apply FocusingNEGU in H1;sauto.    
      --- checkPermutationCases H12.
          inversion H10;sauto.
          eapply CutHC with (FC:=OO) (i:=x) (j:=S n1) (m:=x+S n1);sauto.
          LLExact H13.
          apply AbsorptionL;sauto.
          decide3 (NEG OO loc).
          apply oothc_neg;sauto. 
          tensor [u| OO|] (x1++ N).
          rewrite H11;perm.
        eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
       LLExact H13. 
       apply weakeningN;sauto. 
       --- 
    decide3(NEG OO loc).
      apply oothc_neg;auto.
     tensor (@nil oo) (M++N).
     eapply CutHL with (FC:=FC) (i:=x) (j:= S n1) (m:=x+S n1) ;sauto...
     apply weakeningN;sauto.  
  
  + (* CASE CLASSIC *)  
    
     assert(CutL h a).
       unfold CutL;intros.
       
       assert((seqN (TH a) i0 L0 (u| FC0 | :: M0) (> []) ->
       seqN (TH a) j0 L0 (d| FC0 | :: N0) (> []) -> seq (THC a n0) L0 (M0 ++ N0) (> []))).
       eapply H with (m:=m)...
       apply H12...
       assert(CutC h a).
       unfold CutC;intros.
       
       assert((seqN (TH a) i0 ((loc, u| FC0 |) :: L0) M0 (> []) ->
       seqN (TH a) j0((loc, d| FC0 |) :: L0) N0 (> []) -> seq (THC a n0) L0 (M0 ++ N0) (> []))).
       eapply H with (m:=m)...
       apply H13...
       
        clear H.
                 
        rename H0 into CutHL.
        rename H1 into CutHC.

        inversion Hi;sauto.
        apply RemoveNotPos1 in H0;sauto...
        apply InUNotPos in H2;sauto...
        apply RemoveNotPos2 in H2;sauto...
        2:{ rewrite allNoD in H0;CleanContext. }
        inversion Hj;sauto.
        apply RemoveNotPos1 in H3;sauto...
        apply InUNotPos in H7;sauto...
        apply RemoveNotPos2 in H7;sauto...
        2:{ rewrite allNoD in H3;CleanContext. }
    inversion H2;sauto.    
     * inversion H7;sauto.
      ** apply FocusingRightRuleU in H4;sauto.
      2:{   
       apply AppPARTENSORRight in H13;sauto.
       inversion H11;sauto.
       decide3 (ConjunctionDefs C Right F1 G).
       constructor;sauto.
       tensor (@nil oo) (M ++ N).
      ---
      rewrite Permutation_cons_append.
      rewrite app_assoc_reverse.
       eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
       OLSolve.
       LLExact H13.
      ---
       rewrite Permutation_cons_append.
      rewrite app_assoc_reverse.
       eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
       OLSolve.
     LLExact H14.
        } 
      
       rewrite H11.
       apply AppPARTENSORRight in H12;sauto.
       decide3 (ConjunctionDefs C Right F1 G).
       constructor;sauto.
       tensor [u| t_bin C F1 G |] (M ++ x0).
       CleanContext.
       ---
      rewrite Permutation_cons_append.
      rewrite app_assoc_reverse.
       eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
       OLSolve.
       LLExact H12. 
       ---
       rewrite Permutation_cons_append.
      rewrite app_assoc_reverse.
       eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
       OLSolve.
       LLExact H13. 
     ** apply FocusingLeftRuleU in H4;sauto.
        --  decide3 (ConjunctionDefs C Left F1 G).
            constructor;auto.
            tensor [d| t_bin C F1 G |] (M++x0).
            rewrite H11...
            apply AppPARTENSORLeft in H12;sauto.
            oplus1.
            rewrite Permutation_cons_append.
            rewrite app_assoc_reverse.
            eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
            OLSolve. LLExact H10.
            oplus2.
            rewrite Permutation_cons_append.
            rewrite app_assoc_reverse.
            eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:=S n0 + x1) ;sauto...
            OLSolve. LLExact H10.
       -- inversion H11;sauto.
          --- 
            inversion H;sauto.
            ++ 
            inversion H4;sauto.
            +++ 
            apply FocusingRightRuleU in H1;sauto.
            apply AppPARTENSORRight in H15;sauto.
            decide3 (ConjunctionDefs C0 Right F0 G0).
            constructor;auto.
            tensor [u| t_bin C0 F0 G0 |] (x1++N).
            rewrite H14...
            rewrite app_comm_cons.
            eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
            rewrite app_comm_cons.
            eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
            inversion H14;sauto.
            2:{  
                apply AppPARTENSORRight in H16;sauto.
                decide3 (ConjunctionDefs C0 Right F0 G0).
                constructor;sauto.
                tensor (@nil oo) (M ++ N).
             ---
             rewrite app_comm_cons.
             eapply CutHC with (FC:=t_bin C F1 G) 
            (j:=S (S x)) (i:= x2) (m:= x2 + S (S x)) ;sauto...
             ---
             rewrite app_comm_cons.
             eapply CutHC with (FC:=t_bin C F1 G) 
            (j:=S (S x)) (i:= x2) (m:= x2 + S (S x)) ;sauto... } 
           
           apply AppPARTENSORRight in H16;sauto.
           apply AppPARTENSORLeft in H13;sauto.
           { assert(Hs1: seq (THC a n) L ((u| F0 | :: M) ++ N) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=S (S (S (S (S x0))))) (i:= x1) (m:=x1+S (S (S (S (S x0))))) ;sauto...
             assert(Hs2: seq (THC a n) L ((u| G0 | :: M) ++ N) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=S (S (S (S (S x0))))) (i:= x1) (m:=x1+S (S (S (S (S x0))))) ;sauto...
             assert(Hs3: seq (THC a n) L (M ++ (d| F0 | :: N)) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=x0) (i:= S (S (S (S (S x1))))) (m:=S (S (S (S (S x1))))+x0) ;sauto...
              assert(Hp1:seq (THC a n) (CEncode loc M++CEncode loc N ++ L) [] (>> u| F0 | & u| G0 |)).
             solveLL.
             apply AbsorptionLSet'...
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs1. 
             apply AbsorptionLSet'... 
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs2.
             assert(Hp2:seq (THC a n) (CEncode loc M++CEncode loc N ++ L) [] (>> d| F0 | op d| G0 |)).
             oplus1.
             apply AbsorptionLSet'...
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs3.
             clear H11 H14 H10 Hs1 Hs2 Hs3.
             apply PosNegSetT'...
             intros... apply oothc_neg... SLSolve.
             intros... apply oothc_pos... SLSolve.
             inversion lngF...
             rewrite <- (app_nil_r []).
             eapply GeneralCut' with (C:=dual (d| F0 | op d| G0 |))...
             rewrite <- (app_nil_r []).
             eapply GeneralCut' with (C:=dual (u| F0 | & u| G0 |))...
             (* CUT COHERENCE *)
             simpl. solveLL. 
             decide3(CUTL F0 ).
             apply oothc_cutln.
             apply ltn with (m:=n1)...
             tensor [d^| F0 |] [u^| F0 | op u^| G0 |]. 
             decide1 (d^| F0 |).
             decide1(u^| F0 | op u^| G0 |).
             decide3(CUTL G0 ).
             apply oothc_cutln.
             apply ltn with (m:=n2)...
             tensor [d^| G0 |] [u^| F0 | op u^| G0 |]. 
             decide1 (d^| G0 |).
             decide1(u^| F0 | op u^| G0 |). }
           { assert(Hs1: seq (THC a n) L ((u| F0 | :: M) ++ N) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=S (S (S (S (S x0))))) (i:= x1) (m:=x1+S (S (S (S (S x0))))) ;sauto...
             assert(Hs2: seq (THC a n) L ((u| G0 | :: M) ++ N) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=S (S (S (S (S x0))))) (i:= x1) (m:=x1+S (S (S (S (S x0))))) ;sauto...
             assert(Hs3: seq (THC a n) L (M ++ (d| G0 | :: N)) (> [])).
             eapply CutHC with (FC:=t_bin C0 F0 G0) (j:=x0) (i:= S (S (S (S (S x1))))) (m:=S (S (S (S (S x1))))+x0) ;sauto...
              assert(Hp1:seq (THC a n) (CEncode loc M++CEncode loc N ++ L) [] (>> u| F0 | & u| G0 |)).
             solveLL.
             apply AbsorptionLSet'...
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs1. 
             apply AbsorptionLSet'... 
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs2.
             assert(Hp2:seq (THC a n) (CEncode loc M++CEncode loc N ++ L) [] (>> d| F0 | op d| G0 |)).
             oplus2.
             apply AbsorptionLSet'...
             apply setTCEncode...
              apply AbsorptionLSet'...
             apply setTCEncode...
             rewrite !secCEncode.
             LLExact Hs3.
             clear H11 H14 H10 Hs1 Hs2 Hs3.
             apply PosNegSetT'...
             intros... apply oothc_neg... SLSolve.
             intros... apply oothc_pos... SLSolve.
             inversion lngF...
             rewrite <- (app_nil_r []).
             eapply GeneralCut' with (C:=dual (d| F0 | op d| G0 |))...
             rewrite <- (app_nil_r []).
             eapply GeneralCut' with (C:=dual (u| F0 | & u| G0 |))...
             (* CUT COHERENCE *)
             simpl. solveLL. 
             decide3(CUTL F0 ).
             apply oothc_cutln.
             apply ltn with (m:=n1)...
             tensor [d^| F0 |] [u^| F0 | op u^| G0 |]. 
             decide1 (d^| F0 |).
             decide1(u^| F0 | op u^| G0 |).
             decide3(CUTL G0 ).
             apply oothc_cutln.
             apply ltn with (m:=n2)...
             tensor [d^| G0 |] [u^| F0 | op u^| G0 |]. 
             decide1 (d^| G0 |).
             decide1(u^| F0 | op u^| G0 |). }
          +++  apply FocusingLeftRuleU in H1;sauto.
               decide3 (ConjunctionDefs C0 Left F0 G0).
               constructor;sauto.
               tensor [d| t_bin C0 F0 G0 |] (x1++N).
               rewrite H14...
               apply AppPARTENSORLeft in H15;sauto.
               oplus1.
               rewrite app_comm_cons.
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
               oplus2.
               rewrite app_comm_cons.
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
              
               inversion H14...
               decide3 (ConjunctionDefs C0 Left F0 G0).
               constructor;sauto.
               tensor (@nil oo) (M ++ N).
               apply AppPARTENSORLeft in H16;sauto.
               oplus1.
               rewrite app_comm_cons.
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
               oplus2.
               rewrite app_comm_cons.
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x2) (m:= x2+S (S x)) ;sauto...
            +++ apply FocusingRightMU in H1...
                 apply PosNegSetT'...
               intros... apply oothc_neg... SLSolve.
               intros... apply oothc_pos... SLSolve.
                decide3 (ModalDefs C0 Right A a).
                constructor;constructor;sauto.
                tensor (@nil oo)  (@nil oo).
                CleanContext.
                init2 loc (CEncode loc N ++ L).
                intro... SLSolve.
                apply AppQUESTBANGRightLoc in H16...
                eapply @GenK4Rel' with (C4:=x2) (CK:=[]) (CN:=(loc, u| t_ucon C0 A |) :: x3++ CEncode loc N)...
                intro... SLSolve.
                rewrite H15...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H18.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H18.
                
                inversion H15...
                rewrite <- (app_nil_l N).
                apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
                decide3 (ModalDefs C0 Right A a).
                constructor;constructor;sauto.
                tensorUnb (@nil oo) (@nil oo).
                CleanContext.
                apply InPermutation in H5...
                init2 x1 (CEncode loc N ++ x2).
                rewrite H1...
                intro... SLSolve.
                apply AppQUESTBANGRightLoc in H18...
                eapply @GenK4Rel' with (C4:=x3) (CK:=[]) (CN:=x4++ CEncode loc N)...
                intro... SLSolve.
                rewrite H18...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H21.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H21.
           +++ apply FocusingLeftMU in H1...
               decide3 (ModalDefs C0 Left A a).
               constructor;constructor;sauto.
               tensor [d| t_ucon C0 A |]  (x1++N).
               rewrite H15... 
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
               LLExact H16.
               LLSwap.
               apply weakeningN...
               inversion H15...
               decide3 (ModalDefs C0 Left A a).
               constructor;constructor;sauto.
               tensor (@nil oo)  (M++N).
               eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
               LLExact H17.
               LLSwap.
               apply weakeningN...
      ++ apply FocusingInitRuleU in H1...     
         apply PosNegSetT'...
         intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
                     
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         init2 loc (CEncode loc [d| OO|] ++ CEncode loc N ++ L). 
         srewrite H9...      
         init2 loc (CEncode loc [u| OO|] ++ CEncode loc N ++ L). 
         srewrite H9...      
         inversion H12...
         apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         SLSolve.
         rewrite allSeTLEmpty...
         init2 loc ( CEncode loc N ++ L).
         apply InPermutation in H1...
         init2 x0 ((loc, u| OO |) ::CEncode loc N ++ x1).
         rewrite H1...
         
         inversion H12...
         LLPerm (N ++ LEncode [t_bin C F1 G]).
         apply PosSetP with (a:=loc)... 
                intros... apply oothc_pos... SLSolve.
         SLSolve.       
         decide3((ConjunctionDefs C Left F1 G)).
         constructor;auto.
         tensor (@nil oo) N.
         init2 loc L.
         apply seqNtoSeq in H13.
         eapply WeakTheory with (th:=(TH a)).
         apply TheoryEmb1.
         LLExact H13.
                
         apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         SLSolve.
         rewrite allSeTLEmpty...
         apply InPermutation in H1...
         init2 x0 ((loc, d| OO |) ::CEncode loc N ++ x1).
         rewrite H1...
         init2 loc ( CEncode loc N ++ L).
         
         inversion H9...
         inversion H12...
         apply AppPARTENSORLeft in H13;sauto.
           
         rewrite <- (app_nil_l N).
          apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3((ConjunctionDefs C Left F1 G)).
         constructor;auto.
         tensorUnb (@nil oo) (@nil oo).
         apply InPermutation in H1...
         init2 x0 (CEncode loc N ++ x)...
         rewrite H1...
         oplus1.
         apply AbsorptionLSet'...
         apply setTCEncode...
         CleanContext.   
         rewrite !secCEncode.
         rewrite <- (app_nil_l  (d| F1 | :: N)).
         eapply CutHC with (FC:=t_bin C F1 G) (j:=x1) (i:= S n0) (m:= S n0 + x1) ;sauto...
         rewrite <- (app_nil_l N).
          apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3((ConjunctionDefs C Left F1 G)).
         constructor;auto.
         tensorUnb (@nil oo) (@nil oo).
         apply InPermutation in H1...
         init2 x0 (CEncode loc N ++ x)...
         rewrite H1...
         oplus2.
         apply AbsorptionLSet'...
         apply setTCEncode...
         CleanContext.   
         rewrite !secCEncode.
         rewrite <- (app_nil_l  (d| G | :: N)).
         eapply CutHC with (FC:=t_bin C F1 G) (j:=x1) (i:= S n0) (m:= S n0 + x1) ;sauto...
         rewrite <- (app_nil_l N).
          apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
        decide3(RINIT OO).
        apply oothc_init;auto.
        tensorUnb (@nil oo) (@nil oo). 
        apply InPermutation in H15...
        init2 x1 (CEncode loc N ++ x2).
        rewrite H15...
        apply InPermutation in H1...
        init2 x0 (CEncode loc N ++ x2).
        rewrite H1...
   ++ apply FocusingPOSU in H1...     
      decide3(POS OO loc).
      apply oothc_pos...
      tensor [d| OO |] (x1++N).
      rewrite H14...        
      eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
      LLExact H15.      
      LLSwap.
      apply weakeningN...
      inversion H14...
        apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3(POS OO loc).
         apply oothc_pos...
         tensorUnb (@nil oo) (@nil oo).
         apply InPermutation in H1...
         init2 x1 (CEncode loc M++CEncode loc N ++ x2)...
         rewrite H1...
         LLPerm( CEncode loc M ++ CEncode loc N ++ (loc, d| OO |) :: L).
         apply AbsorptionLSet'...
         apply setTCEncode...
         apply AbsorptionLSet'...
         apply setTCEncode...
         rewrite !secCEncode.
         eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
         LLExact H16.      
         LLSwap.
      apply weakeningN...
   ++ apply FocusingNEGU in H1...     
      decide3(NEG OO loc).
      apply oothc_neg...
      tensor [u| OO |] (x1++N).
      rewrite H14...        
      eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
      LLExact H15.      
      LLSwap.
      apply weakeningN...
      CleanContext.
         eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
         LLPermH H16 ((L++[(loc, u| t_bin C F1 G |)])++[(loc, u| t_bin C F1 G |)]).
         apply ContractionLoc in H16...
         LLExact H16.
         
        apply InPermutation in H1...
        rewrite H1.
        LLPerm(x2++[(x1, u| OO |)]).
        apply ContractionL'...
        LLPerm(((x1, u| OO |) :: x2) ++ Loc [(x1, u| OO |)]).
        rewrite <- H1.
        LLPerm(Loc [(x1, u| OO |)] ++ L).
        simpl.
         eapply CutHC with (FC:=t_bin C F1 G) (j:=S (S x)) (i:= x0) (m:= x0+S (S x)) ;sauto...
         LLExact H16.      
         LLSwap.
      apply weakeningN...
    --- clear H11.  
        decide3 (ConjunctionDefs C Left F1 G).
        constructor;auto.  
        tensor (@nil oo)  (M++N).
         apply AppPARTENSORLeft in H13;sauto.
         oplus1.
         LLPerm(M++(d| F1 | :: N)).
         eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:= S n0 + x1) ;sauto...
         oplus2.
         LLPerm(M++(d| G | :: N)).
         eapply CutHC with (FC:=FC) (j:=x1) (i:= S n0) (m:= S n0 + x1) ;sauto...
     ** apply FocusingRightMU in H4;sauto.
        --  assert (a <> loc). 
           intro... SLSolve.
           apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve. SLSolve.
                intros... apply oothc_pos... SLSolve. SLSolve.
           decide3 (ModalDefs C Right A a).
            constructor;constructor;auto.
            tensorUnb (@nil oo) (@nil oo).  
            init2 loc (CEncode loc M ++ L).
            SLSolve. 
            apply AppQUESTBANGRightLoc in H13...
             eapply @GenK4Rel' with (C4:=x1) (CK:=[]) (CN:=(loc, u| t_ucon C A |) ::x2++ CEncode loc M)...
                rewrite H13...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H16.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H16.
         --  apply PosNegSetT'...
             all: CleanContext. 
             intros... apply oothc_neg... SLSolve. SLSolve.
             intros... apply oothc_pos... SLSolve. SLSolve.
               assert (a <> loc). 
            intro... SLSolve.
           decide3 (ModalDefs C Right A a).
            constructor;constructor;auto.
            tensorUnb (@nil oo) (@nil oo).  
            apply InPermutation in H4...
            init2 x0 (CEncode loc M ++ x1).
            rewrite H4...
            apply AppQUESTBANGRightLoc in H15...
             eapply @GenK4Rel' with (C4:=x2) (CK:=[]) (CN:=x3++ CEncode loc M)...
                rewrite H15...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H18.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H18.
     ** apply FocusingLeftMU in H4;sauto.
        -- 
           decide3 (ModalDefs C Left A a).
            constructor;constructor;auto.
            tensorUnb [d| t_ucon C A |] (M++x0). 
            rewrite H12... 
            eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:= S n0 + x) ;sauto...
            LLSwap.
            apply weakeningN...
            LLExact H13.
        -- CleanContext.
           2:{
           decide3 (ModalDefs C Left A a).
            constructor;constructor;auto.
            tensorUnb (@nil oo) (M++N). 
            eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:= S n0 + x) ;sauto...
            LLSwap.
            apply weakeningN...
            LLExact H14. }
            inversion H...
            ---
            inversion H4...
            ++
              apply FocusingRightRuleU in H1;sauto.
              decide3(ConjunctionDefs C0 Right F0 G).
              constructor;auto.
              tensor [u| t_bin C0 F0 G | ] (x1++N).
              rewrite H15...
              apply AppPARTENSORRight in H16...
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              apply AppPARTENSORRight in H16...
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              CleanContext.
              decide3(ConjunctionDefs C0 Right F0 G).
              constructor;auto.
              apply AppPARTENSORRight in H17...
              tensor (@nil oo) (M++N).
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
             ++
              apply FocusingLeftRuleU in H1;sauto.
              decide3(ConjunctionDefs C0 Left F0 G).
              constructor;auto.
              tensor [d| t_bin C0 F0 G | ] (x1++N).
              rewrite H15...
              apply AppPARTENSORLeft in H16...
              oplus1.
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              oplus2.
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              CleanContext.
              decide3(ConjunctionDefs C0 Left F0 G).
              constructor;auto.
              tensor (@nil oo) (M++N).
              apply AppPARTENSORLeft in H17...
              oplus1.
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
              oplus2.
              rewrite app_comm_cons.
              eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x2) (m:= x2 + (S (S (S (S x))))) ;sauto...
             ++
             apply FocusingRightMU in H1;sauto.
              apply PosNegSetT'...
             3: CleanContext. 
             intros... apply oothc_neg... SLSolve. SLSolve.
             intros... apply oothc_pos... SLSolve. SLSolve.
               assert (a <> loc). 
            intro... SLSolve.
            decide3((ModalDefs C0 Right A0 a)).
            constructor;constructor;auto.
            tensorUnb (@nil oo) (@nil oo).
            init2 loc (CEncode loc N ++ L).
            apply AppQUESTBANGRightLoc in H16...
             eapply @GenK4Rel' with (C4:=x2) (CK:=[]) (CN:=(loc, u| t_ucon C0 A0 |) :: CEncode loc N ++ x3)...
                rewrite H16...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H19.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H19.
            CleanContext.                
            2:{ rewrite <- (app_nil_l N). 
              apply PosNegSetT'...
             all: CleanContext. 
             intros... apply oothc_neg... SLSolve. 
             intros... apply oothc_pos... SLSolve. 
               assert (a <> loc). 
            intro... SLSolve.
            decide3((ModalDefs C0 Right A0 a)).
            constructor;constructor;auto.
            tensorUnb (@nil oo) (@nil oo).
            apply InPermutation in H1...
            init2 x1 (CEncode loc N ++x2).
            rewrite H1...
            apply AppQUESTBANGRightLoc in H18...
             eapply @GenK4Rel' with (C4:=x3) (CK:=[]) (CN:=CEncode loc N ++ x4)...
                rewrite H18...   
                CleanContext.
                solveLL. 
                apply seqNtoSeq in H21.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H21.  }  
               assert(a <> loc).
                 intro... SLSolve.
               inversion lngF...
               
               assert(seq (THC a n1) L [] (>> a ! u| A0 |)).
               apply AppQUESTBANGRightLoc in H18...
               rewrite H15.
               apply weakeningGen_rev...
               createWorld.
               apply @GenK4Rel' with (C4:=x2) (CK:=[]) (CN:=[])...
               CleanContext.
               solveLL.
               eapply WeakTheory with (th:=TH a).
               intros...
               apply TheoryEmb1...
               HProof.
               assert(seq (THC a n1) L N (>> a ? d| A0 |)).
               solveLL.
               LLPermH  H14 (L ++ [(a, d| A0 |)] ++ [(loc, d| t_ucon C0 A0 |)]) .
               apply aux_cut in H14...
               eapply WeakTheory with (th:=TH a).
               intros...
               apply TheoryEmb1...
               
                LLExact H14.
               rewrite <- (app_nil_l N). 
               eapply @GeneralCut' with (C:=dual (a ? d| A0|))... 
               2: eapply CutRuleNBound' with (n:=n1)...
               rewrite <- (app_nil_l []). 
               eapply @GeneralCut' with (C:=dual (a ! u| A0|))...
               2: eapply CutRuleNBound' with (n:=n1)...
               simpl. solveLL.
               decide1.
               apply GenK4Rel' with (C4:=[(a, u^| A0 |)]) (CK:=[]) (CN:=L)...
               constructor;simpl;SLSolve. 
               split;SLSolve. assumption.
               CleanContext.
               rewrite plustpropT...
               solveLL.
               eapply CutRuleNBound' with (n:=n1)...
               decide3(CUTL A0).
               apply oothc_cutln.
               eapply ltn with (m:=n1)...
               tensor [d^| A0 |] (@nil oo).
               decide1 (d^| A0 |).
               decide2u a (u^| A0 |).
         ++  apply FocusingLeftMU in H1;sauto.
             decide3(ModalDefs C0 Left A0 a).
             constructor;constructor;auto.    
             tensorUnb [d| t_ucon C0 A0 |] (x1 ++ N).
             rewrite H15...
               eapply CutHC with (FC:= t_ucon C A) (j:=S (S (S (S x)))) (i:= x0) (m:=x0 + S (S(S (S x)))) ;sauto...
             HProof.
             decide3(ModalDefs C Left A a).
             tensorUnb (@nil oo) N.
             init2 loc ( (a, d| A0 |) :: L).
             LLPerm( (a, d| A0 |) ::((loc, d| t_ucon C A |) :: L ++ [(a, d| A |)])).
             apply weakeningN...  
             CleanContext.
             decide3(ModalDefs C0 Left A0 a).
             constructor;constructor;auto.    
             tensorUnb (@nil oo) (M ++ N).
              eapply CutHC with (FC:= t_ucon C A) (j:=S (S (S (S x)))) (i:= x0) (m:=x0 + S (S(S (S x)))) ;sauto...
             HProof.
             decide3(ModalDefs C Left A a).
             tensorUnb (@nil oo) N.
            
             init2 loc ( (a, d| A0 |) :: L).
             LLPerm( (a, d| A0 |) ::((loc, d| t_ucon C A |) :: L ++ [(a, d| A |)])).
             apply weakeningN... 
        ---       
         apply FocusingInitRuleU in H1...     
         apply PosNegSetT'...
         intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
                     
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         init2 loc (CEncode loc [d| OO|] ++ CEncode loc N ++ L). 
         srewrite H5...      
         init2 loc (CEncode loc [u| OO|] ++ CEncode loc N ++ L). 
         srewrite H5...  
         CleanContext.   
         rewrite <- (app_nil_r (u| OO | :: N)). 
         apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensorUnb (@nil oo)  (@nil oo).
         init2 loc (CEncode loc N ++ L).
         apply InPermutation in H1...
         init2 x0 ((loc, u| OO |) :: CEncode loc N ++ x1).
         rewrite H1...
         
         CleanContext.
        
         decide3(POS (t_ucon C A) loc).
         apply oothc_pos... SLSolve. 
         tensor [d| t_ucon C A |] N .
         apply seqNtoSeq in Hj.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact Hj.
         
         rewrite <- (app_nil_l (d| OO | :: N)). 
         apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensorUnb (@nil oo)  (@nil oo).
         apply InPermutation in H1...
         init2 x0 ((loc, d| OO |) :: CEncode loc N ++ x1).
         rewrite H1...
         init2 loc (CEncode loc N ++ L).
         CleanContext.
         2:{ rewrite <- (app_nil_l N).
          apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve.
                intros... apply oothc_pos... SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensorUnb (@nil oo)  (@nil oo).
         apply InPermutation in H1...
         init2 x1 (CEncode loc N ++ x2).
         rewrite H1...
         apply InPermutation in H13...
         init2 x0 (CEncode loc N ++ x2).
         rewrite H5... }
          apply InPermutation in H13...
        rewrite H1.
        LLPerm(x1++[(x0, d| t_ucon C A |)]).
        apply ContractionL'...
        simpl.
        LLPerm(((x0, d| t_ucon C A |) :: x1) ++ [(loc, d| t_ucon C A |)]).
        rewrite <- H1.
         apply seqNtoSeq in Hj.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact Hj.
   --- apply FocusingPOSU in H1...  
       decide3(POS OO loc).
       apply oothc_pos...
       tensor [d| OO | ] (x1++N).   
       rewrite H15...
       eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x0) (m:= x0+(S (S (S (S x))))) ;sauto...
         LLExact H16.      
         LLSwap.
      apply weakeningN...
        CleanContext.
        decide3(POS OO loc).
       apply oothc_pos...
       tensor (@nil oo) (M++N).
       eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x0) (m:= x0+(S (S (S (S x))))) ;sauto...
         LLExact H17.      
         LLSwap.
      apply weakeningN...
   --- apply FocusingNEGU in H1...  
       decide3(NEG OO loc).
       apply oothc_neg...
       tensor [u| OO | ] (x1++N).   
       rewrite H15...
       eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x0) (m:= x0+(S (S (S (S x))))) ;sauto...
         LLExact H16.      
         LLSwap.
      apply weakeningN...
        CleanContext.
      2:{  
        decide3(NEG OO loc).
       apply oothc_neg...
       tensor (@nil oo) (M++N).
       eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x0) (m:= x0+(S (S (S (S x))))) ;sauto...
         LLExact H17.      
         LLSwap.
      apply weakeningN... }
       eapply CutHC with (FC:=t_ucon C A) (j:=(S (S (S (S x))))) (i:= x0) (m:= x0+(S (S (S (S x))))) ;sauto...
      eapply @contractionN with (F:=(loc, u| t_ucon C A |) )...    
  *     apply FocusingInitRuleU in H4...     
        rewrite H8.
         apply PosNegSetT'...
         intros... apply oothc_neg... SLSolve. SLSolve.
                intros... apply oothc_pos... SLSolve. SLSolve.
         CleanContext.            
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         init2 loc (CEncode loc [d| OO|] ++ CEncode loc M ++ L). 
         SLSolve.      CleanContext.
          init2 loc (CEncode loc [u| OO|] ++ CEncode loc M ++ L). 
         SLSolve. CleanContext.  
         
         CleanContext. 
          decide3(NEG OO loc).
       apply oothc_neg...
       tensor [u| OO | ] M.
       decide3 F.
       apply TheoryEmb1...
       apply seqNtoSeq in H1.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact H1.
     
         apply PosNegSetT'...
         intros... apply oothc_neg... SLSolve. SLSolve.
                intros... apply oothc_pos... SLSolve. SLSolve.
         CleanContext.            
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
         init2 loc (CEncode loc M ++ L). 
         SLSolve.  
         apply InPermutation in H4...
          init2 x (CEncode loc M ++ (loc, u| OO |) :: x0).
          rewrite H4... 
         
          apply PosNegSetT'...
         intros... apply oothc_neg... SLSolve. SLSolve.
                intros... apply oothc_pos... SLSolve. SLSolve.
         CleanContext. 
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensor (@nil oo)  (@nil oo).
           apply InPermutation in H4...
          init2 x (CEncode loc M ++ (loc, d| OO |) :: x0).
          rewrite H4... 
         init2 loc (CEncode loc M ++ L). 
         SLSolve.  
         
         CleanContext.
         apply InPermutation in H4...
         rewrite H4.
        LLPerm(x++[(x0, u| OO |)]).
        apply ContractionL'...
        simpl.
        LLPerm(((x0, u| OO |) :: x) ++ [(loc, u| OO |)]).
        rewrite <- H4.
         apply seqNtoSeq in Hi.
                eapply WeakTheory with (th:=(TH a)).
                apply TheoryEmb1.
                LLExact Hi.
         
         
         rewrite <- (app_nil_r M). 
         apply PosNegSetT'...
                intros... apply oothc_neg... SLSolve. SLSolve.
                intros... apply oothc_pos... SLSolve. SLSolve.
         decide3 (RINIT OO).  
         apply oothc_init...    
         tensorUnb (@nil oo)  (@nil oo).
         apply InPermutation in H4...
         init2 x0 (CEncode loc M ++ x1).
         rewrite H4...
         apply InPermutation in H10...
         init2 x (CEncode loc M ++ x1).
         rewrite H8...
   * apply FocusingPOSU in H4...
     decide3(POS OO loc).
         apply oothc_pos... 
         tensor [d| OO |] (M++x0) .
         rewrite H12...
          eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:=S n0+x) ;sauto...
         LLSwap.
         apply weakeningN...
         LLExact H13.
         CleanContext.
            eapply CutHC with (FC:=OO) (j:=x) (i:= S n0) (m:=S n0+x) ;sauto...
        apply @contractionN with (F:=(loc, d| OO |))...
          decide3(POS OO loc).
         apply oothc_pos... 
         tensorUnb (@nil oo)  (M ++ N).
          eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:=S n0+x) ;sauto...
         LLSwap.
         apply weakeningN...
         LLExact H14.
   * apply FocusingNEGU in H4...
     decide3(NEG OO loc).
         apply oothc_neg... 
         tensor [u| OO |] (M++x0) .
         rewrite H12...
          eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:=S n0+x) ;sauto...
         LLSwap.
         apply weakeningN...
         LLExact H13.
         CleanContext.
      
          decide3(NEG OO loc).
         apply oothc_neg... 
         tensorUnb (@nil oo)  (M ++ N).
          eapply CutHC with (FC:=FC) (j:=x) (i:= S n0) (m:=S n0+x) ;sauto...
         LLSwap.
         apply weakeningN...
         LLExact H14.        
  Qed.        
      
      
 (*  Theorem CutElimination:
    forall n a i j FC L M N,
    isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    SetU L ->
    mt a = true -> u a = true -> md a = false ->
    seqN  (TH a) i L (u|FC|::M)  (> []) -> 
    seqN  (TH a) j L (d|FC|::N)  (> []) ->
    seq   (THC a n) L (M ++ N)  (> []) with 
    CUTCElimination : forall n a i j FC L M N,
     isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    SetU L ->
    mt a = true -> u a = true -> md a = false ->
    seqN  (TH a) i ((loc,u|FC|)::L) M  (> []) -> 
    seqN  (TH a) j ((loc,d|FC|)::L) N  (> []) ->
    seq   (THC a n) L (M++N)  (> []).
  Proof with CutTacPOSNEG.
  *) 
  
  Theorem Corollary_CutElimination:
    forall n a FC L M N,
    isOLFormula FC ->
    lengthUexp FC n ->
    IsPositiveAtomFormulaL M -> 
    IsPositiveAtomFormulaL N -> 
    IsPositiveAtomFormulaL (second L) -> 
    SetU L ->
    mt a = true -> u a = true ->
    seq   (TH a) L (M ++ N)  (> []) <-> seq  (THC a n) L (M ++ N)  (> [])  .
  Proof with CutTacPOSNEG.
  (* TODO *)
 Abort.
End OLCutElimination.

