Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.Bipoles.

Set Implicit Arguments.


(** ** Rules of the encoded proof system *)
Section KT4InferenceRules.

Context {SI : Signature}.
Context {SY : OLSyntax}.

  Inductive ContantEnc := TOPZERO | ZEROTOP .
  
  Definition CteRulesDefs (t:ContantEnc) (s:Side):=
    match t,s with
    | TOPZERO, Left => Top
    | ZEROTOP, Left => Zero
    | TOPZERO, Right => Zero
    | ZEROTOP, Right => Top
    end.
 
  Inductive RulesEnc := PLUSWITH | WITHPLUS.
  
  Definition RulesDefs (t:RulesEnc) (s:Side) (A B : uexp)  :=
       match t,s with
      | PLUSWITH, Left => AOr (d|A|) (d|B|)
      | PLUSWITH, Right => AAnd (u|A|) ( u|B|)
      | WITHPLUS, Left => AAnd (d|A|) (d|B|)
      | WITHPLUS, Right => AOr (u|A|) ( u|B|)
      end.  

Inductive ModalEnc := QUESTBANG.
  
  Definition ModalDefs (t:ModalEnc) (i: subexp) (s:Side) (A : uexp)  :=
       match t, s with
      | QUESTBANG, Left => Quest i (d|A|)
      | QUESTBANG, Right => Bang i (u|A|)
     end.
     
     
  Class OORules :=
    {
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc;
      rulesUnary : uconnectives -> ModalEnc
    }.
  
End KT4InferenceRules.
 
Section CutCohBipoles.
  Context {SI : Signature}.
 
Inductive Constants := TT | FF.
Inductive Connectives := AND | OR.
Inductive UConnectives := BOX. 
Inductive Quantifiers := .

Global Instance SimpleOLSig : OLSyntax:=
  {|
    OLType := nat;
    constants := Constants;
    uconnectives := UConnectives;
    connectives := Connectives ;
    quantifiers := Quantifiers
  |}.
 
 Instance TT_BODY : CteBody := {
    cte := TT;
    rc_rightBody := CteRulesDefs TOPZERO Right;
    rc_leftBody := CteRulesDefs TOPZERO Left
  }.
  
 Instance FF_BODY : CteBody := {
    cte := FF;
    rc_rightBody := CteRulesDefs ZEROTOP Right;
    rc_leftBody := CteRulesDefs ZEROTOP Left
  }.
  
 Instance AND_BODY : BinBody := {
    con := AND;
    rb_rightBody := RulesDefs PLUSWITH Right;
    rb_leftBody := RulesDefs PLUSWITH Left
  }.
  
 Instance OR_BODY : BinBody := {
    con := OR;
    rb_rightBody := RulesDefs WITHPLUS Right;
    rb_leftBody := RulesDefs WITHPLUS Left
  }.
 
 Instance BOX_BODY i: UnBody := {
    ucon := BOX;
    ru_rightBody := ModalDefs QUESTBANG i Right ;
    ru_leftBody := ModalDefs QUESTBANG i Left
  }.
  
  Section CutCoherence.
  
Instance TT_CUTCOHERENT : CteCutCoherent TT_BODY .
Proof.
   constructor.
   simpl. solveLL.
 Defined.  
 
  
Instance FF_CUTCOHERENT : CteCutCoherent FF_BODY .
Proof. 
   constructor.
   simpl. solveLL. 
 Defined.
  
  
Instance AND_CUTCOHERENT : BinCutCoherent (RCUT:=CUTLN) AND_BODY .
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl. 
  LLStore.
  LLWith.
  all: LLStore.
  -  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H.
      LLTensor [d^| F |] [AOr (u^| F |) (u^| G |)]. 
             LLRelease. solveLL.
             LLRelease. solveLL.
             LFocus(AOr (u^| F |) (u^| G |)) [u| F |].
   -  TFocus(CUTL G ).
      apply ltn with (m:=m)...
      inversion H.
      LLTensor [d^| G |] [AOr (u^| F |) (u^| G |)]. 
             LLRelease. solveLL.
             LLRelease. solveLL.
             LFocus(AOr (u^| F |) (u^| G |)) [u| G |]. 
 Defined.  
 
 
Instance OR_CUTCOHERENT : BinCutCoherent (RCUT:=CUTLN) OR_BODY .
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl. 
  LLWith.
  all: do 2 LLStore.
  -  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H.
      LLTensor  [AOr (d^| F |) (d^| G |)] [u^| F |]. 
             LLRelease. LLStore.
             LFocus(AOr (d^| F |) (d^| G |)) [d| F |].
             LLRelease. solveLL.
   -  TFocus(CUTL G ).
      apply ltn with (m:=m)...
      inversion H.
      LLTensor  [AOr (d^| F |) (d^| G |)] [u^| G |]. 
             LLRelease. LLStore.
             LFocus(AOr (d^| F |) (d^| G |)) [d| G |]. 
             LLRelease. solveLL.
    Defined.       

Instance BOX_CUTCOHERENT {UNB: UnbSignature} i : m4 i = true -> mt i = true -> UnCutCoherent (RCUT:=CUTLN) (BOX_BODY i).
Proof with sauto. 
  constructor.
  intros *. intros lenF isFF.
  simpl.
  LLStoreC.
  LLStore.
  LFocus. createWorld.
  solveSignature1.
  copyK4 i (u^|F |) (@nil TypedFormula).
  reflexivity.
  finishExp.
  rewrite plustpropT...
  LLStore.
  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H1.
  LLTensor [d^|F|]  (@nil oo). 
  all: LLRelease; LLStore;solveLL.
  UFocus; apply allU.
  Defined.          
  
End CutCoherence.

  Inductive buildTheoryCons : oo ->  Prop := 
  | cteTTR : isOLFormula (t_cons TT_BODY.(cte)) -> 
        buildTheoryCons (CteBipole TT_BODY Right)
  | cteTTL : isOLFormula (t_cons TT_BODY.(cte)) -> 
        buildTheoryCons (CteBipole TT_BODY Left)
  | cteFFR : isOLFormula (t_cons FF_BODY.(cte)) -> 
        buildTheoryCons (CteBipole FF_BODY Right)
  | cteFFL : isOLFormula (t_cons FF_BODY.(cte)) -> 
        buildTheoryCons (CteBipole FF_BODY Left).

Inductive buildTheory : oo ->  Prop :=  
  | bconANDR : forall F G, 
          isOLFormula ( t_bin AND_BODY.(con) F G) ->
          buildTheory  (BinBipole AND_BODY Right F G) 
  | bconANDL : forall F G, 
          isOLFormula ( t_bin AND_BODY.(con) F G) ->
          buildTheory  (BinBipole AND_BODY Left F G)          
  | bconORR : forall F G, 
          isOLFormula ( t_bin OR_BODY.(con) F G) ->
          buildTheory  (BinBipole OR_BODY Right F G) 
  | bconORL : forall F G, 
          isOLFormula ( t_bin OR_BODY.(con) F G) ->
          buildTheory  (BinBipole OR_BODY Left F G).
       
  Inductive buildTheoryM {a: subexp}: oo ->  Prop := 
  | mdBOXR : forall F,  mt a = true -> m4 a = true ->
    isOLFormula (t_ucon (BOX_BODY a).(ucon) F) -> 
              buildTheoryM (UnBipole (BOX_BODY a) Right F)
  | mdBOXL : forall F,  mt a = true -> m4 a = true ->
    isOLFormula (t_ucon (BOX_BODY a).(ucon) F) -> 
              buildTheoryM (UnBipole (BOX_BODY a) Left F).
    
              
 (** A theory containing only the logical rules and init *)
  Inductive KT4Theory {a:subexp} : oo -> Prop :=
  | ooth_consC : forall OO, buildTheoryCons OO ->  KT4Theory OO
  | ooth_rulesC : forall OO, buildTheory OO ->  KT4Theory OO
  | ooth_initC : forall OO, isOLFormula OO -> KT4Theory (RINIT OO)
  | ooth_boxC : forall OO, buildTheoryM (a:=a) OO -> KT4Theory OO
  | ooth_posC : forall OO,  isOLFormula OO -> KT4Theory (POS OO loc) 
  | ooth_negC : forall OO, isOLFormula OO -> KT4Theory (NEG OO loc) 
.          

 (** A theory containing the logical rules, init and cut *)
  Inductive KT4TheoryCut (n:nat) {a:subexp} : oo -> Prop :=
  | oothc_consC : forall OO, buildTheoryCons OO ->  KT4TheoryCut n OO
  | oothc_rulesC : forall OO, buildTheory OO ->  KT4TheoryCut n OO
  | oothc_initC : forall OO, isOLFormula OO -> KT4TheoryCut n (RINIT OO)
  | oothc_boxC : forall OO, buildTheoryM (a:=a) OO -> KT4TheoryCut n OO
  | oothc_posC : forall OO,  isOLFormula OO -> KT4TheoryCut n (POS OO loc) 
  | oothc_negC : forall OO, isOLFormula OO -> KT4TheoryCut n (NEG OO loc) 
  | oothc_cutln : forall OO, CUTLN n (CUTL OO) -> KT4TheoryCut n (CUTL OO).
  
 Lemma CuteRuleNBound {SIU: UnbSignature}: forall h n B L X ,  seqN (CUTLN n) h B L X ->
                                             forall m, n<=m -> seq (CUTLN m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (CUTLN n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (CUTLN m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n) ;solveF
                   );clear Hs
             end;try solveLL;auto.
    -         
    rewrite H3. 
    LLTensor M N B0 D.
    - 
    LFocus F ;eauto.
    -
    UFocus i F;eauto ...
    -
    BFocus i F;eauto ...
    -
    TFocus F;eauto ...
    inversion H3...
    apply @ltn with (m:= m0)...
    -
    LLExists t.
    -
    apply H4 in properX...
    eapply H  with (m:= h) (n:= n) ;solveF.
    - 
   apply InvSubExpPhaseU in H4...
   2:{ apply allU. }
   createWorld.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia.              
    - 
   apply InvSubExpPhaseU in H3...
   2:{ apply allU. }
   createWorld i.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    solveSignature1.
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia. solveSignature1.
  Qed.
  
  
  Lemma CuteRuleN : forall n F, CUTLN n F ->
                                             forall m, n<=m -> CUTLN m F.
  Proof with sauto.
    intros.
    inversion H...
    econstructor;eauto.
    (transitivity n);auto.
  Qed.

  Lemma CuteRuleNBound' {USI: UnbSignature}: forall n B L X ,
      seq (CUTLN n)  B L X ->
      forall m, n<=m -> seq (CUTLN m) B L X .
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CuteRuleNBound;eauto.
  Qed.
  
 (** There are no (object logic) formulas of size 0 *)
  Lemma CuteRuleN0 : forall F, ~ (CUTLN 0 F).
  Proof with solveF.
    intros F Hn.
    inversion Hn...
    generalize (LengthFormula H H0); intro.
    lia.
  Qed.
  
 Definition KT4 i := KT4Theory (a:=i).
 Definition KT4C i n := KT4TheoryCut (a:=i) n.
 
 Local Hint Constructors  KT4TheoryCut KT4Theory  : core.
 Local Hint Unfold RINIT CUTL CUTC  : core.
 Local Hint Unfold KT4 KT4C : core.

Lemma CutRuleNBound {SIU: UnbSignature}: forall h i n B L X ,  seqN (KT4C i n) h B L X ->
                         forall m, n<=m -> seq (KT4C i m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i0 C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (KT4C i n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (KT4C i m) B1 N1 X1) by
                   (
                     eapply H  with (m:= h) (n:= n)  (B:= B1);solveF 
                   );clear Hs
             end;solveLL;auto.
    -         
    rewrite H3. LLTensor M N B0 D.
    -
    LFocus F ;eauto.
    -
    UFocus i0 F;eauto ...
    -
    BFocus i0 F;eauto ...
    -
    TFocus F;eauto ...
    unfold KT4C in H3.
    unfold KT4C.
    inversion H3...
    eapply oothc_cutln.
     eapply CuteRuleN;eauto.
    -
    LLExists t.
    -
    apply H4 in properX.
     eapply H  with (m:= h) (n:= n)  ;solveF.
    - 
       apply InvSubExpPhaseU in H4...
   2:{ apply allU. }
   createWorld.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia.              
    - 
   apply InvSubExpPhaseU in H3...
   2:{ apply allU. }
   createWorld i0.
    eapply @GenK4RelU' with (C4:=x) (CK:=x0) (CN:=x1)...
    solveSignature1.
    eapply H  with (m:= h) (n:= n) ;solveF.
    eapply HeightGeq. exact H14.
    lia. solveSignature1.
   Qed. 

 
  Lemma CutRuleNBound' {SIU: UnbSignature}:  forall i n B L X ,  
  seq (KT4C i n)  B L X ->
                         forall m, n<=m -> seq (KT4C i m) B L X .
  Proof with solveF.
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CutRuleNBound;eauto.
    
  Qed.
  
  (** Some easy equivalences on the  above theories *)
 Lemma OOTheryCut0 : forall i F, 
 KT4 i F <-> (KT4C i 0) F.
 Proof. 
    intros.
    autounfold.
    split;intro H ;inversion H;subst;auto.
    *
    inversion H0;subst.
    assert (m =  0%nat) by lia;subst.
    generalize (LengthFormula H3 H4);intro.
    lia.
  Qed.
   
  Lemma TheoryEmb1 : forall n i F  ,  
  KT4 i  F -> (KT4C i n) F.
 Proof.
    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.
  
  Lemma TheoryEmb2 : forall n i F  , ((CUTLN n) F) -> (KT4C i n) F.
Proof.
    intros.
    inversion H;subst.
    apply oothc_cutln;auto.
  Qed.
  
 End CutCohBipoles.

Global Hint Constructors  KT4TheoryCut KT4Theory  : core.
Global Hint Unfold RINIT CUTL CUTC  : core.
Global Hint Unfold KT4 KT4C : core.