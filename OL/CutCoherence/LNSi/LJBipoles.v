Require Export MMLL.Misc.Hybrid.
Require Export MMLL.OL.CutCoherence.Bipoles.

Set Implicit Arguments.


(** ** Rules of the encoded proof system *)
Section LJInferenceRules.

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
 
  Inductive RulesEnc := PLUSWiTH | WiTHPLUS  | TENSORPAR .
  
  Definition RulesDefs (t:RulesEnc) (s:Side) {i: subexp} (A B : uexp)  :=
       match t,s with
      | PLUSWiTH, Left => AOr (d|A|) (d|B|)
      | PLUSWiTH, Right => AAnd (u|A|) ( u|B|)
      | WiTHPLUS, Left => AAnd (d|A|) (d|B|)
      | WiTHPLUS, Right => AOr (u|A|) ( u|B|)
      | TENSORPAR, Left => MAnd (u|A|) (d|B|)
      | TENSORPAR, Right => Bang i (MOr (d|A|) (u|B|)) 
      end.  

  Inductive QEnc := ALLSOME | SOMEALL .
  
  Definition QDefs (t:QEnc) (s:Side) (FX : uexp -> uexp):=
    match t,s with 
    | ALLSOME, Left =>  Some (fun x => d| (FX x)|) 
    | ALLSOME, Right => All (fun x => u| (FX x)|)
    | SOMEALL, Left =>  All (fun x => d| (FX x)|)
    | SOMEALL, Right => Some (fun x => u| (FX x)|)
    end .
 
  Class OORules :=
    {
      rulesCte : constants -> ContantEnc ; 
      rulesBin : connectives -> RulesEnc;
      rulesQ :   quantifiers -> QEnc
    }.
  
End LJInferenceRules.
 
Section CutCohBipoles.
  Context {SI : Signature}.
 
Inductive Constants := TT | FF.
Inductive Connectives := AND | OR | IMP.
Inductive UConnectives := . 
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
    rc_rightBody := CteRulesDefs ZEROTOP Right;
    rc_leftBody := CteRulesDefs ZEROTOP Left
  }.
  
 Instance FF_BODY : CteBody := {
    cte := FF;
    rc_rightBody := CteRulesDefs TOPZERO Right;
    rc_leftBody := CteRulesDefs TOPZERO Left
  }.
  
 Instance AND_BODY : BinBody := {
    con := AND;
    rb_rightBody := RulesDefs (i:=loc) PLUSWiTH Right;
    rb_leftBody := RulesDefs  (i:=loc) PLUSWiTH Left
  }.
  
 Instance OR_BODY : BinBody := {
    con := OR;
    rb_rightBody := RulesDefs (i:=loc) WiTHPLUS Right;
    rb_leftBody := RulesDefs (i:=loc) WiTHPLUS Left
  }.
 
 Instance IMP_BODY i: BinBody := {
    con := IMP;
    rb_rightBody := RulesDefs (i:=i) TENSORPAR Right;
    rb_leftBody := RulesDefs (i:=loc) TENSORPAR Left
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

Instance IMP_CUTCOHERENT {UNB: UnbSignature} i : m4 i = true -> mt i = true -> BinCutCoherent (RCUT:=CUTLN) (IMP_BODY i).
Proof with sauto. 
  constructor.
  intros *. intros lenF lenG isFF isFG.
  simpl.
  LLStoreC. 
  LLPar.
  do 2 LLStore.
  TFocus(CUTL F ).
       eapply ltn with (m:=n)... 
       inversion H1.
  LLTensor  [d^| G |] [u^| F |]. 
             LLRelease. LLStore.
  TFocus(CUTL G ).
       eapply ltn with (m:=m)... 
       inversion H1.
  LLTensor  [d^| G |] [d| F |].  
             LLRelease. solveLL. 
   LLRelease. LLStore. 
   UFocus. apply allU. 
    LLTensor [d|F |] [u|G |].
             LLRelease. solveLL. 
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
 
 
Inductive buildTheory {i: subexp}: oo ->  Prop :=  
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
          buildTheory  (BinBipole OR_BODY Left F G)           
  | bconIMPR : forall F G, m4 i = true -> mt i = true ->
          isOLFormula ( t_bin (IMP_BODY i).(con) F G) ->
          buildTheory  (BinBipole (IMP_BODY i) Right F G) 
  | bconIMPL : forall F G, 
          isOLFormula ( t_bin (IMP_BODY loc).(con) F G) ->
          buildTheory  (BinBipole (IMP_BODY loc) Left F G) .
                    
 (** A theory containing only the logical rules and init *)
  Inductive LJTheory {a:subexp} : oo -> Prop :=
  | ooth_consC : forall OO, buildTheoryCons OO ->  LJTheory OO
  | ooth_rulesC : forall OO, buildTheory (i:=a) OO ->  LJTheory OO
  | ooth_initC : forall OO, isOLFormula OO -> LJTheory (RINIT OO)
 | ooth_posC : forall OO,  isOLFormula OO ->  LJTheory (POS OO a) 

   | ooth_negC : forall OO, isOLFormula OO -> LJTheory (NEG OO loc) 
.          

 (** A theory containing the logical rules, init and cut *)
  Inductive LJTheoryCut (n:nat) {a:subexp} : oo -> Prop :=
  | oothc_consC : forall OO, buildTheoryCons OO ->  LJTheoryCut n OO
  | oothc_rulesC : forall OO, buildTheory (i:=a) OO ->  LJTheoryCut n OO
  | oothc_initC : forall OO, isOLFormula OO -> LJTheoryCut n (RINIT OO)
 | oothc_posC : forall OO, isOLFormula OO -> LJTheoryCut n (POS OO a) 
  | oothc_negC : forall OO, isOLFormula OO -> LJTheoryCut n (NEG OO loc) 
  | oothc_cutln : forall OO, CUTLN n (CUTL OO) -> LJTheoryCut n (CUTL OO).
  
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
  
 Definition LJ i := LJTheory (a:=i).
 Definition LJC i n := LJTheoryCut (a:=i) n.
 
 Local Hint Constructors  LJTheoryCut LJTheory  : core.
 Local Hint Unfold RINIT CUTL CUTC  : core.
 Local Hint Unfold LJ LJC : core.

Lemma CutRuleNBound {SIU: UnbSignature}: forall h i n B L X ,  seqN (LJC i n) h B L X ->
                         forall m, n<=m -> seq (LJC i m) B L X .
  Proof with solveF.
    induction h using strongind ; intros.
    inversion H ...
    init2 i0 C. 
    inversion H0;solveF;
      repeat match goal with
             | [ Hs : seqN (LJC i n) ?h ?B1 ?N1 ?X1 |- _] =>
               let Hs1 := fresh in
               assert (Hs1 : seq (LJC i m) B1 N1 X1) by
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
    unfold LJC in H3.
    unfold LJC.
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
  seq (LJC i n)  B L X ->
                         forall m, n<=m -> seq (LJC i m) B L X .
  Proof with solveF.
    intros.
    apply seqtoSeqN in H. destruct H.
    eapply CutRuleNBound;eauto.
    
  Qed.
  
  (** Some easy equivalences on the  above theories *)
 Lemma OOTheryCut0 : forall i F, 
 LJ i F <-> (LJC i 0) F.
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
  LJ i  F -> (LJC i n) F.
 Proof.
    intros.
    inversion H;subst; solve[constructor;auto].
  Qed.
  
  Lemma TheoryEmb2 : forall n i F  , ((CUTLN n) F) -> (LJC i n) F.
Proof.
    intros.
    inversion H;subst.
    apply oothc_cutln;auto.
  Qed.
  

 
Lemma LJHasNeg a: hasNeg (LJ a) loc.  
Proof with auto.
  intro;intros...
Qed.

Lemma LJHasPos a: hasPos (LJ a) a.  
Proof with auto.
  intro;intros...
Qed.

Lemma LJCHasNeg a n: hasNeg (LJC a n) loc.  
Proof with auto.
  intro;intros...
Qed.

Lemma LJCHasPos a n: hasPos (LJC a n) a.  
Proof with auto.
  intro;intros...
Qed.


 End CutCohBipoles.

Global Hint Resolve  LJHasNeg LJCHasNeg:core.
Global Hint Resolve  LJHasPos LJCHasPos:core.
Global Hint Constructors  LJTheoryCut LJTheory  : core.
Global Hint Unfold RINIT CUTL CUTC  : core.
Global Hint Unfold LJ LJC : core.