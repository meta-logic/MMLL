(** * Syntax of MMLL
This file defines the syntax of formulas in MMLL
(type [oo]). Predicate [isFormula] determines when a term is a valid
MMLL formula (ruling out exotic terms). Proofs usually proceed by
induction on the fact that a term satisfies this property.
 *)

Require Export FLL.Misc.UtilsTactics.
Require Export FLL.Misc.Permutations.
Require Export FLL.Misc.Hybrid.

Require Export Coq.Classes.SetoidDec.

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.DecidableClass.
Require Export Coq.Lists.List.
Require Export Permutation.
Require Export Lia.
Require Import Coq.Logic.FunctionalExtensionality.


Export ListNotations.
Set Implicit Arguments.

(** ** External definitions for the Object Logic (OL)
The class [OLSig] specifies the external definitions for terms and
atomic propositions of the object logic. The syntax is parametric on:

 - [atm] : type for atomic propositions (judgments at the Object Logic level)
 - [con] : type for syntactic constructors at the OL level
 - [uniform_atm] : predicate ruling out exotic terms at the OL level
 *)

Class OLSig :=
  {
    (* Signature for atoms (judgments at the OL level) *)
    atm:Set; 
    (* Type for constants (constructors for OL syntax) *)
    con:Set; 
    (* predicate ruling out exotic terms for atoms *)
    uniform_atm : (expr con -> atm) -> Prop
  }.

(** ** Subexponential Signature

This class defines the set of indices that can be used in subexponentials. 
For each of them, it is possible to define the axioms (D,T 4) that
it features and whether it is linear or unbounded 

*)
Class Signature :=
  { 
    subexp: Set;
    lt : relation subexp ; (* < relation of the preorder *)
    lt_pre : PreOrder lt ; (* < is a preorder *)
    lt_dec : forall x y, {lt x  y} + {~ lt x  y}; (* < is decidable *)
    
    (* modal axioms *)
    md : subexp -> bool ; 
    mk : subexp -> bool ; 
    m4 : subexp -> bool ; 
    mt : subexp -> bool ; 
    u : subexp -> bool ;
   
    allK: forall x, mk x = true; 
    
    (* closure conditions *)
    uClosure : forall x y,u x = true -> lt x y -> u y = true;
    mdClosure : forall x y, md x = true -> lt x y -> md y = true;
    mkClosure : forall x y,  mk x = true -> lt x y -> mk y = true;
    m4Closure : forall x y, m4 x = true -> lt x y -> m4 y = true;
    mtClosure : forall x y, mt x = true -> lt x y -> mt y = true; 
    
    (** The local subexponential cannot move between components *)
    (* "local" subexp *)
    loc : subexp ;
    locK : mk loc = true;
    locD : md loc = false;
    locT : mt loc = true;
    loc4 : m4 loc = false;
    locu : u loc = true;
    locAlone : forall a, a <> loc -> ~ (lt a loc \/ lt loc a);
    locAlone' : forall a, lt a loc \/ lt loc a ->a=loc;
   
    plust : subexp -> subexp ;
    plustpropF : forall x, mt x = false -> mt (plust x) = true /\
                           m4 (plust x) = m4 x /\
                           md (plust x) = md x /\ 
                           mk (plust x) = mk x /\
                           u (plust x) = u x /\
                           lt x (plust x) ;
    plustpropT : forall x, mt x = true -> plust x = x;
    
    plust_mono : forall x y, lt x y -> lt (plust x) (plust y)            
                                                   
  }.
  
Instance Lt_Reflexive `{Signature} : Reflexive lt.
Proof. apply @PreOrder_Reflexive;eauto. exact lt_pre. Qed.

Instance Lt_Transitive `{Signature} : Transitive lt.
Proof.  apply @PreOrder_Transitive;eauto. exact lt_pre. Qed.

Class UnbSignature `{Signature}:=
  { 
    allU: forall x, u x = true; }.


Section LLSyntax.
 
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.
  
  Lemma SubExpInhabitant : subexp.
  exact loc.
  Qed.
  
 Hint Resolve SubExpInhabitant : core.
  
  Lemma uDec : forall x, {u x = true} + {u x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.
   
  Lemma m4Dec : forall x, {m4 x = true} + {m4 x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  
  
  Lemma mtDec : forall x, {mt x = true} + {mt x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  
  
  Lemma mdDec : forall x, {md x = true} + {md x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  
    
 Ltac solveSubExp :=
 auto;
  match goal with
  | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = true ] => apply locK 
  | [ |- md loc = false ] => apply locD

  | [H: u loc = false |- _] => rewrite locu in H; discriminate H   
  | [H: mk loc = false |- _] => rewrite locK in H; discriminate H  
  | [H: mt loc = false |- _] => rewrite locT in H; discriminate H  
  | [H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H  
  | [H: md loc = true |- _] => rewrite locD in H; discriminate H  
  
  | [H1: ?a <> loc, H2: lt ?a loc |- _] => apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
| [H1: ?a <> loc, H2: lt loc ?a |- _] => apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction

  end.
  
  Lemma locNoD i : md i = true -> i <> loc.
  Proof with subst;solveSubExp.
  intros.
  intro...
  Qed.
  
  Lemma locNo4 i : m4 i = true -> i <> loc.
  Proof with subst;solveSubExp.
  intros.
  intro...
  Qed.
  
  Lemma locTDiff i : mt i = false -> i <> loc.
  Proof with subst;solveSubExp.
  intros.
  intro...
  Qed.
  
  
  Lemma locUDiff i : u i = false -> i <> loc.
  Proof with subst;solveSubExp.
  intros.
  intro...
  Qed.
  
    
  Lemma locDec a: {loc = a} + {loc <> a}.
  Proof.
     destruct (lt_dec a loc);
     destruct (lt_dec loc a).
     rewrite @locAlone' with (a:=a);auto.
     rewrite @locAlone' with (a:=a);auto.
     rewrite @locAlone' with (a:=a);auto.
     right.
     intro;subst.
     apply n.
     apply @PreOrder_Reflexive.
     exact lt_pre.
  Qed.
    
  Lemma plust_keeping4 : forall b a, m4 a = b -> m4 (plust a) = b.
  Proof.
   intros.
   destruct (mtDec a).
   * apply plustpropT in e.
     rewrite e;auto.
   * apply plustpropF in e.
     decompose [and] e;clear e.
     rewrite H2;auto.
  Qed.
  
  Lemma plust_keepingu : forall b a, u a = b -> u (plust a) = b.
  Proof.
   intros.
   destruct (mtDec a).
   * apply plustpropT in e.
     rewrite e;auto.
   * apply plustpropF in e.
     decompose [and] e;clear e.
     rewrite H4;auto.
  Qed.
  
     Lemma plust_keepingu' : forall b a, u (plust a) = b -> u a = b.
  Proof.
  intros.
  destruct (mtDec a).
     apply plustpropT in e.
     rewrite <- e;auto.
     apply plustpropF in e.
     decompose [and] e;clear e. 
     rewrite <- H4;auto.
  Qed. 
   
  Lemma plust_loc_fixpoint : (plust loc) = loc.
  Proof.
    assert(mt loc = true) by apply locT.
    apply plustpropT in H;auto.
  Qed.
 
 
   Lemma plust_plust_fixpoint : forall x , plust (plust x) = (plust x).
  Proof.                             
    intros.
    destruct (mtDec x). 
    apply plustpropT in e.
    rewrite e;auto.
    apply plustpropF in e.
    decompose [and] e;clear e.
    apply plustpropT in H.
    rewrite H;auto.
  Qed.
  
   Lemma plust_loc_diff a : a <> loc -> (plust a) <> loc.
  Proof.
   intros.
   destruct (mtDec a).
   * intro.
     apply locAlone in H.
     apply plustpropT in e.
     apply H.
     rewrite e in *.
     rewrite H0 in *.
     left. apply @PreOrder_Reflexive. 
     exact lt_pre.
   * intro.
     apply locAlone in H.
     apply plustpropF in e.
     decompose [and] e;clear e.
     apply H.
     rewrite H0 in *.
     left;auto.
  Qed.
   
  Lemma plust_incL : forall x y, lt x y -> lt x (plust y).
  Proof.                             
    intros.
    destruct (mtDec y). 
    * apply plustpropT in e.
      rewrite e;auto.
    * apply plustpropF in e.
      decompose [and] e;clear e.  
      apply @PreOrder_Transitive with (R:=lt) (y:=y);auto.
      exact lt_pre.
  Qed. 
  
  Lemma T_in_plust a : mt(plust a) = true.
  Proof.
    intros.
    destruct (mtDec a). 
    * apply plustpropT in e as H'.
      rewrite H';auto.
    * apply plustpropF in e as H'.
      decompose [and] H';clear H'.  
      eapply @eq_trans with (y:=true);auto.
  Qed. 
  
  
  (** Connectives of the logic *)
  Inductive oo : Set :=
  | atom : atm -> oo
  | perp : atm -> oo
  | Top : oo
  | One : oo
  | Zero : oo
  | Bot : oo 
  | AAnd : oo -> oo -> oo
  | MAnd : oo -> oo -> oo
  | AOr : oo -> oo -> oo
  | MOr : oo -> oo -> oo 
  | Bang : subexp -> oo -> oo
  | Quest : subexp -> oo -> oo 
  | All : (expr con -> oo) -> oo 
  | Some : (expr con -> oo) -> oo.
  
 
  (** Complexity of formulas *)
  Fixpoint complexity (X:oo) :=
    match X with
    | atom A   => 1
    | perp A   => 1
    | One => 1
    | Bot => 1
    | Zero => 1
    | Top => 1
    | MAnd F G => 1+ complexity F + complexity G
    | AAnd F G => 1+ complexity F + complexity G
    | MOr F G => 1+ complexity F + complexity G
    | AOr F G => 1+ complexity F + complexity G
    | Bang a F   => 1+ complexity F
    | Quest a F  => 1+ complexity F
    | Some FX => 1+ complexity (FX (VAR con 0))
    | All FX => 1+ complexity (FX (VAR con 0))
    end.
    

     (** Complexity on list of formulas *)
  Fixpoint complexityL (L: list oo) :=
    match L with
    | nil => 0
    | a :: L' => complexity a + complexityL L'
    end.

  Lemma Complexity0 : forall F, complexity F > 0.
    induction F;simpl;lia.
  Qed.

  Lemma ComplexityL0 : forall L, complexityL L =0 -> L = [].
    intros;destruct L;simpl;auto.
    simpl in H.
    generalize (Complexity0 o);intros.
    lia.
  Qed.
  
  (** Classical linear logic dualities *)
  Fixpoint dual (X: oo) :=
    match X with
    | atom A   => perp A
    | perp A   => atom A
    | One => Bot
    | Bot => One
    | Zero => Top
    | Top => Zero
    | MAnd F G => MOr (dual  F) (dual G)
    | AAnd F G => AOr (dual  F) (dual G)
    | MOr F G => MAnd (dual  F) (dual G)
    | AOr F G => AAnd (dual  F) (dual G)
    | Bang a F   => Quest a (dual F)
    | Quest a F  => Bang a (dual   F)
    | Some X => All (fun x => dual  (X x))
    | All X => Some (fun x => dual (X x))
    end.

  (** Negation is involutive *)
  Theorem ng_involutive: forall F: oo, F = dual (dual F).
  Proof.
    intro. 
    induction F; simpl; auto;
      try( try(rewrite <- IHF1); try(rewrite <- IHF2); try(rewrite <- IHF);auto);
      try(assert (o = fun x =>  dual (dual (o x))) by
             (extensionality e; apply H); rewrite <- H0; auto).
  Qed.

  Lemma DualComplexity : forall F, complexity F = complexity (dual F) .
    intros.
    induction F;intros;auto;
      try solve
          [simpl; try rewrite IHF; try rewrite IHF1; try rewrite IHF2;auto].
  Qed.
 
  (**  Linear Implication *)
  Definition Limp (F G : oo) : oo := MOr (dual F) G .
  Definition TypedFormula : Type := subexp * oo.
  

  (** Uniform Predicate (ruling out exotic terms) *)
  Inductive uniform_oo: (expr con -> oo) -> Prop := 
  | uniform_atom: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (atom (a x)))
  | uniform_perp: forall (a: expr con -> atm),
      uniform_atm a -> uniform_oo (fun x => (perp (a x)))
  | uniform_Top: uniform_oo (fun x => Top)
  | uniform_One: uniform_oo (fun x => One)
  | uniform_Bot: uniform_oo (fun x => Bot)  
  | uniform_Zero: uniform_oo (fun x => Zero)
  | uniform_AAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AAnd (A x) (B x)))
  | uniform_MAnd: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MAnd (A x) (B x)))
  | uniform_AOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (AOr (A x) (B x)))
  | uniform_MOr: forall (A B: expr con -> oo),
      uniform_oo A -> uniform_oo B -> uniform_oo (fun x => (MOr (A x) (B x))) 
  | uniform_Bang: forall (A: expr con -> oo) a,
      uniform_oo A -> uniform_oo (fun x => (Bang a (A x)))
  | uniform_Quest: forall (A: expr con -> oo) a, 
      uniform_oo A -> uniform_oo (fun x => (Quest a (A x)))
  | uniform_All: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (All (fun y => (A y x))))
  | uniform_Some: forall (A: expr con -> expr con -> oo),
      (forall y:expr con, uniform_oo (fun x => (A y x))) ->
      uniform_oo (fun x => (Some (fun y => (A y x)))).

  (** Well formedness condition  *)
  Inductive isFormula: oo -> Prop  :=
  | wf_atm : forall (P1:atm), isFormula (atom P1)
  | wf_perp : forall (P1:atm), isFormula (perp P1)
  | wf_Top : isFormula Top
  | wf_One : isFormula One
  | wf_Zero : isFormula Zero
  | wf_Bot : isFormula Bot
  | wf_AAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AAnd A1 A2)
  | wf_MAnd : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MAnd A1 A2)
  | wf_AOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (AOr A1 A2)
  | wf_MOr : forall (A1 A2 :oo), isFormula A1  -> isFormula A2  -> isFormula (MOr A1 A2)
  | wf_Bang : forall (A1 :oo) a, isFormula A1 -> isFormula (Bang a A1)
  | wf_Quest : forall (A1 :oo) a, isFormula A1 -> isFormula (Quest a A1)
  | wf_All : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (All A)
  | wf_Some : forall (A : expr con -> oo), uniform_oo A -> (forall t: expr con, isFormula (A t)) -> isFormula (Some A).

  Hint Constructors isFormula : core.

  
  Lemma ComplexityUniformEq : forall FX x y , uniform_oo FX ->
                                            proper x -> proper y ->
                                            complexity (FX x) =  complexity (FX y).
    intros.
    induction H;subst;simpl;firstorder.
  Qed.
  
   Lemma ComplexityPerm: forall M N, Permutation M N ->
                                        complexityL M =  complexityL N.
    intros.
    induction H;subst;simpl;lia.
  Qed.
  
    Global Instance permComplexity   :
   Proper ((@Permutation oo) ==> eq) (complexityL).
    Proof.
    unfold Proper; unfold respectful.
      intros.
      apply ComplexityPerm;auto.
  Qed.
  
  (** Well formendness conditions for lists and arrows *)
  Definition isFormulaL  (L:list oo)  := Forall isFormula L. 
  Definition multiset := list.
  Hint Constructors Remove : core. 
  
  Global Instance perm_isFormulaL :
      Proper (@Permutation oo ==> Basics.impl)
             (isFormulaL  ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold isFormulaL.
      rewrite <- H;auto.
    Qed.
 
  
  Lemma isFormulaIn : forall F L, 
      isFormulaL L -> In F L -> isFormula F. 
  Proof.
    intros. eapply @ForallIn with (F:=F) in H;auto.
  Qed.

  (** Arrows for the focused system
      - [UP] : negative phase
      - [DW] : positive phase 
   *)
  Inductive Arrow  := 
  | UP (l : list oo) (* negative phase *)
  | DW (F : oo). (* positive phase *)

  (** Transforming arrows into lists of formulas *)
  Definition Arrow2LL (A: Arrow) : list oo :=
    match A  with
    | UP l => l
    | DW F => [F]
    end.

  (** Checking when a formulas has to lose focusing *)
  Inductive release : oo -> Prop :=
  | RelNA1 : forall A,  release (atom A)
  | RelTop : release Top
  | RelBot : release Bot
  | RelPar : forall F G, release (MOr F G)
  | RelWith : forall F G, release (AAnd F G)
  | RelQuest : forall a F, release (Quest a F)
  | RelForall : forall FX, release (All FX).

  (** Positive formulas (focusing persists *)
  Inductive positiveFormula : oo -> Prop :=
  | PosAt : forall A,  positiveFormula (perp A)
  | PosOne : positiveFormula One
  | PosZero : positiveFormula Zero
  | PosTensor : forall F G, positiveFormula (MAnd F G)
  | PosPlus : forall F G, positiveFormula (AOr F G)
  | PosBang : forall F a, positiveFormula (Bang a F)
  | PosEx : forall FX, positiveFormula (Some FX).


  (** Every formula is either  a positive formula, or it must be released *)
  Theorem PositiveOrRelease : forall F,
      positiveFormula F \/ release F.
    intros.
    destruct F;try (left;constructor);try(right;constructor).
  Qed.

  (** Positive formulas cannot be released *)
  Theorem PositiveNotRelease: forall F,
      positiveFormula F -> ~ release F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.

  Theorem ReleaseNotPositive : forall F,
      release F -> ~ positiveFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  (** The dual of a positive formula is a release formula *)
  Theorem PositiveDualRelease : forall F,
      positiveFormula F -> release (dual F).
    intros F Hpos.
    inversion Hpos;subst;constructor.
  Qed.

  Theorem ReleaseDualPositive : forall F, release F -> positiveFormula (dual F).
    intros F Hrel.
    inversion Hrel;subst;constructor.
  Qed.
  
  (** Assynchronous connectives *)
  Inductive asynchronous : oo -> Prop :=
  | aTop :   asynchronous Top
  | aBot :   asynchronous Bot
  | aPar :   forall F G, asynchronous (MOr F G)
  | aWith :  forall F G, asynchronous (AAnd F G)
  | aQuest : forall a F , asynchronous (Quest a F)
  | aForall : forall FX  , asynchronous (All FX).

  Definition Notasynchronous F := ~ (asynchronous F).
  Definition isNotAsyncL (L : list oo) := Forall Notasynchronous L.

  (** Postive atoms *)
  Inductive IsPositiveAtom : oo -> Prop :=
  | IsPAP : forall A, IsPositiveAtom (atom A).

  (** Negative atoms *)
  Inductive IsNegativeAtom : oo -> Prop :=
  | IsNAP : forall A, IsNegativeAtom (perp A).
  
Local Hint Constructors IsPositiveAtom IsNegativeAtom : core.
  
  Theorem NegativeAtomDec : forall F,
      IsNegativeAtom F \/ ~ IsNegativeAtom F.
    induction F;auto; try solve[right;intro H'; inversion H'].
  Qed.

  
  Theorem PositiveAtomDec : forall F,
      IsPositiveAtom F \/ ~ IsPositiveAtom F.
    destruct F;auto;right;intro H';inversion H'.
  Qed.

  (** List of positive atoms *)
  Definition IsPositiveAtomL  L : Prop := Forall IsPositiveAtom L.

  Lemma NotAsynchronousPosAtoms :
    forall F, ~ asynchronous  F -> positiveFormula F \/ IsPositiveAtom F.
    intros.
    destruct F;intuition;  first
                             [left;constructor
                             | match goal with [_:  asynchronous ?F -> False |- _] => 
                                               assert(asynchronous F) by constructor;contradiction end
                             ].
  Qed.

  Lemma AsyncRelease: forall F, asynchronous F -> release F.
  Proof.
    intros.
    inversion H; constructor.
  Qed.
  
  Lemma AsIsPosRelease: forall F,
      (asynchronous F \/ IsPositiveAtom F ) -> release F.
  Proof.
    intros.
    destruct H;auto using AsyncRelease.
    inversion H;constructor;auto.
  Qed.

  Lemma NotAsynchronousPosAtoms' :
    forall G, ~ asynchronous G ->
              IsPositiveAtom G \/ (positiveFormula G).
    intros G HG.
    apply NotAsynchronousPosAtoms in HG;tauto.
  Qed.

  Lemma  IsPositiveAtomNotAssync :
    forall F,  IsPositiveAtom F -> ~ asynchronous F.
  Proof.
    intros.
    inversion H;auto.
    intro.
    inversion H1.
  Qed.
  
  
  End LLSyntax.
  
  Ltac solveSubExp :=
 auto;
  match goal with
    | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = false ] => apply locK 
  | [ |- md loc = false ] => apply locD   
   | [SI : Signature, OLS: OLSig, 
      H: u loc = false |- _] => rewrite locu in H; discriminate H   
   | [SI : Signature, OLS: OLSig, 
      H: mk loc = false |- _] => rewrite locK in H; discriminate H  
   | [SI : Signature, OLS: OLSig, 
      H: mt loc = false |- _] => rewrite locT in H; discriminate H 
   | [SI : Signature, OLS: OLSig, 
      H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H 
   | [SI : Signature, OLS: OLSig,   
      H: md loc = true |- _] => rewrite locD in H; discriminate H 
   | [SI : Signature, OLS: OLSig, H1: ?a <> loc, H2: lt ?a loc |- _] => 
      apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
   | [SI : Signature, OLS: OLSig, H1: ?a <> loc, H2: lt loc ?a |- _] => 
      apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction    
  end.
  

Section SubExpSets.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.
  
  Definition SetS (i:subexp) (K : list TypedFormula) := Forall (fun k => ~ lt i (fst k) ) K.
     Global Instance perm_SetS i  :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetS i).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetS.
      rewrite <- H;auto.
    Qed.
  
  
  Definition SetT (K : list TypedFormula) := Forall (fun k => mt (fst k) = true) K.
     Global Instance perm_SetT  :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetT ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetT.
      rewrite <- H;auto.
    Qed.
  
  Definition SetU (K : list TypedFormula) := Forall (fun k => u (fst k) = true) K.
  Global Instance perm_SetU  :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetU ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetU.
      rewrite <- H;auto.
    Qed.
 
  Definition SetL (K : list TypedFormula) := Forall (fun k => u (fst k) = false) K.
  Global Instance perm_SetL  :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetL ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetL.
      rewrite <- H;auto.
    Qed.
 
(* Definition Setno4 (K : list TypedFormula) := Forall (fun k => m4 (fst k) = false) K.
  Definition Set4 (K : list TypedFormula) := Forall (fun k => m4 (fst k) = true) K.
  Definition SetS i (K : list TypedFormula) := Forall (fun k => lt i (fst k)) K.
 *)
  
  Definition SetK i (K : list TypedFormula) := Forall (fun k => m4 (fst k) = false /\ lt i (fst k)) K.
  Global Instance perm_SetK (i:subexp) :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetK i ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetK.
      rewrite <- H;auto.
    Qed.
 
  
  Definition SetK4 i (K : list TypedFormula) := Forall (fun k => m4 (fst k) = true /\ lt i (fst k)) K.
  Global Instance perm_SetK4 (i:subexp) :
      Proper (@Permutation TypedFormula ==> Basics.impl)
             (SetK4 i ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.impl .
      intros.
      unfold SetK4.
      rewrite <- H;auto.
    Qed.
    
  Definition Loc (L:list TypedFormula):= 
        map (fun x => (loc,(snd x))) L.
  Global Instance perm_Loc :
      Proper (@Permutation TypedFormula ==> @Permutation TypedFormula)
             (Loc ).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      unfold Loc.
      rewrite <- H;auto.
    Qed.
    
  Definition PlusT (L:list TypedFormula):=   
        map (fun x => (plust (fst x),snd x) ) L.
  Global Instance perm_PlusT :
      Proper (@Permutation TypedFormula ==> @Permutation TypedFormula)
             (PlusT ).
    Proof.
      unfold Proper; unfold respectful.
      intros.
      unfold PlusT.
      rewrite <- H;auto.
    Qed.
  
   Fixpoint getU  (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then (x,F) :: (getU l0) else getU l0
  end.
  
 Fixpoint getL (l : list TypedFormula) :=
  match l with
  | [] => []
  | (x,F) :: l0 => if u x then getL l0 else (x,F) :: (getL l0) 
  end.
   
End SubExpSets.

 Global Hint Unfold SetT SetU SetL SetK SetK4 PlusT Loc isFormulaL first second: core.  

Ltac sfold := 
repeat
match goal with
 | [  |- context[Forall (fun k : subexp * oo => mt (fst k) = true) ?K] ] => 
       change (Forall (fun k : subexp * oo => mt (fst k) = true) K) with (SetT K)
 | [  |- context[Forall (fun k : subexp * oo => u (fst k) = true) ?K] ] => 
       change (Forall (fun k : subexp * oo => u (fst k) = true) K) with (SetU K)
 | [  |- context[Forall (fun k : subexp * oo => u (fst k) = false) ?K] ] =>
       change (Forall (fun k : subexp * oo => u (fst k) = false) K) with (SetT K)
 | [  |- context[Forall (fun k : subexp * oo => m4 (fst k) = false /\ lt ?i (fst k)) ?K ] ] =>   
         change (Forall (fun k : subexp * oo => m4 (fst k) = false /\ lt i (fst k)) K) with (SetK i K)
 | [  |- context[Forall (fun k : subexp * oo => m4 (fst k) = true /\ lt ?i (fst k)) ?K ] ] =>  
         change (Forall (fun k : subexp * oo => m4 (fst k) = true /\ lt i (fst k)) K) with (SetK4 i K)
 | [  |- context[map (fun x => (loc,_)) ?K]] => change (map (fun x => (loc,_)) K) with (Loc K) 
 | [  |- context[map (fun x => (plust _,_)) ?K]] => change (map (fun x => (plust _,_)) K) with (PlusT K)
 | [  |- context[Forall isFormula ?L] ] => change (Forall isFormula L) with (isFormulaL L)
 | [  |- context[map snd ?L] ] => change (map snd L) with (second L)
 | [ H : context[map snd ?L] |- _ ] => fold (second L) in H
  
 | [ H : context[Forall (fun k : subexp * oo => mt (fst k) = true) ?K]  |- _ ] => fold (SetT K) in H
 | [ H : context[Forall (fun k : subexp * oo => u (fst k) = true) ?K] |- _ ] => fold (SetU K) in H
 | [ H : context[Forall (fun k : subexp * oo => u (fst k) = false) ?K] |- _ ] => fold (SetL K) in H  
 | [ H : context[Forall (fun k : subexp * oo => m4 (fst k) = false /\ lt ?i (fst k)) ?K] |-  _ ] => fold (SetK i K) in H  
 | [ H : context[Forall (fun k : subexp * oo => m4 (fst k) = true /\ lt ?i (fst k)) ?K] |-  _ ] => fold (SetK4 i K) in H
 | [ H : context[map (fun x => (loc,_)) ?K] |- _ ] => fold (Loc K) in H  
 | [ H : context[map (fun x => (plust _,_)) ?K] |- _ ] => fold (PlusT K) in H 
 | [ H : context[Forall isFormula ?L] |- _ ] => fold (isFormulaL L) in H                
end.
 
Tactic Notation "srewrite" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => try rewrite H
                     
end;sfold.

Tactic Notation "srewrite_reverse" constr(H) := autounfold;
 let Hs := type of H in 
 match Hs with
| Permutation _ _ => symmetry in H;try rewrite H
                     
end;sfold.


Tactic Notation "srewrite" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => try rewrite H1 in H2
                     
end;sfold.

Tactic Notation "srewrite_reverse" constr(H1) "in" constr(H2) := 
autounfold in H2;
 let Hs := type of H1 in 
 match Hs with
| Permutation _ _ => symmetry in H1; try rewrite H1 in H2
                     
end;sfold.

 Ltac simplSignature1 := 
  repeat 
    multimatch goal with
  (* Basic simplifcation *)
  | [  |- context[length []] ] => simpl
  | [ H: context[length []]  |- _ ] => simpl in H
  | [  |- context[Loc []] ] => simpl
  | [ H:  context[Loc []] |- _ ] => simpl in H
  | [  |- context[PlusT []] ] => simpl
  | [ H:  context[PlusT []] |- _ ] => simpl in H
  | [  |- context[second []] ] => simpl
  | [ H:  context[second []] |- _ ] => simpl in H

 | [ H: context[if u loc then _ else _] |- _ ] => rewrite locu in H
 | [ H: context[if mt loc then _ else _] |- _ ] => rewrite locT in H
 | [ H: context[if md loc then _ else _] |- _ ] => rewrite locD in H
 | [ H: context[if m4 loc then _ else _] |- _ ] => rewrite loc4 in H
 | [ H: context[if mk loc then _ else _] |- _ ] => rewrite locK in H
 | [ |- context[if u loc then _ else _]  ] => rewrite locu 
 | [ |- context[if mt loc then _ else _] ] => rewrite locT 
 | [ |- context[if md loc then _ else _] ] => rewrite locD 
 | [ |- context[if m4 loc then _ else _] ] => rewrite loc4 
 | [ |- context[if mk loc then _ else _] ] => rewrite locK 

  | [ H1: u (fst ?F) = _, H2: context[getU (?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; rewrite H1 in H2 
  | [ H1: u (fst ?F) = _, H2: context[getL (?F :: _)] |- _ ] => 
     destruct F;simpl in H1;simpl in H2; rewrite H1 in H2      
  | [ H: u (fst ?F) = _ |- context[getU (?F :: _)] ] => 
     destruct F;simpl;simpl in H; rewrite H 
  | [ H: u (fst ?F) = _ |- context[getL (?F :: _)] ] => 
     destruct F;simpl;simpl in H; rewrite H 
 | [ H1: ?s ?a = _, H2: context[if ?s ?a then _ else _] |- _ ] => rewrite H1 in H2 
 | [ H: ?s ?a = _|- context[if ?s ?a then _ else _] ] => rewrite H 

(* About second *)
 | [ H: context[second(_++_)] |- _ ] => rewrite secondApp in H 
 | [ |- context[second(_++_)] ] => rewrite secondApp
 
 | [  |- context[_ (_::_)] ] => simpl
  | [ H: context[_ (_::_)] |- _ ] => simpl in H 

  end.
 
 
 Ltac solveSignature1 := try
  match goal with
  | [ H: UnbSignature |- u ?i = true ] => apply allU 
  | [ H: md ?i = true |- ?i <> loc ] => apply locNoD;auto 
  | [ H: m4 ?i = true |- ?i <> loc ] => apply locNo4;auto 
  | [ H: mt ?i = false |- ?i <> loc ] => apply locTDiff;auto 
  | [ H: u ?i = false |- ?i <> loc ] => apply locUDiff;auto 

  | [ |- lt ?i ?i] => apply @PreOrder_Reflexive; exact lt_pre
  | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = true ] => apply locK 
  | [ |- md loc = false ] => apply locD
  
  | [ |- mt (plust _) = true ] => apply T_in_plust
  | [ |- subexp ] => exact loc
    
  | [H: u loc = false |- _] => rewrite locu in H; discriminate H   
  | [H: mk loc = false |- _] => rewrite locK in H; discriminate H  
  | [H: mt loc = false |- _] => rewrite locT in H; discriminate H  
  | [H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H  
  | [H: md loc = true |- _] => rewrite locD in H; discriminate H  

  | [H1: ?a <> loc, H2: lt ?a loc |- _] => apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
  | [H1: ?a <> loc, H2: lt loc ?a |- _] => apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction
    
   | [H: SetT (?F::?K) |- mt (fst ?F) = true] => inversion H;subst;auto
   | [H: SetU (?F::?K) |- u (fst ?F) = true] => inversion H;subst;auto
   | [H: SetL (?F::?K) |- u (fst ?F) = false] => inversion H;subst;auto
   
   | [H: SetT ((?s, _)::?K) |- mt ?s = true] => inversion H;subst;auto
   | [H: SetU ((?s, _)::?K) |- u ?s = true] => inversion H;subst;auto
   | [H: SetL ((?s, _)::?K) |- u ?s = false] => inversion H;subst;auto
   
   | [H: SetK ?i (?F::?K) |- m4 (fst ?F) = false] => inversion H;subst;intuition
   | [H: _ ?i (?F::?K) |- lt ?i (fst ?F) ] => inversion H;subst;intuition
   | [H: SetK ?i ((?s, _)::?K) |- m4 ?s = false] => inversion H;subst;intuition
   | [H: _ ?i ((?s, _)::?K) |- lt ?i ?s ] => inversion H;subst;intuition
   | [H: SetK4 ?i (?F::?K) |- m4 (fst ?F) = true] => inversion H;subst;intuition
   | [H: SetK4 ?i ((?s, _)::?K) |- m4 ?s = true] => inversion H;subst;intuition
   
  end.
  
 
Global Hint Constructors isFormula : core.

 Lemma isFormulaInS1 (OLS:OLSig) (SI:Signature): forall (i:subexp) F L, 
      isFormulaL (second L) -> In (i,F) L -> isFormula F. 
  Proof.
    intros. 
    apply InPermutation in H0;sauto.
    eapply @ForallIn with (F:=F) in H;auto.
    eapply @Permutation_map with (f:=snd) in H0.
    rewrite H0.
    simpl;sauto.
  Qed.

Lemma isFormulaInS2 (OLS:OLSig) (SI:Signature): forall (i:subexp) F L L', 
      isFormulaL (second L) -> Permutation L ((i,F)::L') -> isFormula F. 
  Proof.
    intros. 
    eapply @ForallIn with (F:=F) in H;auto.
    eapply @Permutation_map with (f:=snd) in H0.
    rewrite H0.
    simpl;sauto.
  Qed.

Ltac solveSignature2 :=
simplSignature1;
try solve [solveSignature1];
try
match goal with
 | [ |- SetK ?i ?K] => solveFoldFALL2 (fun k :subexp*oo => m4 (fst k) = false /\ lt i (fst k) )
 | [ |- SetK4 ?i ?K] => solveFoldFALL2  (fun k :subexp*oo => m4 (fst k) = true /\ lt i (fst k) )
 | [ |- SetT ?K] => solveFoldFALL1 (fun k :subexp*oo => mt (fst k) = true)
 | [ |- SetU ?K] => solveFoldFALL1 (fun k :subexp*oo => u (fst k) = true)
 | [ |- SetL ?K] => solveFoldFALL1 (fun k :subexp*oo => u (fst k) = false)
 end;try sfold.  


Section Properties.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.
       
  Lemma locSetK1 F: SetK loc [(loc, F)].
  Proof with sauto;solveSignature2.
  constructor... 
  Qed.

   
  Lemma locSetK2 i F: i <> loc -> ~ SetK i [(loc, F)].
  Proof with sauto;solveSignature2.
  intros. intro.
  inversion H0...
  Qed.
  
  Lemma locSetK4 i F:  ~ SetK4 i [(loc, F)].
  Proof with sauto.
  intro.
  inversion H...
  solveSubExp.
  Qed.
   
    
  Lemma locSetU F : SetU [(loc, F)].
  Proof.
  unfold SetU.
  constructor;auto. 
  simpl. solveSubExp. 
  Qed.
  
  Lemma locSetT F : SetT [(loc, F)].
  Proof.
  unfold SetT.
  constructor;auto. 
  simpl. solveSubExp. 
  Qed.
  
 
  
  Lemma locApp K1 K2: Loc (K1 ++ K2) = Loc K1 ++ Loc K2.
  Proof.
    induction K1;auto.
  destruct a;simpl;auto.
  rewrite IHK1; auto.
   Qed.
 
  Lemma PlusTApp K1 K2: PlusT (K1 ++ K2) = PlusT K1 ++ PlusT K2.
  Proof.
    induction K1;auto.
  destruct a;simpl;auto.
  rewrite IHK1; auto.
   Qed.
 
 Lemma locApp' K1 K2 : Permutation (Loc (K1 ++ K2)) (Loc K1 ++ Loc K2).
  Proof.
  rewrite locApp;auto.
  Qed.
 
 Lemma PlusTApp' K1 K2: Permutation (PlusT (K1 ++ K2)) (PlusT K1 ++ PlusT K2).
  Proof.
   rewrite PlusTApp;auto.
   Qed.
   
   Lemma SetU_then_empty K : SetU K -> getL K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 
  
    
   Lemma SetL_then_empty K : SetL K -> getU K =[].
   Proof with sauto.
  induction K;intros...
  destruct a as [p F].
  inversion H...
  simpl. rewrite H2...
  Qed. 
  
  Lemma MapPlusT_fixpoint : forall C , PlusT (PlusT C) = (PlusT C).
  Proof with subst;auto.
  induction C;simpl;intros;auto.
  rewrite plust_plust_fixpoint...
  rewrite IHC...
  Qed.
 
        
  Lemma SetTPlusT K: SetT K -> PlusT K = K.
   Proof with sauto.
   induction K;intros...
   destruct a;simpl.
   inversion H...
   apply plustpropT in H2.
   rewrite H2.
   rewrite IHK;auto.
 Qed.


   Lemma SetKTrans i a K : SetK i K -> lt a i -> SetK a K.
  Proof with sauto.
  induction K;simpl;intros...
  inversion H...
  
  apply Forall_and_inv in H4...
  
  apply Forall_cons... 
  apply @PreOrder_Transitive with (R:=lt) (y:=i);auto.
  exact lt_pre.
  
apply IHK...

autounfold in *. solveForall.
  Qed.

  Global Instance trans_SetK :
       Proper (lt ==> @Permutation TypedFormula ==> Basics.flip Basics.impl)
             (SetK ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl .
      intros;subst.
      rewrite H0.
      eapply (SetKTrans _ H1);auto. 
    Qed.
  
  Lemma SetKK4_then_empty' i K : SetK i K -> m4 i = true -> K=[].
  Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  assert(m4 p = true).
  {
  eapply m4Closure.
  exact H0. exact H2. }
  sauto.
  Qed.
  
    Lemma SetTKClosure i K  : mt i = true -> SetK i K -> SetT K. 
  Proof with sauto.
  unfold SetK; unfold SetT.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply mtClosure. 
  exact H. exact H2.
  Qed.

  Lemma SetUKClosure i K  : u i = true -> SetK i K -> SetU K. 
  Proof with sauto.
  unfold SetK; unfold SetU.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply uClosure. 
  exact H. exact H2.
  Qed.

 Lemma SetK4In a i K: SetK4 i K -> In a K -> m4 (fst a) = true.
  Proof with sauto.
  intros.
  eapply @ForallIn with (F:=a) in H...
  Qed.
 
   Lemma SetK4Trans i a K : SetK4 i K -> lt a i -> SetK4 a K.
  Proof with sauto.
  induction K;simpl;intros...
  inversion H...
  
  apply Forall_and_inv in H4...
  
  apply Forall_cons... 
  apply @PreOrder_Transitive with (R:=lt) (y:=i);auto.
  exact lt_pre.
  
apply IHK...

autounfold in *. solveForall.
  Qed.


  Global Instance trans_SetK4 :
       Proper (lt ==> @Permutation TypedFormula ==> Basics.flip Basics.impl)
             (SetK4 ).
    Proof.
      unfold Proper; unfold respectful; unfold Basics.flip; unfold Basics.impl .
      intros;subst.
      rewrite H0.
      eapply (SetK4Trans _ H1);auto. 
    Qed.
 
 
  Lemma SetKK4_then_empty i K : SetK i K -> SetK4 i K -> K=[].
   Proof with sauto.
  destruct K;intros...
  destruct t as [p F].
  inversion H...
  inversion H0...
  Qed. 
  
    Lemma SetTK4Closure i K  : mt i = true -> SetK4 i K -> SetT K. 
  Proof with sauto.
  unfold SetK4; unfold SetT.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply mtClosure. 
  exact H. exact H2.
  Qed.
  
  Lemma SetUK4Closure i K  : u i = true -> SetK4 i K -> SetU K. 
  Proof with sauto.
  unfold SetK4; unfold SetU.
  induction K;intros... 
  inversion H0...
  apply Forall_cons...
  eapply uClosure. 
  exact H. exact H2.
  Qed.

 Theorem cxtDestruct K: Permutation K (getU K++getL K).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
  Theorem cxtDestructSecond K: Permutation (second K) (second (getU K++getL K)).
 Proof with subst;auto.
 induction K;auto.
 destruct a as [a F].
 destruct (uDec a); simpl; rewrite e.
 constructor;auto.
 rewrite secondApp.
 simpl.
 apply Permutation_cons_app;auto.
 rewrite <- secondApp;auto.
 Qed.

 Theorem cxtDestruct' K: exists K1 K2, Permutation K (getU K++getL K1 ++ getL K2) /\ Permutation (getL K) (getL K1 ++ getL K2).
 Proof with sauto.
 induction K...
 exists [].
 exists [].
 simpl;auto.
 destruct a as [a F].
 destruct (uDec a); simpl;
 rewrite e;simpl.
 exists x. exists x0.
 constructor;auto.
 exists ((a,F)::x).
  exists x0.
  simpl; rewrite e;simpl.
  constructor;auto.
 apply Permutation_cons_app;auto.
 Qed.
 
 Lemma getUPerm K1 K2 : Permutation K1 K2 -> Permutation (getU K1) (getU K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.
 
  Lemma getLPerm K1 K2 : Permutation K1 K2 -> Permutation (getL K1) (getL K2).
Proof with subst;auto.
 revert dependent K2.
 revert dependent K1.
 induction 1;intros. 
 * simpl...
 * destruct x as [x F];
   destruct (uDec x);
   simpl;rewrite e...
 * destruct x as [x F];
   destruct y as [y G];
   destruct (uDec x);
   destruct (uDec y);
   simpl;rewrite e;rewrite e0...  
   apply perm_swap.
 * eapply (Permutation_trans IHPermutation1 IHPermutation2). Qed.

  Global Instance getU_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getU ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getUPerm;auto.
    Qed. 
  
    Global Instance getL_morph :
      Proper ((@Permutation TypedFormula) ==> (@Permutation TypedFormula))
             (getL ).
    Proof.
    unfold Proper; unfold respectful.
    intros. 
    apply getLPerm;auto.
    Qed. 
    
     
  Lemma getU_fixpoint K : getU(getU K) =  getU K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
    Lemma getL_fixpoint K : getL(getL K) =  getL K.
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.  
 
  Lemma getUgetL K : getU(getL K) =  [].
  Proof.
  induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
 Qed.
  
  Lemma getLgetU K : getL(getU K) =  [].
  Proof.
   induction K;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl; rewrite e.
  rewrite IHK; auto.
  Qed.

 
  Lemma getUApp K1 K2 : getU (K1 ++ K2) =  getU K1 ++ getU K2.
  Proof.
    induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto;
  simpl.
  rewrite IHK1; auto.
   Qed.
 
 
 Lemma getUApp' K1 K2 : Permutation (getU (K1 ++ K2)) (getU K1 ++ getU K2).
  Proof.
  rewrite getUApp;auto.
  Qed. 
 
 Lemma uIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *.
  rewrite e in *...  firstorder. 
  rewrite e in *...
  inversion H0...
 Qed.
 
  Lemma getLApp K1 K2 : getL (K1 ++ K2) =  getL K1 ++ getL K2.
  Proof.
  induction K1;auto.
  destruct a;simpl;auto.
  destruct (uDec s);rewrite e;auto.
  simpl. 
  rewrite IHK1. auto.
 Qed.
  
 Lemma getLApp' K1 K2 : Permutation (getL (K1 ++ K2)) (getL K1 ++ getL K2).
  Proof.
  rewrite getLApp;auto.
  Qed. 

Lemma lIngetL i F B :  u i = false -> In (i, F) B -> In (i, F) (getL B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
 Qed.

Lemma lIngetU i F B :  u i = true -> In (i, F) B -> In (i, F) (getU B).
 Proof with sauto.
  intros.
  rewrite cxtDestruct in H0.
  apply in_app_or in H0.
  destruct H0;auto.
  induction B...
  destruct a.
  destruct(uDec s); simpl in *;
  rewrite e in *...
  simpl in H0...
  firstorder.
  inversion H0...
 Qed.


  Theorem getUtoSetU K: SetU (getU K).
 Proof with subst;auto.
 induction K... 
 simpl;solveSignature2.
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
   Theorem getLtoSetU K: SetU (getL K) -> getL K =[].
 Proof with sauto.
 induction K;intros. 
 * auto.
 * destruct a as [a F].
   destruct (uDec a); simpl in *;
  rewrite e in *...
  inversion H...
 Qed.
 
 
 Lemma getUPerm_SetU K X : Permutation (getU K) X -> SetU X.
  Proof.
  intros.
  symmetry in H.
  srewrite  H.
  apply getUtoSetU.
 Qed. 
 

 
  Theorem getLtoSetL K: SetL (getL K).
 Proof with subst;auto.
 induction K...
 simpl;solveSignature2.
 destruct a as [a F].
 simpl.
 destruct (uDec a); simpl;
 rewrite e...
 Qed.
 
  Lemma getLPerm_SetL K X : Permutation (getL K) X -> SetL X.
  Proof.
  intros.
  symmetry in H.
  srewrite H.
  apply getLtoSetL.
 Qed. 
 
  Theorem setUtoGetU K: SetU K -> getU K = K.
 Proof with subst;auto.
 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.

  Theorem setLtoGetL K: SetL K -> getL K = K.
 Proof with subst;auto.

 induction K; intros...
 destruct a as [a F].
 inversion H...
 apply IHK in H3.
 simpl in *. rewrite H2...
 rewrite H3...
 Qed.
 
   Lemma getUPermU K1 K2 : Permutation (getU K1) K2 -> Permutation (getU K1) (getU K2).
Proof with sauto.
 intros.
 rewrite H.
 apply getUPerm_SetU in H.
 rewrite cxtDestruct...
 rewrite (SetU_then_empty H)...
 rewrite setUtoGetU...
 rewrite setUtoGetU...
 Qed.
 
 Theorem Unb_Lin_Disj' K: exists K1 K2, SetU K1 /\ SetL K2 /\ Permutation K (K1++K2).
 Proof with subst;try solveSignature2;auto .
 induction K;auto.
 do 2 eexists [];simpl...
 destruct IHK.
 destruct H.
 decompose [and] H ;clear H.
 destruct a as [a F].
 destruct (uDec a).
 eexists ((a,F)::x).
 eexists x0.
 split... 
 eexists x.
 eexists ((a,F)::x0).
 split... 
 split...  
 rewrite H3... apply Permutation_middle.
 Qed.
 
(* Lemmata about SetK *) 
  
   Lemma SetKPlusT' a K: SetK (plust a)  K -> SetK a K.
  Proof with sauto.
  induction K;intros;auto.

  destruct a0 as [p F].
  inversion H...
 
  apply IHK in H3;auto.
  solveSignature2.
  split;auto.
  apply @PreOrder_Transitive with (R:=lt) (y:=(plust a));auto.
  exact lt_pre.
  apply plust_incL. 
  apply @PreOrder_Reflexive.
  exact lt_pre.
  Qed.
  
  Lemma SetKPlusT a K: SetK a K ->  SetK (plust a) (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.

  destruct a0 as [p F].
  inversion H...
  unfold SetK. apply Forall_cons;simpl;[split;auto|]. 
  apply plust_keeping4;auto.
  apply plust_mono;auto.
 apply IHK...
  Qed.
  
  
   Lemma SetK4PlusT' a K: SetK4 (plust a)  K -> SetK4 a K.
  Proof with sauto.
  induction K;intros;auto.

  destruct a0 as [p F].
  inversion H...
 
  apply IHK in H3;auto.
  solveSignature2.
  split;auto.
  apply @PreOrder_Transitive with (R:=lt) (y:=(plust a));auto.
  exact lt_pre.
  apply plust_incL. 
  apply @PreOrder_Reflexive.
  exact lt_pre.
  Qed.
  
    Lemma SetK4PlusT a K: SetK4 a K ->  SetK4 (plust a) (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.

  destruct a0 as [p F].
  inversion H...
  unfold SetK. apply Forall_cons;simpl;[split;auto|]. 
  apply plust_keeping4;auto.
  apply plust_mono;auto.
 apply IHK...
  Qed.

  Lemma SetUPlusT K: SetU K ->  SetU (PlusT K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    inversion H...
    apply Forall_cons...  
    apply plust_keepingu in H2;auto.
  Qed.

 Lemma PlusTSetU K: SetU (PlusT K) -> SetU K.
  Proof with sauto.
  induction K;simpl;intros;auto.
    apply Forall_cons...
    apply  Forall_inv in H...
    apply plust_keepingu';auto.
    apply  Forall_inv_tail in H...
  Qed.
  
  Lemma SetUDec K :  {SetU K} + {~ SetU K}.
  Proof with sauto.
    induction K;simpl;auto.
    destruct IHK.
    - destruct a as [p F]. 
      destruct (uDec p).
      left.  apply Forall_cons...
      right. intro.
      inversion H...
    - destruct a as [p F]. 
      destruct (uDec p).
      right. intro. inversion H... 
      right. intro.
      inversion H... 
 Qed.
 
 
  Lemma SetULoc K: SetU (Loc K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    simpl.
    apply Forall_cons...
    apply locu.  
 Qed.
 
   Lemma SetTLoc K: SetT (Loc K).
  Proof with sauto.
  induction K;simpl;intros;auto.
    destruct a as [p F].
    simpl.
    apply Forall_cons...
    apply locT.  
 Qed.
 
  
  Lemma getLPlusT K: SetT K -> getL K = getL (PlusT K).
  Proof with sauto.
  induction K. 
  * simpl;auto.
  * destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      apply IHK.
      inversion H...
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      rewrite IHK.
      apply  Forall_inv in H...
      rewrite plustpropT;auto.
      apply  Forall_inv_tail in H...
  Qed.
 
   Lemma getUPlusT K: SetT K -> getU K = getU (PlusT K).
  Proof with sauto.
  induction K. 
  * simpl;auto.
  * destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      rewrite IHK.
      apply  Forall_inv in H...
      rewrite plustpropT;auto.
      apply  Forall_inv_tail in H...
 - simpl. rewrite e.
      apply plust_keepingu in e.
      rewrite e.
      apply IHK.
      inversion H...      
  Qed.
 
 Lemma getLEPlusT K: getL K = [] <-> getL (PlusT K) = [].
  Proof with sauto.
  split;intros.
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl in H. rewrite e in H.
      apply plust_keepingu in e.
      simpl.
      rewrite e...
    - simpl in H. rewrite e in H...
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
    -  simpl in H.
      apply plust_keepingu in e.
      rewrite e in H... 
Qed.

 Lemma getUEPlusT K: getU K = [] <-> getU (PlusT K) = [].
  Proof with sauto.
  split;intros.
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl in H. rewrite e in H.
      apply plust_keepingu in e.
      simpl.
      rewrite e...
    - simpl in H. rewrite e in H...
      apply plust_keepingu in e.
      simpl.
      rewrite e...
  * induction K...
    destruct a as [p F].
    destruct (uDec p);intros.
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
    - simpl. rewrite e.
      simpl in H.
      apply plust_keepingu in e.
      rewrite e in H...
Qed.
    
 Lemma getUELoc K: K = [] <-> getU (Loc K) = [].
  Proof with sauto.
  split;intros.
  rewrite H. simpl;auto.
  * induction K...
    simpl in H. rewrite locu in H...
Qed.
   
  Lemma getULoc K: getU (Loc K) = Loc K.
  Proof with sauto.
  induction K;intros...
  simpl. rewrite locu...
  rewrite IHK...
Qed.

Lemma  PlusTgetU K : (PlusT (getU K)) = getU (PlusT K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    rewrite e.
    simpl.
    rewrite (plust_keepingu _ e).
    rewrite IHK...
  * simpl...
    rewrite e...
    rewrite (plust_keepingu _ e)... 
Qed.

Lemma  PlusTgetL K : (PlusT (getL K)) = getL (PlusT K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    rewrite e.
    simpl.
    rewrite (plust_keepingu _ e)...
  * simpl...
    rewrite e...
    rewrite (plust_keepingu _ e)...
    simpl.
    rewrite IHK...
Qed.

Lemma  getUPlusTgetU' K : getU (PlusT (getU K)) = PlusT (getU K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    rewrite e.
    simpl.
    rewrite (plust_keepingu _ e).
    rewrite IHK...
  * simpl...
    rewrite e...
Qed.

Lemma  getUPlusTgetL' K : getL (PlusT (getL K)) = PlusT (getL K).
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  destruct (uDec b)...
  * simpl...
    rewrite e...
  * simpl...
    rewrite e.
    simpl.
    rewrite (plust_keepingu _ e).
    rewrite IHK...    
Qed.

 Lemma getLELoc K: getL (Loc K) = [].
  Proof with sauto.
  induction K...
  destruct a as [p F].
  simpl.
  rewrite locu;auto.
 Qed. 
 
  Lemma getLgetUPlusT K: getL (PlusT (getU K)) = [].
  Proof with sauto.
  induction K... 
  destruct a as [p F].
  destruct (uDec p).
  - assert(u (plust p) = true).
    apply plust_keepingu;auto.
    simpl. rewrite e. 
    simpl. rewrite H;auto.
  - simpl. rewrite e;auto. 
 Qed. 
 
 Lemma getLgetUPlusT' K: SetU K -> getL (PlusT K) = [].
  Proof with sauto.
  induction K;intros... 
  destruct a as [p F].
  destruct (uDec p).
  - assert(u (plust p) = true).
    apply plust_keepingu;auto.
    simpl. rewrite H0.
    apply IHK.
    inversion H... 
  - inversion H... 
 Qed. 
 
  Lemma getUgetLPlusT K: getU (PlusT (getL K)) = [].
  Proof with sauto.
  
  induction K... 
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e;auto. 
  - assert(u (plust p) = false).
    apply plust_keepingu;auto. 
    simpl. rewrite e;auto.
    simpl. rewrite H;auto.
 Qed. 
 
  Lemma isFormulaL_getU B :  
      isFormulaL (second B) -> isFormulaL (second (getU B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - rewrite e.
      simpl in *.
      inversion H;sauto.
      firstorder.
    - rewrite e.
      simpl in *.
      inversion H;sauto.
  Qed.    
    
    Lemma isFormulaL_getL B :  
      isFormulaL (second B) -> isFormulaL (second (getL B)). 
  Proof.
    induction B;intros;sauto. 
    destruct a as [a F]. 
    destruct(uDec a);simpl;sauto.
    - rewrite e.
      simpl in *.
      inversion H;sauto.
   - rewrite e.
      simpl in *.
      inversion H;sauto.
      firstorder.
  Qed.
  
  Lemma isFormulaLSplitUL B :  
      isFormulaL (second (getU B)) ->  isFormulaL (second (getL B)) -> isFormulaL (second B). 
  Proof.
    intros.
    rewrite cxtDestructSecond.
    rewrite secondApp.
    apply Forall_app;auto.
  Qed.   
  
      
 Lemma isFormulaL_PlusT B :  
      isFormulaL (second B) -> isFormulaL (second (PlusT B)). 
  Proof.
    induction B;simpl;unfold isFormulaL;intros;auto.
    apply Forall_cons.
    apply Forall_inv in H;auto.
    apply Forall_inv_tail in H.
    apply IHB;auto.
    Qed.
 
 Lemma isFormulaL_Loc  B :  
      isFormulaL (second B) -> isFormulaL (second (Loc B)). 
  Proof.
    induction B;simpl;unfold isFormulaL;intros;auto.
    constructor...
    apply Forall_inv in H;auto.
    apply Forall_inv_tail in H.
    apply IHB;auto.
    Qed.
    
     Lemma isFormulaLSecond B D X Y:  
     Permutation (getL B) (getL D ++ X) -> 
     Permutation (getU B) (getU D ++ Y) ->
     isFormulaL (second B) -> isFormulaL (second D). 
  Proof.
    autounfold;unfold second;intros.
    rewrite cxtDestruct in H1.
    rewrite H in H1.
    rewrite H0 in H1.
    fold (second ((getU D ++ Y) ++ getL D ++ X)) in H1.
    repeat rewrite secondApp in H1.
    apply Forall_app in H1.
    destruct H1.
    apply Forall_app in H1.
    apply Forall_app in H2.
    sauto.
    rewrite cxtDestruct.
    fold (second (getU D ++ getL D)). 
    repeat rewrite secondApp.
    apply Forall_app;auto.
    Qed.
   
    
   Lemma subexpInLoc  C: forall (i:subexp) (F:oo), In (i, F) (Loc C) -> i = loc.
  Proof with subst;auto.
  induction C;intros...
  * simpl in H. contradiction.
  * simpl in H.
    destruct H.
    inversion H...
    apply IHC in H...
  Qed.
   
    Lemma subexpInMap  C: forall (i:subexp) (F:oo), In (i, F) (PlusT C) -> i = plust i.
  Proof with subst;auto.
  induction C;intros...
  * simpl in H. contradiction.
  * simpl in H.
    destruct H.
    inversion H...
    rewrite plust_plust_fixpoint;auto.
    apply IHC in H...
  Qed.
  
    Lemma SetKLoc i K  : i <> loc -> SetK i K -> In loc (first K) -> False. 
  Proof with sauto.
  induction K;simpl;intros.
  contradiction.
  destruct H1.
  * destruct a;simpl in *;subst.
    inversion H0...
    apply locAlone in H.
    apply H. left;auto.
  * apply IHK;auto.
    solveSignature2. 
 Qed. 

  Lemma SetK4Loc i K  : i <> loc -> SetK4 i K -> In loc (first K) -> False. 
  Proof with sauto.
  induction K;simpl;intros.
  contradiction.
  destruct H1.
  * destruct a;simpl in *;subst.
    inversion H0...
    apply locAlone in H.
    apply H. left;auto.
  * apply IHK;auto.
    solveSignature2. 
  Qed.

  
  Lemma PlusT_fixpoint : forall C , PlusT (PlusT C) = (PlusT C).
  Proof with subst;auto.
  induction C;simpl;intros;auto.
  rewrite plust_plust_fixpoint...
  rewrite IHC...
  Qed.
  
  Lemma PlusT_fixpoint' : forall C , SetT C -> (PlusT C) = C.
  Proof with sauto.
  induction C;simpl;intros;auto.
  inversion H...
  apply IHC in H3.
  rewrite H3...
  destruct a as [p F].
  simpl in *.
  rewrite plustpropT...
  Qed.
  

 Lemma getUS F t D L: getU D = (t, F)::L -> u t = true.
 Proof with sauto.
 induction D;intros...
 destruct a.
 destruct (uDec s).
 inversion H... rewrite e in *...
 inversion H1...
 inversion H... rewrite e in *...
 Qed.
 

  Lemma linearEmpty K : getL K = [] -> getL K = [] /\ Permutation (getU K) K /\ SetU K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    apply IHK in H. 
    split;sauto. 
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
Qed.

Lemma unboundedEmpty K : getU K = [] -> getU K = [] /\ Permutation (getL K) K /\ SetL K.
  Proof with auto.
  intros. split;auto.
  revert dependent K. 
  induction K;intros...
  destruct a as [p F].
  destruct (uDec p).
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
    inversion H...
  - simpl. rewrite e.
    simpl in H.
    rewrite e in H.
     apply IHK in H. 
    split;sauto. 
 Qed.
 
  Lemma SetK4Destruct i K : SetK4 i K -> SetK4 i (getU K) /\ SetK4 i (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  solveSignature2.
  Qed.
  
   Lemma SetKDestruct i K : SetK i K -> SetK i (getU K) /\ SetK i (getL K).
  Proof with sauto.
  intros.
  rewrite cxtDestruct in H;split;
  solveSignature2.
  Qed.

   Lemma linearInUnb a A K : u a = false -> SetU K -> In (a, A) K -> False.
  Proof with sauto.
  induction K;intros...
  destruct a0.
  inversion H1...
  inversion H0...
  apply IHK...
  inversion H0... 
  Qed. 
  
  
Lemma  setUPlusTgetU K : SetU K -> PlusT (getU K) = PlusT K.
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  inversion H...
  simpl. rewrite H2...
  simpl...
  rewrite IHK;auto.
 Qed.

Lemma  setULocgetU K : SetU K -> Loc (getU K) = Loc K.
Proof with sauto.
  induction K;intros...
  destruct a as [b F].
  inversion H...
  simpl. rewrite H2...
  simpl...
  rewrite IHK;auto.
 Qed.
  
  
 Lemma SetK4LocEmpty C : SetK4 loc C -> Permutation C (Loc C).
 Proof with sauto.
 induction C;intros...
 inversion H...
 assert(False).
 eapply @locAlone with (a:=(fst a))...
 intro...
 rewrite H2 in H0.
 solveSubExp.
 contradiction.
 Qed. 
 
 Lemma InContext1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F B ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.

 Lemma InSecond1 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second B) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H.
  rewrite H1.
  rewrite app_assoc.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.
  
  
  
 Lemma InContext2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F D ->  In F BD.
  Proof with sauto.
  intros.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  apply in_or_app;auto.
  Qed.
  
  Lemma InSecond2 F BD B D:
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  In F (second D) ->  In F (second BD).
  Proof with sauto.
  intros.
  unfold second.
  rewrite cxtDestruct.
  rewrite H0.
  rewrite H1.
  rewrite Permutation_midle_app.
  rewrite <- cxtDestruct.
  rewrite map_app.
  apply in_or_app;auto.
  Qed.  

  Lemma isFormulaSecond1 BD X Y B Z U:
  isFormulaL (second (X++getU BD++Y)) -> 
  Permutation (X++getU BD++Y) (Z++B++U) ->
  isFormulaL (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.  

 Lemma isFormulaSecond2 BD X Y B Z U:
  isFormulaL (second (X++getL BD++Y)) -> 
  Permutation (X++getL BD++Y) (Z++B++U) ->
  isFormulaL (second B).
   Proof with sauto.
   intros.
   assert(isFormulaL (second (Z ++ B ++ U))).
   symmetry in H0.
   srewrite H0...
   rewrite !secondApp in H1.
   apply Forall_app in H1...
   apply Forall_app in H3...
 Qed.
 


  Lemma isFormulaSecondSplit1 BD X Y B D:
  isFormulaL (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU B) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL (second B).
   Proof with sauto.
  intros.
   rewrite !secondApp in H.
  assert(isFormulaL (second BD)).
  apply Forall_app in H...
  assert(isFormulaL (second X)).
  apply Forall_app in H...
  apply Forall_app in H4...
  assert(isFormulaL (second Y)).
  apply Forall_app in H...
  apply Forall_app in H5...
  assert(Permutation ([] ++ getU BD ++ X) ([] ++getU B ++ [])).
  sauto.
  eapply isFormulaSecond1 in H5...
  assert(Permutation ([] ++ getL BD ++ Y) ([] ++getL B ++ getL D)).
  sauto.
  eapply isFormulaSecond2 in H6...
  apply isFormulaLSplitUL...
  
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getL...
  rewrite !secondApp...
  apply Forall_app...
  apply isFormulaL_getU...
 Qed. 
 
  Lemma isFormulaSecondSplit2 BD X Y B D:
  isFormulaL (second (BD++X++Y)) -> 
  Permutation (getU BD++X) (getU D) ->
  Permutation (getL BD++Y) (getL B ++ getL D) -> isFormulaL (second D).
   Proof with sauto.
  intros.
  eapply isFormulaSecondSplit1 with (X:=X) (Y:=Y) (BD:=BD) (D:=B);auto.
  rewrite H1... perm.
  Qed.
 
 
     Theorem destructClassicSetK4 a C4 C4' CN CN': 
    SetK4 a C4 -> SetK4 a C4' ->
    Permutation (C4 ++ CN) (C4' ++ CN') -> 
    exists K4_1 K4_2 K4_3 N, Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
                    Permutation CN (K4_3 ++ N) /\ Permutation CN' (K4_2 ++ N). 
  Proof with subst;auto.
    intros.
    revert dependent C4'.
    revert dependent CN.
    revert dependent CN'.
    revert dependent a.
    induction C4;intros.
    * 
      eexists []. 
      eexists []. 
      eexists C4'.
      eexists CN'. 
      simpl.
      split;auto.
    *
      simpl in H1.
      symmetry in H1.
      
      checkPermutationCases H1.
      - eapply IHC4 with (CN:=a::CN) (CN':=CN') in H0;
        [sauto | solveSignature2 | 
         rewrite H2;symmetry;rewrite <- app_comm_cons;
         apply Permutation_cons_app;auto].
         checkPermutationCases H4.
         + 
           eexists (a::x0).
           eexists x1.
           eexists x4.
           eexists x3.
           split;auto.
           rewrite <- app_comm_cons.
           apply Permutation_cons...
           split;auto.
           rewrite H5.
           rewrite H4. perm. 
         + eexists x0.
           eexists (a::x1).
           eexists x2.
           eexists x4.
           split;auto.
           apply Permutation_cons_app...
           split;auto.
           split;auto.
           rewrite H7. 
           rewrite H4. perm. 
      - 
        eapply IHC4 with (CN:=CN) (CN':=x) in H0;
        [sauto | solveSignature2 | symmetry;auto].
        eexists x0.
        eexists (a::x1).
        eexists x2.
        eexists x3.
        split;auto.
        apply Permutation_cons_app...
        split;auto.
        split;auto.
        rewrite H2. rewrite H7.
        perm. 
 Qed.       
 
  Theorem destructClassicSetK a CK CK' CN CN': 
    SetK a CK -> SetK a CK' ->
    Permutation (CK ++ CN) (CK' ++ CN') -> 
    exists K_1 K_2 K_3 N, Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
                    Permutation CN (K_3 ++ N) /\ Permutation CN' (K_2 ++ N). 
  Proof with subst;auto.
    intros.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    revert dependent a.
    induction CK;intros.
    * 
      eexists []. 
      eexists []. 
      eexists CK'.
      eexists CN'. 
      simpl.
      split;auto.
    *
      checkPermutationCases H1.
      - eapply IHCK with (CN:=a::CN) (CN':=CN') in H0;
        [sauto | solveSignature2 | 
         rewrite H2;symmetry;rewrite <- app_comm_cons;
         apply Permutation_cons_app;auto].
         checkPermutationCases H4.
         + 
           eexists (a::x0).
           eexists x1.
           eexists x4.
           eexists x3.
           split;auto.
           rewrite <- app_comm_cons.
           apply Permutation_cons...
           split;auto.
           rewrite H5.
           rewrite H4. perm. 
         + eexists x0.
           eexists (a::x1).
           eexists x2.
           eexists x4.
           split;auto.
           apply Permutation_cons_app...
           split;auto.
           split;auto.
           rewrite H7. 
           rewrite H4. perm. 
      - 
        eapply IHCK with (CN:=CN) (CN':=x) in H0;
        [sauto | solveSignature2 | symmetry;auto].
        eexists x0.
        eexists (a::x1).
        eexists x2.
        eexists x3.
        split;auto.
        apply Permutation_cons_app...
        split;auto.
        split;auto.
        rewrite H2. rewrite H7.
        perm. 
 Qed.       

 Theorem destructClassicSet a C4 C4' CK CK' CN CN': 
 SetK4 a C4 -> SetK4 a C4' -> SetK a CK -> SetK a CK' -> 
 Permutation (C4 ++ CK ++ CN) (C4' ++ CK' ++ CN') -> 
 (exists K_1 K_2 K_3 N, 
          Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
          Permutation (C4 ++ CN) (K_3 ++ N) /\ Permutation (C4' ++ CN') (K_2 ++ N)) /\
 (exists K4_1 K4_2 K4_3 N, 
          Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
          Permutation (CK ++ CN) (K4_3 ++ N) /\ Permutation (CK' ++ CN') (K4_2 ++ N)). 
  Proof with subst;auto.
  split;intros.
  * assert(Permutation (CK ++ (C4 ++ CN)) (CK' ++ (C4' ++ CN'))).
    rewrite Permutation_app_swap_app.
    rewrite H3. perm.
    clear H3.
    apply destructClassicSetK with (a:=a) in H4...
  * apply destructClassicSetK4 with (a:=a) in H3...
  Qed.
 

  Theorem destructClassicSet' a C4 C4' CK CK' CN CN': 
 SetK4 a C4 -> SetK4 a C4' -> SetK a CK -> SetK a CK' -> 
 Permutation (C4 ++ CK ++ CN) (C4' ++ CK' ++ CN') -> 
 exists K_1 K_2 K_3 K4_1 K4_2 K4_3 N, 
          Permutation CK (K_1 ++ K_2) /\ Permutation CK' (K_1 ++ K_3) /\ 
          Permutation C4 (K4_1 ++ K4_2) /\ Permutation C4' (K4_1 ++ K4_3) /\ 
          Permutation CN (K_3 ++ K4_3 ++ N) /\ Permutation CN' (K_2 ++ K4_2 ++ N) . 
  Proof with sauto.
  intros.
    
    revert dependent CK.
    revert dependent C4'.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    induction C4;intros...
    * 
    revert dependent C4'.
    revert dependent CK'.
    revert dependent CN.
    revert dependent CN'.
    induction CK;intros...
      eexists []. 
      eexists []. 
      eexists CK'.
      eexists []. 
      eexists []. 
      eexists C4'.
      eexists CN'...
      rewrite H3... perm. 
      simpl in H3.
      checkPermutationCases H3.
      - rewrite H4 in H0.
        inversion H0...
        inversion H1...
      -  checkPermutationCases H4.
         rewrite <- H6 in H5.
         symmetry in H5.
         apply IHCK in H5...
         sauto...
         eexists (a0 :: x1).
         eexists x2.
         eexists x3.
         eexists [].
         eexists [].
         eexists x6.
         eexists x7...
         rewrite H5...
         rewrite H4.
         rewrite H8...
         solveSignature2.
         rewrite H4 in H2.
         solveSignature2.
         rewrite <- H6 in H5.
         symmetry in H5.
         apply IHCK in H5...
         sauto...
         eexists x1.
         eexists (a0::x2).
         eexists x3.
         eexists [].
         eexists [].
         eexists x6.
         eexists x7...
         rewrite H5... perm.
         rewrite H4.
         rewrite H12...
         solveSignature2.
    *
      simpl in H3.
      revert dependent C4'.
      revert dependent CK'.
      revert dependent CN.
      revert dependent CN'.
      induction CK;intros...
      - checkPermutationCases H3.
         symmetry in H5.
         change (C4++CN) with (C4++[]++CN) in H5.
         apply IHC4 in H5...
         sauto...
         eexists [].
         eexists [].
         eexists x2.
         eexists (a0::x3).
         eexists x4.
         eexists x5.
         eexists x6...
         rewrite H6...
         rewrite H4.
         rewrite H8...
         solveSignature2.
         rewrite H4 in H0.
         solveSignature2.
         
         checkPermutationCases H4.
         rewrite H4 in H2.
         inversion H2...
         inversion H...
         
         rewrite <- H6 in H5.
         symmetry in H5.
         change (C4++CN) with (C4++[]++CN) in H5.
         apply IHC4 in H5...
         sauto...
         eexists [].
         eexists [].
         eexists x3.
         eexists x4.
         exists (a0::x5).
         eexists x6.
         eexists x7...
         rewrite H7... perm.
         rewrite H4.
         rewrite H12...
         solveSignature2.
      -  assert(Permutation  (a0 :: C4 ++ (a1 :: CK) ++ CN)  (a1 :: C4 ++ (a0 :: CK) ++ CN)) by perm.
         rewrite H4 in H3. clear H4. 
          checkPermutationCases H3.
          symmetry in H5.
            assert(Permutation (C4 ++ a0 :: CK ++ CN) (a0 ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         apply IHCK in H5... 
         rewrite H4 in H0.
         inversion H0...
         inversion H1...
         solveSignature2.
         rewrite H4 in H0.
         solveSignature2.
         checkPermutationCases H4.
        
         
         symmetry in H5.
         assert(Permutation (C4 ++ a0 :: CK ++ CN) (a0 ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         rewrite <- H6 in H5.
         apply IHCK in H5... 
         eexists (a1::x1).
         exists x2.
         exists x3.
         exists x4.
         exists x5.
         exists x6.
         exists x7...
         rewrite H5...
         rewrite H4.
         rewrite H8...
         solveSignature2.
         rewrite H4 in H2.
         solveSignature2.
         symmetry in H5.
         assert(Permutation (C4 ++ a0 :: CK ++ CN) (a0 ::  C4 ++ CK ++ CN)) by perm.
            rewrite H3 in H5.
         clear H3.
         rewrite <- H6 in H5.
         apply IHCK in H5... 
         eexists x1.
         exists (a1::x2).
         exists x3.
         exists x4.
         exists x5.
         exists x6.
         exists x7...
         rewrite H5... perm.
         rewrite H4.
         rewrite H12...
         solveSignature2.
  Qed.
  
   Theorem destructClassicSetU' a C4 C4' CK CK' CN CN': 
 SetK4 a C4 -> SetK4 a C4' -> SetK a CK -> SetK a CK' -> 
 Permutation (getU C4 ++ getU CK ++ getU CN) (getU C4' ++ getU CK' ++ getU CN') -> 
 exists K_1 K_2 K_3 K4_1 K4_2 K4_3 N, 
          Permutation (getU CK) (getU K_1 ++ getU K_2) /\ Permutation (getU CK') (getU K_1 ++ getU K_3) /\ 
          Permutation (getU C4) (getU K4_1 ++ getU K4_2) /\ Permutation (getU C4') (getU K4_1 ++ getU K4_3) /\ 
          Permutation (getU CN) (getU K_3 ++ getU K4_3 ++ getU N) /\ Permutation (getU CN') (getU K_2 ++ getU K4_2 ++ getU N) . 
  Proof with sauto.
     intros.
     apply destructClassicSet' with (a:=a) in H3...
     eexists x.
     eexists x0.
     eexists x1.
     eexists x2.
     eexists x3.
     eexists x4.
     eexists x5.
       2:{ rewrite cxtDestruct in H. solveSignature2. }
      2:{ rewrite cxtDestruct in H0. solveSignature2. }
     2:{ rewrite cxtDestruct in H1. solveSignature2. }
    2:{ rewrite cxtDestruct in H2. solveSignature2. }
    repeat rewrite <- getUApp.
    rewrite (@setUtoGetU (x++x0)).
     rewrite (@setUtoGetU (x++x1)).
      rewrite (@setUtoGetU (x2++x3)).
       rewrite (@setUtoGetU (x2++x4)).
        rewrite (@setUtoGetU (x1++x4++x5)).
        rewrite (@setUtoGetU (x0++x3++x5))...
    
    apply getUPerm_SetU in H10...
    apply getUPerm_SetU in H8...
    apply getUPerm_SetU in H7...
    apply getUPerm_SetU in H5...
    apply getUPerm_SetU in H6...
    apply getUPerm_SetU in H4...
   Qed. 
   
     
  Theorem destructClassicSetU a C4 C4' CK CK' CN CN': 
 SetK4 a C4 -> SetK4 a C4' -> SetK a CK -> SetK a CK' -> 
 Permutation (getU C4 ++ getU CK ++ getU CN) (getU C4' ++ getU CK' ++ getU CN') -> 
 (exists K_1 K_2 K_3 N, 
          Permutation (getU CK) (getU K_1 ++ getU K_2) /\ Permutation (getU CK') (getU K_1 ++ getU K_3) /\ 
          Permutation (getU C4 ++ getU CN) (getU K_3 ++ getU N) /\ Permutation (getU C4' ++ getU CN') (getU K_2 ++ getU N)) /\
 (exists K4_1 K4_2 K4_3 N, 
          Permutation (getU C4) (getU K4_1 ++ getU K4_2) /\ Permutation (getU C4') (getU K4_1 ++ getU K4_3) /\ 
          Permutation (getU CK ++ getU CN) (getU K4_3 ++ getU N) /\ Permutation (getU CK' ++ getU CN') (getU K4_2 ++ getU N)). 
  Proof with sauto.
  intros. apply destructClassicSet with (a:=a) in H3...
  
  
  3:{ rewrite cxtDestruct in H. solveSignature2. }
  3:{ rewrite cxtDestruct in H0. solveSignature2. }
  3:{ rewrite cxtDestruct in H1. solveSignature2. }
  3:{ rewrite cxtDestruct in H2. solveSignature2. }
 
  apply getUPermU  in H3.
  apply getUPermU in H10.
  setoid_rewrite <- getUApp in H8.
  apply getUPermU in H8.
  setoid_rewrite <- getUApp in H12.
  apply getUPermU in H12...

  setoid_rewrite getUApp in H3.
  setoid_rewrite getUApp in H10.
  setoid_rewrite getUApp in H8.
  setoid_rewrite getUApp in H12.
  
  exists x3. exists x4.
  exists x5. exists x6...
  
    apply getUPermU  in H5.
  apply getUPermU  in H7.
  setoid_rewrite <- getUApp in H6.
  apply getUPermU  in H6.
  setoid_rewrite <- getUApp in H9.
  apply getUPermU  in H9.
  
  setoid_rewrite getUApp in H5.
  setoid_rewrite getUApp in H6.
  setoid_rewrite getUApp in H7.
  setoid_rewrite getUApp in H9.
  
  exists x. exists x0.
  exists x1. exists x2...
  Qed.
 
  Lemma simplUnb BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetU B -> Permutation BD D.
  Proof.   
  intros.
  rewrite (SetU_then_empty H2) in H1.
  rewrite (cxtDestruct BD).
  rewrite H0.
  rewrite H1.
  simpl. 
  rewrite <- cxtDestruct;auto.
  Qed.
  
  Lemma simplUnb' BD B D:          
  Permutation (getU BD) (getU B) ->
  Permutation (getU BD) (getU D) ->
  Permutation (getL BD) (getL B ++ getL D) ->
  SetU D -> Permutation BD B.
  Proof.   
  intros.
  rewrite (SetU_then_empty H2) in H1.
  rewrite (cxtDestruct BD).
  rewrite H.
  rewrite H1;sauto.
  rewrite <- cxtDestruct;auto.
  Qed.
      
End Properties.

Global Hint Resolve SubExpInhabitant : core.
Global Hint Constructors IsPositiveAtom : core.

