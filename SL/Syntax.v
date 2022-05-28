(** * Syntax of MMLL
This file defines the syntax of formulas in MMLL
(type [oo]). Predicate [isFormula] determines when a term is a valid
MMLL formula (ruling out exotic terms). Proofs usually proceed by
induction on the fact that a term satisfies this property.
 *)

Require Export MMLL.Misc.UtilsTactics.
Require Export MMLL.Misc.Permutations.
Require Export MMLL.Misc.Hybrid.
Require Export MMLL.Misc.Database.
Require Export MMLL.SL.Signature.

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

Section LLSyntax.
 
  Context `{OLS: OLSig}.
  Context `{SI: Signature}.
  
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
  Inductive negativeFormula : oo -> Prop :=
  | RelNA1 : forall A,  negativeFormula (atom A)
  | RelTop : negativeFormula Top
  | RelBot : negativeFormula Bot
  | RelPar : forall F G, negativeFormula (MOr F G)
  | RelWith : forall F G, negativeFormula (AAnd F G)
  | RelQuest : forall F a, negativeFormula (Quest a F)
  | RelForall : forall FX, negativeFormula (All FX).

  (** Positive formulas (focusing persists *)
  Inductive positiveFormula : oo -> Prop :=
  | PosAt : forall A,  positiveFormula (perp A)
  | PosOne : positiveFormula One
  | PosZero : positiveFormula Zero
  | PosTensor : forall F G, positiveFormula (MAnd F G)
  | PosPlus : forall F G, positiveFormula (AOr F G)
  | PosBang : forall F a, positiveFormula (Bang a F)
  | PosEx : forall FX, positiveFormula (Some FX).

  (** Checking when a formulas has to be stored *)
  Inductive positiveLFormula : oo -> Prop :=
  | PosLAt : forall A,  positiveLFormula (atom A)
  | PosLPe : forall A,  positiveLFormula (perp A)
  | PosLOne : positiveLFormula One
  | PosLZero : positiveLFormula Zero
  | PosLTensor : forall F G, positiveLFormula (MAnd F G)
  | PosLPlus : forall F G, positiveLFormula (AOr F G)
  | PosLBang : forall F a, positiveLFormula (Bang a F)
  | PosLEx : forall FX, positiveLFormula (Some FX).

Theorem PositiveToLPositive : forall F,
      positiveFormula F -> positiveLFormula F.
    intros.
    inversion H;constructor.
  Qed.

  (** Every formula is either  a positive formula, or it must be released *)
  Theorem PositiveOrNegative : forall F,
      positiveFormula F \/ negativeFormula F.
    intros.
    destruct F;try (left;constructor);try(right;constructor).
  Qed.

Theorem PositiveNegativeSplit : forall M, exists M1 M2, 
    Forall positiveFormula M1 /\ Forall negativeFormula M2 /\ Permutation M (M1++M2).
  Proof with sauto. 
    induction M; intros...
    - exists nil. 
      exists nil...
    - destruct (PositiveOrNegative a)...
      { exists (a::x). 
        exists x0...
        rewrite H3... }
      { exists x. 
        exists (a::x0)...
        rewrite H3... }
  Qed.      
  
  (** Positive formulas cannot be released *)
   Theorem PositiveNotNegative: forall F,
      positiveFormula F -> ~ negativeFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  
 Theorem NegativeNotPositive : forall F,
      negativeFormula F -> ~ positiveFormula F.
    intros F H Hneg.
    inversion H;subst;inversion Hneg.
  Qed.
  
  (** The dual of a positive formula is a release formula *)
Theorem PositiveDualNegative : forall F,
      positiveFormula F -> negativeFormula (dual F).
    intros F Hpos.
    inversion Hpos;subst;constructor.
  Qed.

  Theorem NegativeDualPositive : forall F, negativeFormula F -> positiveFormula (dual F).
    intros F Hrel.
    inversion Hrel;subst;constructor.
  Qed.
  
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
    forall F, positiveLFormula F -> positiveFormula F \/ IsPositiveAtom F.
    intros.
    inversion H;auto; first [left;constructor
                             | right;constructor ].
  Qed.

Theorem PositiveAtomToNegativeFormula : forall F,
      IsPositiveAtom F -> negativeFormula F.
    intros.
    inversion H;constructor.
  Qed.
 
Theorem NetagiveAtomToPositiveFormula : forall F,
      IsNegativeAtom F -> positiveFormula F.
    intros.
    inversion H;constructor.
  Qed.
 
Theorem PositiveAtomToPositiveLFormula : forall F,
      IsPositiveAtom F -> positiveLFormula F.
    intros.
    inversion H;constructor.
  Qed.

Theorem positiveNotAtom F: positiveFormula F -> IsPositiveAtom F -> False.
Proof.
  intros.
  inversion H0;subst.
  inversion H.
 Qed.
 
   
  End LLSyntax.
 
Global Hint Constructors uniform_oo : core.
Global Hint Resolve Complexity0
                    DualComplexity: core.

Module LLNotations .
  Notation "'⊥'" := Bot.
  Notation "'⊤'" := Top.
  Notation "'1'" := One.
  Notation "'0'" := Zero.
  Notation "A ⊗ B" := (MAnd A B ) (at level 50) .
  Notation "A ⅋ B" := (MOr A B) (at level 50) .
  Notation "A ⊕ B" := (AOr A B) (at level 50) . 
  Notation "A & B" := (AAnd A B) (at level 50) .
  Notation "! A" := (Bang A) (at level 50) .
  Notation "? A" := (Quest A) (at level 50) .
  Notation " A ^ " := (dual A) (at level 10) .
  Notation "'∀{' FX '}'" := (All FX) (at level 10) .
  Notation "'∃{' FX '}'" := (Some FX) (at level 10) .
End LLNotations .

Global Hint Constructors IsPositiveAtom : core.

Global Hint Constructors 
    negativeFormula 
    positiveFormula
    positiveLFormula 
    uniform_oo isFormula IsPositiveAtom
    IsNegativeAtom: core.
    
Global Hint Resolve 
     PositiveToLPositive
     PositiveAtomToNegativeFormula
     PositiveAtomToPositiveLFormula
     NetagiveAtomToPositiveFormula 
     positiveNotAtom: core.    

Global Hint Unfold isFormulaL :core.

