  (** * Tactics for the focused system

The tactics defined in this module solves some of the repetitive goals
generated when the system is used. In particular those related
   to well-formedness conditions on formulas
 *)
Require Export MMLL.Misc.Utils.
Require Export MMLL.SL.Sequent.
Require Import MMLL.Misc.Permutations.

Export ListNotations.
Export LLNotations.
Set Implicit Arguments.

(* Section FLL. *)

(** Solves some efficiency problems related to rewriting with setoids *)
(* Remove Hints Equivalence.pointwise_equivalence : typeclass_instances. *)
#[global] Existing Instance Equivalence.pointwise_equivalence | 11.


Ltac solveIsFormula1 := auto;try
  match goal with
(*   | [ H1: isFormulaL (second ?L), H2: In (_,?P) ?L  |- isFormula ?P ] => apply isFormulaInS1 in H2;auto
 *) (*  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A _) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ _ ?A) ?L  |- isFormula ?A ] => apply isFormulaInS1 in H2;solveIsFormula1
  | [ H1: isFormulaL (second ?L), H2: In (_,_ ?A) ?L  |- isFormula (?A _) ] => apply isFormulaInS1 in H2;solveIsFormula1
  *)
 (*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,?P)::_)  |- isFormula ?P ] => apply isFormulaInS2 in H2;auto
  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A _)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  *)(*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ _ ?A)::_)  |- isFormula ?A ] => apply isFormulaInS2 in H2;solveIsFormula1
  *)(*  | [ H1: isFormulaL (second ?L), H2: Permutation ?L ((_,_ ?A)::_)  |- isFormula (?A _) ] => apply isFormulaInS2 in H2;solveIsFormula1
 *)
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th ?P  |- isFormula ?P ] => apply H1 in H2;auto
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A _)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ _ ?A)  |- isFormula ?A ] => apply H1 in H2;solveIsFormula1
  | [ H1: forall P:oo, ?th P -> isFormula P, H2: ?th (_ ?A)  |- isFormula (?A _) ] => apply H1 in H2;solveIsFormula1
 
  | [ H: isFormula (_ ?A _) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ _ ?A) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormula (_ ?A) |- isFormula (?A _) ] => inversion H;subst;eauto
  
  | [ H: isFormulaL ((_ ?A _)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ _ ?A)::_) |- isFormula ?A ] => inversion H;subst;auto
  | [ H: isFormulaL ((_ ?A)::_) |- isFormula (?A _) ] => inversion H;subst;eauto
end.

Ltac solveIsFormula2 := auto;try
  match goal with

  | [  |- isFormulaL (second (PlusT (getU _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (PlusT (getL _))) ] => try solve [apply isFormulaL_PlusT;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (Loc (getU _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (Loc (getL _))) ] => try solve [apply isFormulaL_Loc;apply isFormulaL_getL;auto]
  | [  |- isFormulaL (second (PlusT _)) ] => try solve [apply isFormulaL_PlusT;auto]
  | [  |- isFormulaL (second (Loc _)) ] => try solve [apply isFormulaL_Loc;auto]
  | [  |- isFormulaL (second (getU _)) ] => try solve [apply isFormulaL_getU;auto]
  | [  |- isFormulaL (second (getL _)) ] => try solve [apply isFormulaL_getL;auto]
  
  | [ H1: Permutation (getL ?mBD) (getL ?mB ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mD),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mD)] => eapply @isFormulaSecondSplit2 with (X:=nil) (Y:=nil) (BD:=mBD) (B:=mB);sauto
  | [ H1: Permutation (getL ?mBD) (getL ?Bm ++ getL ?mD), 
      H2: Permutation (getU ?mBD) (getU ?mB),
      H3: isFormulaL (second ?mBD)
      |- isFormulaL (second ?mB)] => eapply @isFormulaSecondSplit1 with (X:=nil) (Y:=nil) (BD:=mBD) (D:=mD);sauto
end.


Ltac SLFormulaSolve := auto; try solve[solveIsFormula1];
match goal with
 | [ |- isFormulaL ?K] => simpl;solveFoldFALL1 isFormula;solveIsFormula1
end.

Ltac SLSolve := try
 match goal with
 | |- isFormulaL (second ?K) => solveIsFormula2;SLFormulaSolve
 | |- isFormulaL ?K => SLFormulaSolve
    end.
 
Ltac solveUniform :=
  auto;
  repeat 
    match goal with
    | [|- uniform_oo _] =>  constructor 
    | [|- uniform _ ] => eauto 10  using uniform_id, uniform_con, uniform_app, proper_uniform, abstr_lambda
    | [|- uniform_atm _ ] => constructor
    | [|- proper _ ] => constructor
    | [|- level _ _ ] => constructor
    end.

   
Ltac cleanF :=
 repeat
 match goal with
  | [H: negativeFormula Top  |- _] => clear H
 | [H: negativeFormula Bot  |- _] => clear H
 | [H: negativeFormula (MOr _ _)  |- _] => clear H
 | [H: negativeFormula (atom _)  |- _] => clear H
 | [H: negativeFormula (All _)  |- _] => clear H
 | [H: negativeFormula (AAnd _ _)  |- _] => clear H
 | [H: negativeFormula (Quest _ _)  |- _] => clear H
 
 | [H: positiveFormula (perp _)  |- _] => clear H
 | [H: positiveFormula Zero  |- _] => clear H
 | [H: positiveFormula One  |- _] => clear H
 | [H: positiveFormula (MAnd _ _)  |- _] => clear H
 | [H: positiveFormula (Some _)  |- _] => clear H
 | [H: positiveFormula (AOr _ _)  |- _] => clear H
 | [H: positiveFormula (Bang _ _ )  |- _] => clear H 

 | [H: positiveLFormula (atom _)  |- _] => clear H
 | [H: positiveLFormula (perp _)  |- _] => clear H
 | [H: positiveLFormula Zero  |- _] => clear H
 | [H: positiveLFormula One  |- _] => clear H
 | [H: positiveLFormula (MAnd _ _)  |- _] => clear H
 | [H: positiveLFormula (Some _)  |- _] => clear H
 | [H: positiveLFormula (AOr _ _)  |- _] => clear H
 | [H: positiveLFormula (Bang _ _)  |- _] => clear H 
 
 
 | [H : ~ IsPositiveAtom (perp _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MOr _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (MAnd _ _) |- _ ] => clear H   
 | [H : ~ IsPositiveAtom (AAnd _ _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (AOr _ _) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Bang _ _) |- _ ] => clear H    
 | [H : ~ IsPositiveAtom (Quest _ _) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (All _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom (Some _ ) |- _ ] => clear H 
 | [H : ~ IsPositiveAtom Top |- _ ] => clear H    
 | [H : ~ IsPositiveAtom Bot |- _ ] => clear H 
 | [H : ~ IsPositiveAtom One |- _ ] => clear H 
 | [H : ~ IsPositiveAtom Zero |- _ ] => clear H  
    
    | [H : SetK [] |- _ ] => clear H
    | [H : SetK4 [] |- _ ] => clear H
    | [H : SetT [] |- _ ] => clear H
    | [H : SetU [] |- _ ] => clear H
    | [H : SetL [] |- _ ] => clear H   
  | [H : LtX ?a [] |- _ ] => clear H
  | [H : lt ?a ?a |- _ ] => clear H
  
 end.
 
(** This tactic solves most of the irrelevant goals in a focused
  proof (e.g., proving whether a formula is positive or not) *)
Ltac solveF :=
  sauto;
  let H := fresh "H" in
    match goal with
    | [|- ~ negativeFormula _] => intro H; solveF 
    | [|- ~ positiveFormula _] => intro H; solveF
    | [|- ~ positiveLFormula _] => intro H; solveF
    | [|- ~ IsPositiveAtom _ ] => intro H; solveF
    | [|- ~ IsNegativeAtom _ ] => intro H; solveF
    
    | [H: negativeFormula ?F  |- _] =>
      match F with
      | perp _ => inversion H      
      | MAnd _ _ => inversion H
      | AOr _ _ => inversion H
      | Some _ => inversion H
      | Bang _ _ => inversion H
      | Zero => inversion H
      | One => inversion H
      end
    | [H : positiveFormula ?F |- _ ] =>
      match F with
      | atom _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H      
      | All _ => inversion H
      | Quest _ _ => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : positiveLFormula ?F |- _ ] =>
      match F with
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | All _ => inversion H
      | Quest _ _ => inversion H
      | Bot => inversion H
      | Top => inversion H
    end
    | [H : IsPositiveAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ => inversion H
      | Quest _ _ => inversion H
      | perp _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : IsNegativeAtom ?F |- _ ] =>
      match F with
      | MAnd _ _ => inversion H
      | AAnd _ _ => inversion H
      | MOr _ _ => inversion H
      | AOr _ _ => inversion H
      | Bang _ _ => inversion H
      | Quest _ _ => inversion H
      | atom _ => inversion H
      | Some _ => inversion H
      | All _ => inversion H
      | Zero => inversion H
      | One => inversion H
      | Bot => inversion H
      | Top => inversion H
      end
    | [H : ~ IsPositiveAtom (atom _ ) |- _ ] => contradict H;auto
    | [H : ~ positiveLFormula (atom _ ) |- _ ] => contradict H;auto
    | [H : ~ positiveLFormula (perp _ ) |- _ ] => contradict H;auto
  
    | _  => idtac
    end;auto.

(** Splits the linear context L into L1 ++ L2 where L1 contains the first n elements of L *)
Ltac SplitContext n :=
  match goal with
  | [ |- seqN _ _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.

Ltac SplitContext' n :=
  match goal with
  | [ |- seq _ _ ?L _ ] =>
    let H := fresh "H" in
    let L1 := constr:(firstn n L) in
    let L2 := constr:(skipn n L) in
    let L1' := eval simpl in L1 in
        let L2' := eval simpl in L2 in
            let L3 := constr:(L1' ++ L2') in
            (assert(H : Permutation L L3) by auto using Permutation_midle, Permutation_midle_app);rewrite H;clear H 
  end.


(** Notation for forward reasoning on  sequents *)

(* Focusing on positive formulas *)
Tactic Notation "LFocus" := match goal with
    | [ |- seq _ _ (?P::?PL) _ ] =>  eapply @tri_dec1' with (F:= P) (L':=PL);[solveF | sauto | sauto ]
    | [|- seqN _ _ _ (?P::?PL) _] => eapply @tri_dec1 with (F:= P) (L':=PL);[solveF | sauto | sauto ]
end.

Tactic Notation "LFocus"  constr(R) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R);[solveF | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R);[solveF | sauto | sauto]
end.

Tactic Notation "LFocus"  constr(R) constr(T) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec1' with (F:= R) (L':=T);[solveF | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec1 with (F:= R) (L':=T);[solveF | sauto | sauto]
end.

(* Focusing on unbounded formulas *)
Tactic Notation "UFocus" := match goal with
    | [ |- seq _ ((?a,?P)::_) _ _ ] =>  eapply @tri_dec2u' with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- seqN _ _ ((?a,?P)::_) _ _] => eapply @tri_dec2u with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "UFocus"  constr(a) constr(S) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2u' with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec2u with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.

(* Focusing on bounded formulas *)
Tactic Notation "BFocus" := match goal with
    | [ |- seq _ ((?a,?P)::_) _ _ ] =>  eapply @tri_dec2l' with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- seqN _ _ ((?a,?P)::_) _ _] => eapply @tri_dec2l with (F:= P) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.

Tactic Notation "BFocus"  constr(a) constr(S) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec2l with (F:= S) (i:=a);[sauto | sauto | solveF | sauto | sauto ]
end.
                                                                     
Tactic Notation "BFocus"  constr(a) constr(S) constr(T):= match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec2l' with (F:= S) (i:=a) (B':= T);[sauto | sauto | solveF | sauto | sauto ]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec2l with (F:= S) (i:=a) (B':= T);[sauto | sauto | solveF | sauto | sauto ]
end.

(* Focusing on formulas in theory *)
Tactic Notation "TFocus"  constr(S) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_dec3' with (F:= S);[sauto | solveF | sauto]
    | [|- seqN _ _ _ _ _] => eapply @tri_dec3 with (F:= S);[ sauto | solveF | sauto]
end.

(* Multiplicative conjuction with bounded formulas *)
Tactic Notation "LLTensor"  constr(Ctx1) constr(Ctx2) constr(Ctx3) constr(Ctx4) := match goal with
                                                       | [ |- seq _ _ _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (D:=Ctx4);solveF
                                                       | [|- seqN _ _ _ _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=Ctx3) (D:=Ctx4);solveF
                                                       end.


(* Multiplicative conjuction with no bounded formulas *)
Tactic Notation "LLTensor"  constr(Ctx1) constr(Ctx2) := match goal with
               | [ |- seq _ ?C _ _ ] =>  eapply @tri_tensor' with (M:=Ctx1) (N:=Ctx2) (B:=C) (D:=C);solveF
               | [|- seqN _ _ ?C _ _] => eapply @tri_tensor with (M:=Ctx1) (N:=Ctx2) (B:=C) (D:=C);solveF
                 end.

Tactic Notation "LLTensor"  := match goal with
               | [ |- seq _ ?C [] _ ] =>  eapply @tri_tensor' with (M:=nil) (N:=nil) (B:=C) (D:=C);solveF
               | [|- seqN _ _ ?C [] _] => eapply @tri_tensor with (M:=nil) (N:=nil) (B:=C) (D:=C);solveF
                 end.

Lemma allSeTU (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) B : SetU B.
Proof with auto.
 induction B...
 apply Forall_cons... 
 apply allU.
Qed.

Lemma allSeTLEmpty (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) (B : list TypedFormula) : getL B = (@nil TypedFormula).
Proof with auto.
 rewrite (SetU_then_empty _ (allSeTU SIU B));auto.
Qed.

Lemma permSeTL (OLS: OLSig) (SI: Signature) (SIU: UnbSignature) (B : list TypedFormula) : Permutation (getL B) (getL B ++ getL B).
Proof with auto.
 rewrite allSeTLEmpty...
Qed.

Lemma permSeTL' (OLS: OLSig) (SI: Signature)  (B : list TypedFormula) : SetU B -> Permutation (getL B) (getL B ++ getL B).
Proof with auto.
  intros.
  simplEmpty...
Qed.

Global Hint Resolve allSeTU permSeTL permSeTL': core. 

 Lemma tensorU (OLS: OLSig) (SI : Signature) (USI : UnbSignature) n th B MN M N F G:          
  Permutation MN (M ++ N) ->
  seqN th n B M (DW F) ->
  seqN th n B N (DW G) -> seqN th (S n) B MN (DW (MAnd F  G)).
  Proof.   
  intros.
  LLTensor M N.
  Qed.

 Lemma tensorU' (OLS: OLSig) (SI : Signature) th B MN M N F G:    SetU B ->    
  Permutation MN (M ++ N) ->
  seq th B M (DW F) ->
  seq th B N (DW G) -> seq th B MN (DW (MAnd F G)).
  Proof.   
  intros.
  LLTensor M N.
  Qed.

(* Additive conjuction *)
Tactic Notation "LLWith" := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_with';sauto
    | [|- seqN _ _ _ _ _] => eapply @tri_with;sauto
end.

(* Additive disjuction *)
Tactic Notation "LLPlusL" := match goal with
                           | [ |- seq _ _ _ _ ] =>   apply tri_plus1';sauto
                           | [|- seqN _ _ _ _ _] =>  apply tri_plus1;sauto
                            end.

Tactic Notation "LLPlusR" := match goal with
   | [ |- seq _ _ _ _ ] =>   apply tri_plus2';sauto
   | [|- seqN _ _ _ _ _] =>  apply tri_plus2;sauto
end.

(* Multiplicative disjuction *)
Tactic Notation "LLPar" := match goal with
                         | [ |- seq _ _ _ _ ] =>  apply tri_par';sauto
                         | [|- seqN _ _ _ _ _] => apply tri_par;sauto
                         end.

(* Quantifiers *)
Tactic Notation "LLExists" constr(tt) :=  match goal with
   | [ |- seq _ _ _ _ ] => eapply @tri_ex' with (t:=tt);try solveUniform;sauto
   | [|- seqN _ _ _ _ _] => eapply @tri_ex with (t:=tt);try solveUniform;sauto
end.

Tactic Notation "LLForall" := match goal with
   | [ |- seq _ _ _ _ ] => eapply @tri_fx'; intros;sauto
   | [|- seqN _ _ _ _ _] => eapply @tri_fx; intros;sauto
end.

(* Storing formulas *)
Tactic Notation "LLStore" := match goal with
       | [ |- seq _ _ _ _ ] =>  apply tri_store';[solveF | auto]
       | [|- seqN _ _ _ _ _] => apply tri_store;[solveF | auto]
                           end. 

Tactic Notation "LLStoreC" := match goal with
       | [ |- seq _ _ _ _ ] =>  apply tri_quest';sauto
       | [|- seqN _ _ _ _ _] => apply tri_quest;sauto
                           end.

(* Changing to the negative phase *)
Tactic Notation "LLRelease" := match goal with
                         | [ |- seq _ _ _ _ ] =>  apply tri_rel';[solveF | auto]
                         | [|- seqN _ _ _ _ _] => apply tri_rel;[solveF | auto]
                         end. 

(* Axioms *)   
Tactic Notation "init1"  := match goal with
     | [ |- seq _ _ _ _ ] =>  apply tri_init1';try SLSolve;auto
     | [|- seqN _ _ _ _ _] => apply tri_init1;try SLSolve;auto
                          end.


Tactic Notation "init2" constr(a) constr(b) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_init2' with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
    | [|- seqN _ _ _ _ _] => eapply @tri_init2 with (i:=a) (C:=b);[try SLSolve | auto | try perm ];auto
                          end.

Tactic Notation "init2" constr(a) := match goal with
    | [ |- seq _ _ _ _ ] =>  eapply @tri_init2' with (i:=a)
   | [|- seqN _ _ _ _ _] => eapply @tri_init2 with (i:=a) 
                          end.
                          
Tactic Notation "init2" := match goal with
     | [ |- seq _ _ _ _ ] =>  eapply @tri_init2'
    | [|- seqN _ _ _ _ _] => eapply @tri_init2
                          end.

Tactic Notation "LLOne"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_one';SLSolve
                          | [|- seqN _ _ _ _ _] => apply tri_one;SLSolve
                          end.

Tactic Notation "LLTop"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_top'
                          | [|- seqN _ _ _ _ _] => apply tri_top
                          end.

(* Others rules *)
Tactic Notation "LLBot"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_bot';sauto
                          | [|- seqN _ _ _ _ _] => apply tri_bot;sauto
                          end.
                          
Tactic Notation "LLBang"  := match goal with
                          | [ |- seq _ _ _ _ ] =>  apply tri_bangL';sauto
                          | [|- seqN _ _ _ _ _] => apply tri_bangL;sauto
                          end.

Tactic Notation "createWorld" constr(a) := match goal with
                | [ |- seq _ _ _ _ ] => eapply @tri_bangD' with (i:=a); try solve [intro ;subst;solveSubExp];auto
                | [|- seqN _ _ _ _ _] => eapply @tri_bangD with (i:=a);try solve [intro ;subst;solveSubExp];auto
                                end.

Tactic Notation "createWorld" := match goal with
                | [ |- seq _ _ _ _ ] => eapply @tri_bang';sauto
                | [|- seqN _ _ _ _ _] => eapply @tri_bang;sauto
                end.

(* Exponential phase*)                

Tactic Notation "copyK4"  constr(i) constr(P) constr(B) := match goal with
    | [ |- tri_bangK4' _ _ _ _ _ _ ] => eapply @tri_copyK4' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | sauto | sauto]
 | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyK4 with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | sauto | sauto]
                                                       end;auto.

Tactic Notation "copyUK"  constr(i) constr(P) constr(B) := match goal with
| [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyUK' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]

| [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyUK with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
                                                                     end;auto. 
                                                       
Tactic Notation "copyLK"  constr(i) constr(P) constr(B) := match goal with
 | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_copyLK' with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
 | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_copyLK with (b:=i) (F:=P) (B':=B);[solveLT | solveSE | solveSE | sauto | sauto]
                                                       end;auto.   
                                                                                                            
   
Tactic Notation "finishExp"  := match goal with
   | [ |- tri_bangK4' _ _ _ _ _ _] => eapply @tri_exp';[solveF | sauto]
   | [|- tri_bangK4 _ _ _ _ _ _ _] => eapply @tri_exp;[solveF | sauto]
          end.
     
                          
(** This tactic applies as many positive/negative rules as
  possible. Connectives as exists and tensor are not automatically
  introduced (due to the decision on the contexts/terms ) *)
  
   Ltac negativePhaseReasoning :=
  try match goal with  
  | [ |- seq _ _ _ (UP  ((AAnd _ _)::_))] => LLWith 
  | [ |- seq _ _ _ (UP ((MOr ?F ?G)::_))] => LLPar
  | [ |- seq _ _ _ (UP ((Quest ?i) ?F :: _))] => LLStoreC
  | [ |- seq _ _ _ (UP (Bot :: _))] => LLBot
  | [ |- seq _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: positiveLFormula ?F |- seq _ _ _ (UP (?F :: ?M))] => LLStore
    | [|- seq _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLStore
      | MAnd _ _  => LLStore
      | Some _ =>LLStore
      | (atom _)  => LLStore
      | (perp _)  => LLStore
      | One  => LLStore
      | Zero => LLStore
      end
    end.

  Ltac negativePhaseReasoningN :=
  try match goal with  
  | [ |- seqN _ _ _ _ (UP  ((AAnd _ _)::_))] => LLWith 
  | [ |- seqN _ _ _ _ (UP ((MOr ?F ?G)::_))] => LLPar
  | [ |- seqN _ _ _ _ (UP ((Quest ?i) ?F :: _))] => LLStoreC
  | [ |- seqN _ _ _ _ (UP (Bot :: _))] => LLBot
  | [ |- seqN _ _ _ _ (UP ( (All _) :: _)) ] => let x:= fresh "x" in
                                              let xp := fresh "properX" in
                                              apply tri_fx' ; try solveUniform ; intros x xp

 (* Storing formulas *)
  | [H: positiveLFormula ?F |- seqN _ _ _ _ (UP (?F :: ?M))] => LLStore
    | [|- seqN _ _ _ _ (UP  (?F::_))] =>
      match F with
      | AOr _ _ => LLStore
      | MAnd _ _  => LLStore
      | Some _ =>LLStore
      | (atom _)  => LLStore
      | (perp _)  => LLStore
      | One  => LLStore
      | Zero => LLStore
      end
    end.

  Ltac positivePhaseReasoning :=
  try match goal with  
  | [USI : UnbSignature |- seq _ _ [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 
  | [H: seq ?th ?B ?L (DW ?F) |- seq ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusL 
  | [H: seq ?th ?B ?L (DW ?G) |- seq ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusR 
  | [ |- seq _ _ _ (DW (Bang loc _))] => apply tri_bangL';negativePhaseReasoning
 
     (* Change of polarity *)
    | [H: negativeFormula ?F |- seq _ _ _ (DW  ?F)] => LLRelease;negativePhaseReasoning
    | [|- seq _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLRelease;negativePhaseReasoning
      | All _ =>LLRelease;negativePhaseReasoning
      | Bot  => LLRelease;negativePhaseReasoning
      | (atom _)  => LLRelease;negativePhaseReasoning
      | Top  => LLRelease;negativePhaseReasoning
      | AAnd _ _  => LLRelease;negativePhaseReasoning
      | Quest _ _ => LLRelease;negativePhaseReasoning
      end
    end.
 
  Ltac positivePhaseReasoningN :=
  try match goal with  
  | [USI : UnbSignature |- seqN _ _ _ [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 
  | [H : SetU ?B |- seqN _ _ ?B [] (DW  (MAnd _ _))] => LLTensor (@nil oo)  (@nil oo) 

  | [H: seqN _ ?th ?B ?L (DW ?F) |- seqN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusL 
  | [H: seqN _ ?th ?B ?L (DW ?G) |- seqN _ ?th ?B ?L (DW (AOr ?F ?G))] => LLPlusR 
  | [ |- seqN _ _ _ _ (DW (Bang loc _))] => apply tri_bangL;negativePhaseReasoningN
 
     (* Change of polarity *)
    | [H: negativeFormula ?F |- seqN _ _ _ _ (DW  ?F)] => LLRelease;negativePhaseReasoningN
    | [|- seqN _ _ _ _ (DW  ?F)] =>
      match F with
      | MOr _ _ => LLRelease;negativePhaseReasoningN
      | All _ =>LLRelease;negativePhaseReasoningN
      | Bot  => LLRelease;negativePhaseReasoningN
      | (atom _)  => LLRelease;negativePhaseReasoningN
      | Top  => LLRelease;negativePhaseReasoningN
      | AAnd _ _  => LLRelease;negativePhaseReasoningN
      | Quest _ _ => LLRelease;negativePhaseReasoningN
      end
    end.
 
 
 
Lemma init2Cut (OLS : OLSig) (SI:Signature) i A L th :
SetU L -> mt i = true ->
In (i,atom A) L -> seq th L [] (DW (perp A)).
 Proof with sauto.
 intros.
 apply InPermutation in H1...
 rewrite H1 in H. 
 init2 i x. inversion H...
 Qed.

  Ltac solveAxioms :=
  try
    match goal with
   | [H: seq _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF
   | [ |- seq _ _ _ (DW One) ] => LLOne
   | [ |- seq _ _ [One] (UP [])] => LFocus;solveAxioms   
   | [ |- seq _ _ [] (UP [One]) ] => LLStore;LFocus;solveAxioms
  
   | [ |- seq _ _ [Top] (UP [])] => LFocus;LLRelease;solveAxioms   
   | [ |- seq _ _ _ (UP (Top :: ?M))] => LLTop
  (* initial rules *)
   | [ |- seq _ _ [atom ?A] (DW (perp ?A))] => init1
   | [ |- seq _ _ [perp ?A; atom ?A] (UP [])] => LFocus;solveAxioms   
   | [ |- seq _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];solveAxioms   

   | [ H: mt ?a = true |- seq _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => init2 a B
    | [ H: mt ?a = true |- seq _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a B
    | [ H: mt ?a = true |- seq _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a (X::B)
    | [ H: mt ?a = true |- seq _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (B++E)   
    | [ H: mt ?a = true |- seq _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- seq  _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- seq _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- seq _ ?D [] (DW (perp ?A))] => init2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- seq _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- seq _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- seq _ ?D [] (DW (perp ?A))] => init2 a (B++E)
 
    | [ H: SetU ?L, Hm: mt ?i = true, HIn: In (?i,atom ?A) ?L |- seq _ ?L [] (DW (perp ?A))] =>  try solve [refine (init2Cut i _ _ _ _ _);auto]
  
  end.

 Ltac solveAxiomsN :=
  try
    match goal with
 
   | [ |- seqN _ _ _ _ (DW One) ] => LLOne
   | [ |- seqN _ _ _  [One] (UP [])] => LFocus;solveAxiomsN   
   | [ |- seqN _ _ _ _ (UP (Top :: ?M))] => LLTop
 
     | [H: seqN _ _ _ _ (DW Zero) |- _ ] => inversion H;subst;solveF

    (* initial rules *)
   | [ |- seqN _ _ _ [atom ?A] (DW (perp ?A))] => init1
   | [ |- seqN _ _ _ [perp ?A; atom ?A] (UP [])] => LFocus;solveAxiomsN   
   | [ |- seqN _ _ _ [atom ?A; perp ?A] (UP [])] => LFocus (perp A) [atom A];solveAxiomsN   

   | [ H: mt ?a = true |- seqN _ _ ((?a,atom ?A)::?B) [] (DW (perp ?A))] => init2 a B
    | [ H: mt ?a = true |- seqN _ _ (?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a B
    | [ H: mt ?a = true |- seqN _ _ (?X::?B++[(?a,atom ?A)]) [] (DW (perp ?A))] => init2 a (X::B)
    | [ H: mt ?a = true |- seqN _ _ (?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (B++E)   
    | [ H: mt ?a = true |- seqN _ _ (?X::?B++(?a,atom ?A)::?E) [] (DW (perp ?A))] => init2 a (X::B++E)   
  
    | [ H: Permutation ((?a,atom _)::?B) ?D |- seqN _  _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++[(?a,atom ?A)]) ?D |- seqN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation (?B++(?a,atom ?A)::?E) ?D |- seqN _ _ ?D [] (DW (perp ?A))] => init2 a (B++E)

    | [ H: Permutation ?D ((?a,atom ?A)::?B)  |- seqN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++[(?a,atom ?A)])  |- seqN _ _ ?D [] (DW (perp ?A))] => init2 a B
    | [ H: Permutation ?D (?B++(?a,atom ?A)::?E)  |- seqN _ _ ?D [] (DW (perp ?A))] => init2 a (B++E)

    | [H: tri_bangK4 _ 0 _ _ _ _ _ |- _ ] => inversion H 
    
    | [H: seqN _ 0 _ _ (UP ( ?F::_)) |- _ ] =>
    match F with
      | Top => idtac
      | _ => inversion H
    end
   
    | [H: seqN _ 0 _ _ (DW ?F) |- _ ] =>
    match F with
      | One => idtac
      | perp _ => idtac
      | _ => inversion H
    end
 
   end.

 Ltac solvell :=
   match goal with
   | [ |- seqN _ _ _ _ (UP _) ] =>  negativePhaseReasoningN
   | [ |- seqN _ _ _ _ (DW _) ] =>  positivePhaseReasoningN
   end;solveAxiomsN.
 
 Ltac solvell' :=
   match goal with
   | [ |- seq _ _ _ (UP _) ] =>  negativePhaseReasoning
   | [ |- seq _ _ _ (DW _) ] =>  positivePhaseReasoning
   end;solveAxioms.
 
 Ltac solveLL :=
   match goal with
   | [ |- seq _ _ _ _ ] =>  solvell'
   | [ |- seqN _ _ _ _ _ ] =>  solvell
   end;auto.


(** Erasing some of the (unimportant) hypotheses added by the [solveF] and [solveLL] procedures *)

Ltac CleanContext :=
  sauto;cleanF;solveF;sauto.

