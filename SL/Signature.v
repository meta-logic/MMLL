Require Export MMLL.Misc.UtilsTactics.
Require Export MMLL.Misc.Database.

Require Export Coq.Classes.SetoidDec.

Require Export Coq.Classes.RelationClasses.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.DecidableClass.
Require Import Coq.Logic.FunctionalExtensionality.


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
  
#[global] Instance Lt_Reflexive `{Signature} : Reflexive lt.
Proof. apply @PreOrder_Reflexive;eauto. exact lt_pre. Qed.

#[global] Instance Lt_Transitive `{Signature} : Transitive lt.
Proof.  apply @PreOrder_Transitive;eauto. exact lt_pre. Qed.

(* All subexponentials are unbouded *)
Class UnbSignature `{Signature}:=
  { 
    allU: forall x, u x = true; }.

(* No subexponential has axiom D *)
Class UnbNoDSignature `{UnbSignature}:=
  { 
    allNoD: forall x, md x = false; }.

Section LLSignature.
 
  Context `{SI : Signature}.
  
  Lemma SubExpInhabitant : subexp.
  exact loc.
  Qed.
  
 Hint Resolve SubExpInhabitant : core.
  
  (** Decidibility on modalities *)
  Lemma subDec sub : forall x:subexp, {sub x = true} + {sub x = false}.
  Proof.
   intros;eauto using Sumbool.sumbool_of_bool.
  Qed.  
  
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
  
     Lemma plust_keeping4' : forall b a, m4 (plust a) = b -> m4 a = b.
  Proof.
  intros.
  destruct (mtDec a).
     apply plustpropT in e.
     rewrite <- e;auto.
     apply plustpropF in e.
     decompose [and] e;clear e. 
     rewrite <- H;auto.
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
 
  End LLSignature.
  
   Global Hint Resolve T_in_plust: ExBase.
Global Hint Resolve SubExpInhabitant : core.
Global Hint Resolve locNoD locNo4 locTDiff locUDiff: ExBase.
Global Hint Resolve plust_keeping4 plust_keeping4' plust_keepingu plust_keepingu': ExBase.

  
  Ltac solveSubExp :=
 auto;
  match goal with
    | [ |- u loc = true ] => apply locu 
  | [ |- mt loc = true ] => apply locT 
  | [ |- m4 loc = false ] => apply loc4 
  | [ |- mk loc = false ] => apply locK 
  | [ |- md loc = false ] => apply locD   
   | [SI : Signature, 
      H: u loc = false |- _] => rewrite locu in H; discriminate H   
   | [SI : Signature, 
      H: mk loc = false |- _] => rewrite locK in H; discriminate H  
   | [SI : Signature, 
      H: mt loc = false |- _] => rewrite locT in H; discriminate H 
   | [SI : Signature, 
      H: m4 loc = true |- _] => rewrite loc4 in H; discriminate H 
   | [SI : Signature,   
      H: md loc = true |- _] => rewrite locD in H; discriminate H 
   | [SI : Signature, H1: ?a <> loc, H2: lt ?a loc |- _] => 
      apply locAlone in H1;assert(False); [apply H1;left;auto|];contradiction
   | [SI : Signature, H1: ?a <> loc, H2: lt loc ?a |- _] => 
      apply locAlone in H1;assert(False); [apply H1;right;auto|];contradiction    
  end.
  




