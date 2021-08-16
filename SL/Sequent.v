(** * Focused Sequent system 
This file specifies a one-sided focused system for MMLL The system is
   parametric to [theory: oo->Prop], defining the formulas that can be used in
   rule [tri_dec3]. In this implementation, all the atoms are assumed to be
   positive and then, proofs must finish with the initial rule focusing on
   atomic propositions of the form [perp A]. The exchange rule is embedded in
   the definition, e.g., of [tri_tensor]. 
 *)


Require Export MMLL.Misc.Utils. 
Require Export MMLL.SL.Syntax.

Export ListNotations.
Set Implicit Arguments.

Section LLSequent.
  Context `{SI : Signature}.
  Context `{OLS: OLSig}.

 
  Variable theory : oo -> Prop. (* theory Definition *)

  (* Andreoli's triadic system for linear logic *)
  Reserved Notation " n '|-F-' B ';' L ';' X " (at level 80).

  (** Sequent rules. in [n '|-F-' B ';' L ';' X], [n] is the height of
  the derivation ; [B] a list representing the classical context ; [L]
  the linear context and [X] and [Arrow] that can be [DW F] (for the
  positive phase) or [UP L] (for the negative phase). *)
  Inductive seqN:  nat -> list TypedFormula -> multiset oo -> Arrow -> Prop :=
  | tri_init1 : forall B A n, SetU B -> n |-F- B ; [atom A] ; DW (perp A)
  | tri_init2 : forall B C A n i, SetU C -> mt i = true -> Permutation ((i, atom A)::C) B -> n |-F- B ; [] ; DW (perp A)
  | tri_one : forall B n, SetU B ->  n |-F- B ; [] ; DW One
  
  | tri_tensor : forall B D BD M N MN F G n, Permutation MN (M++N) -> 
                                      Permutation (getU BD) (getU B) ->
                                      Permutation (getU BD) (getU D) ->
                                      Permutation (getL BD) (getL B ++ getL D) ->
                                        (n |-F- B ; M ; DW F) ->
                                        (n |-F- D ; N ; DW G )->
                                        S n |-F- BD ; MN ; DW (MAnd F G)
                                        
  | tri_plus1 : forall B M F G n,
      n |-F- B ; M ; DW F -> S n |-F- B ; M ; DW (AOr F G)
  | tri_plus2 : forall B M F G n,
      n |-F- B ; M ; DW G -> S n |-F- B ; M ; DW (AOr F G)
  | tri_rel : forall B F L n,
      release F -> n |-F- B ; L ; UP [F] ->  S n |-F- B ; L ; DW F
  | tri_top : forall B L M n,
      n |-F- B ; L ; UP (Top :: M)
  | tri_bot : forall B L M n,
      n |-F- B ; L ; UP M -> S n  |-F- B ; L ; UP (Bot :: M)
  | tri_par : forall B L M F G n,
      n |-F- B ; L ; UP (F::G::M) -> S n  |-F- B ; L ; UP((MOr F G) :: M)
  | tri_with : forall B L M F G n,
      (n |-F- B ; L ; UP (F :: M)) ->
      (n |-F- B ; L ; UP (G :: M)) -> S n|-F- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest : forall B L M F n i,
      n |-F- (i,F)::B ; L ; UP M -> S n  |-F- B ; L ; UP ((Quest i F) :: M)         
  | tri_store : forall B L M F n,
      ~ asynchronous  F-> n |-F- B ; F::L ; UP M -> S n |-F- B ; L ; UP (F::M)
  | tri_dec1 : forall B L L' F n,
      ~IsPositiveAtom F -> Remove F L L' -> n |-F- B ; L' ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2u : forall B L F n i,
     u i = true -> mt i = true -> ~IsPositiveAtom F -> In (i,F) B -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec2l : forall B B' L F n i,
     u i = false -> mt i = true -> ~IsPositiveAtom F -> Remove (i,F) B B' -> n |-F- B' ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_dec3 : forall B L F n,
      theory F -> ~IsPositiveAtom F -> n |-F- B ; L ; DW F -> S n |-F- B ; L ; UP []
  | tri_ex  : forall B FX M t n,
      uniform_oo FX -> proper t -> n |-F- B; M ; DW (FX t) -> S n|-F- B; M ; DW (Some  FX)
  | tri_fx  : forall B L FX M n,
      uniform_oo FX -> (forall x, proper x -> n |-F- B ; L ; UP( (FX x) ::  M)) ->
      S n |-F- B ; L ; UP ((All FX) :: M)                                                                                                                           
  | tri_bangL : forall B F n,
     SetU B ->  n  |-F- B ; [] ; (UP [F]) -> S n  |-F- B ; [] ; DW (Bang loc F)
  | tri_bang : forall B F n i, i <> loc ->
     tri_bangK4 n B i [] [] (UP [F]) -> S n  |-F- B ; [] ; DW (Bang i F)
| tri_bangD : forall n B i,  tri_bangK4 n B i [] [] (UP [ ]) -> md i = true -> S n |-F- B ; [] ; UP []     
     with
      tri_bangK4 : nat -> list TypedFormula -> subexp -> list TypedFormula -> multiset oo -> Arrow -> Prop :=
       | tri_copyK4 : forall b F n L M C B B' i, lt i b  -> m4 b = true -> 
        Remove (b,F) B B' -> tri_bangK4 n B' i (C++[(plust b,F)]) L (UP M) -> 
                                          tri_bangK4 (S n) B i C L (UP M)
       | tri_copyUK : forall b F n L M C B B' i, lt i b  -> m4 b = false -> u b = true ->
        Remove (b,F) B B' -> tri_bangK4 n B' i (C++[(loc,F)]) L (UP M) -> 
                                          tri_bangK4 (S n) B i C L (UP M) 
       | tri_copyLK : forall b F n L M C B B' i, lt i b  -> m4 b = false -> u b = false ->
        Remove (b,F) B B' -> tri_bangK4 n B' i C L (UP (M++[F])) -> 
                                          tri_bangK4 (S n) B i C L (UP M)                                    
       | tri_exp : forall B C i L M n, SetU B ->
                  n |-F- C; L; UP M -> tri_bangK4 (S n) B i C L (UP M)
      
    

  where " n '|-F-' B ';' L ';' X " := (seqN n B L X).

   
  (** Well formedness conditions for arrows. *)
  Definition isArrow (Ar:Arrow) : Prop :=
    match Ar with
    | UP l => isFormulaL l
    | DW F => isFormula F
    end.
  
  Reserved Notation " '|-f-' B ';' L ';' X " (at level 80).

  (** The same system without the height of the derivation *)
  Inductive seq:  list TypedFormula -> multiset oo -> Arrow -> Prop :=
  | tri_init1' : forall B A ,  SetU B ->  |-f- B ; [atom A] ; DW (perp A)
  | tri_init2' : forall B C A i, SetU C -> mt i = true -> Permutation ((i, atom A)::C) B -> |-f- B ; [] ; DW (perp A)
  
  | tri_one' : forall B, SetU B -> |-f- B ; [] ; DW One
  | tri_tensor' : forall M N MN B D BD F G, Permutation MN (M++N) -> 
                                      Permutation (getU BD) (getU B) ->
                                      Permutation (getU BD) (getU D) ->
                                      Permutation (getL BD) (getL B ++ getL D) ->
                                       |-f- B ; M ; DW F ->
                                        |-f- D ; N ; DW G ->
                                        |-f- BD ; MN ; DW (MAnd F G)
  | tri_plus1' : forall B M F G ,
      |-f- B ; M ; DW F -> |-f- B ; M ; DW (AOr F G)
  | tri_plus2' : forall B M F G,
      |-f- B ; M ; DW G -> |-f- B ; M ; DW (AOr F G)
  | tri_rel' : forall B F L,
      release F -> |-f- B ; L ; UP [F] ->  |-f- B ; L ; DW F
  | tri_top' : forall B L M,
      |-f- B ; L ; UP (Top :: M)
  | tri_bot' : forall B L M,
      |-f- B ; L ; UP M -> |-f- B ; L ; UP (Bot :: M)
  | tri_par' : forall B L M F G,
      |-f- B ; L ; UP (F::G::M) -> |-f- B ; L ; UP((MOr F G) :: M)
  | tri_with' : forall B L M F G,
      |-f- B ; L ; UP (F :: M) ->
      |-f- B ; L ; UP (G :: M) -> |-f- B ; L ; UP ((AAnd F  G) :: M)
  | tri_quest' : forall B L M F i,
      |-f- (i,F)::B ; L ; UP M -> |-f- B ; L ; UP ((Quest i F) :: M)         
  | tri_store' : forall B L M F,
      ~ asynchronous  F-> |-f- B ; F::L; UP M -> |-f- B ; L ; UP (F::M)
  | tri_dec1' : forall B L L' F,
      ~IsPositiveAtom F -> Remove F L L' -> |-f- B ; L' ; DW F -> |-f- B ; L ; UP []
  | tri_dec2u' : forall B L F i,
     u i = true -> mt i = true -> ~IsPositiveAtom F -> In (i,F) B -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_dec2l' : forall B B' L F i,
     u i = false -> mt i = true -> ~IsPositiveAtom F -> Remove (i,F) B B' -> |-f- B' ; L ; DW F -> |-f- B ; L ; UP []

  | tri_dec3' : forall B L F ,
      theory F -> ~IsPositiveAtom F -> |-f- B ; L ; DW F -> |-f- B ; L ; UP []
  | tri_ex'  : forall B FX M t,
      uniform_oo FX -> proper t -> |-f- B; M ; DW (FX t) -> |-f- B; M ; DW (Some  FX)
  | tri_fx'  : forall B L FX M ,
      uniform_oo FX -> (forall x, proper x -> |-f- B ; L ; UP( (FX x) ::  M)) ->
      |-f- B ; L ; UP ((All FX) :: M) 
 | tri_bangL' : forall B F,
    SetU B -> |-f- B ; [] ; (UP [F]) -> |-f- B ; [] ; DW (Bang loc F)
                                                                                                                          
| tri_bang' : forall B F i, i <> loc -> 
     tri_bangK4' B i [] [] (UP [F]) -> |-f- B ; [] ; DW (Bang i F)
| tri_bangD' : forall B i,  tri_bangK4' B i [] [] (UP []) -> md i = true -> |-f- B ; [] ; UP []
     with
      tri_bangK4' : list TypedFormula -> subexp -> list TypedFormula -> multiset oo -> Arrow -> Prop :=
       | tri_copyK4' : forall b F L M C B B' i, lt i b  -> m4 b = true -> 
        Remove (b,F) B B' -> tri_bangK4' B' i (C++[(plust b,F)]) L (UP M) -> 
                                      tri_bangK4' B i C L (UP M)
       | tri_copyUK' : forall b F L M C B B' i, lt i b  -> m4 b = false -> u b = true ->
        Remove (b,F) B B' -> tri_bangK4' B' i (C++[(loc,F)]) L (UP M) -> 
                                      tri_bangK4' B i C L (UP M) 
        | tri_copyLK' : forall b F L M C B B' i, lt i b  -> m4 b = false -> u b = false ->
        Remove (b,F) B B' -> tri_bangK4' B' i C L (UP (M++[F])) -> 
                                      tri_bangK4' B i C L (UP M)                                      
       | tri_exp' : forall B C i L M , SetU B ->
                  |-f- C; L; UP M -> tri_bangK4' B i C L (UP M)

  where "'|-f-' B ';' L ';' X " := (seq B L X).

  
End LLSequent .

Module LLNotations .
  Notation "'bot'" := Bot.
  Notation "'top'" := Top.
  Notation "'one'" := One.
  Notation "'zero'" := Zero.
  Notation "A ** B" := (MAnd A B ) (at level 50) .
  Notation "A $ B" := (MOr A B) (at level 50) .
  Notation "A 'op' B" := (AOr A B) (at level 50) . 
  Notation "A & B" := (AAnd A B) (at level 50) .
  Notation "a ! A" := (Bang a A) (at level 60) .
  Notation "a ? A" := (Quest a A) (at level 60) .
  Notation " A ^ " := (dual A) (at level 10) .
  Notation " A -o B" := ( (A ^) $ (B) ) (at level 60).
  Notation "'F{' FX '}'" := (All FX) (at level 10) .
  Notation "'E{' FX '}'" := (Some FX) (at level 10) .

    
  (** Notation for arrows *)
  (**  Positive phase *)
  Notation ">> F" := (DW F) (at level 80)  .
  (** Negative phase *)
  Notation "> L" := (UP L) (at level 80) .
End LLNotations .

Global Hint Constructors seqN seq: core .
