Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.
Section Matroids.

  (* Universe *)
  Parameter U : Type.
  (* Ground Set *)
  Parameter E : Ensemble U.
  (* A1: E is a finite set over universe U *)
  Parameter finite : Finite U E.

  (* I1: Independent set nonempty *)
  Definition I1 (I : Ensemble (Ensemble U)) :=
    I (Empty_set U).

  (* I2: Subsets of independent sets are independent *)
  Definition I2 (I : Ensemble (Ensemble U)) :=
    forall (A B : (Ensemble U)),
      I B /\ (Included U A B) -> I A.
  
  (* I3: If |A| < |B|, A can be extended to a larger
     independent set by adding an element from B.
     Note: This element will be in B - A, but since
     this is an existence statement, that's okay     *)
  Definition I3 (I : Ensemble (Ensemble U)) := 
    forall (A B : (Ensemble U)),
    forall (m n : nat),
      (I A /\ I B) /\
      ((cardinal U A m ) /\ (cardinal U B n)) /\
      m < n ->
        exists x : U, B x /\ I (Add U A x).

  Record Matroid : Type := {
    I : Ensemble (Ensemble U);
    M_I1 : I1 I;
    M_I2 : I2 I;
    M_I3 : I3 I
  }.

  Definition Bases_Independent (M : Matroid) (B : Ensemble U) :=
    I M B.

  (* Bases maximal
     For any base, adding an element from U or E yields
     non-independence.
     Note: independence means inclusion in a set within
     the independent set, no sets containing elements in
     U - E are in the independent set, so forall x : U 
     is also correct.                                     *)
  Definition Bases_Maximally_Independent (M : Matroid)(B : Ensemble U) :=
    forall x : U, ~ (I M (Add U B x)).

  Definition Base (M : Matroid) (B : Ensemble U) :=
    Bases_Independent M B /\ Bases_Maximally_Independent M B.

End Matroids.


