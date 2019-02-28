Require Export Matroids.

(* The following proof has been heavily annotated for clarity   *)

(* Show contradiction on |A| < |B|, proof symmetric for 
   |B| < |A| yielding contradiction on |A| <> |B|, so |A| = |B| 
   forall bases A, B                                            *)
Theorem Bases_Equicardinal 
  (M : Matroid)(A B : Ensemble U)(m n : nat):
    ((Base M A) /\ (Base M B)) /\
    ((cardinal U A m) /\ (cardinal U B n)) /\
    (m < n) -> False.
Proof. 
  (* Break goal into the antecedent and consequent of the 
     implication                                                *)
  intro Antecedent.

  (* Seperate Antecedent into a statement about A B being bases 
     and m n being their cardinality. Seperate statements about 
     A and B out.                                               *)
  destruct Antecedent as [ AntBases AntCardinal ]; 
  destruct AntBases as [ Base_A Base_B ].

  (* Seperate statements about A being a base, B being a base
     into statements about A, B being independent and maximally
     independent                                                *)
  destruct Base_A as [ Independent_A Maximally_Independent_A ]; 
  destruct Base_B as [ Independent_B Maximally_Independent_B].

  (* Forward reasoning: since A, B are Ensemble U, and m, n are
     nats, we can apply them to M.(M_I3) to get the contents of
     the statement of the axiom                                 *)
  pose (HContra := 
    M.(M_I3) A B m n).

  (* Forward reasoning: Since we have proofs of I A, I B, and
     HCardinal seperately, we can construct the antecedent of I3
     directly with conjunction                                  *)
  pose (HContra_Antecedent := 
    conj (conj Independent_A Independent_B) AntCardinal).

  (* We can apply the antecedent of the I3 axiom to get it's
     consequent, "exists x : U, B x /\ I (Add U A x)."          *)
  pose (Exists_Element := 
    HContra HContra_Antecedent).

  (* In 'destructing' Exists_Element, we get a witness of the
     existential statement and the conditions it witnesses      *)
  destruct Exists_Element as [ Witness Condition ].

  (* Construct the statement that adding the witness to A 
     yields independence, which is False.                       *)
  apply (Maximally_Independent_A Witness).

  (* From here Coq does the rest of the work, conducting a
     tree search to find some function that constructs the
     goal.                                                      *)
  intuition.
Qed.