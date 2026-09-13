import RobustTwoMove

/-! Explicit dense endpoint at order eleven. Every missing pair has a safe
intermediary, checked by kernel reduction. This is a concrete finite theorem;
the general dense families remain ordinary proofs. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.ElevenVertexDense
abbrev Vertex := Fin 11

def missing (s t : Vertex) : Prop :=
  (s.val = 0 ∧ (t.val = 4 ∨ t.val = 8)) ∨
  (s.val = 1 ∧ (t.val = 9 ∨ t.val = 10)) ∨
  (s.val = 2 ∧ (t.val = 8 ∨ t.val = 9)) ∨
  (s.val = 3 ∧ (t.val = 7 ∨ t.val = 10)) ∨
  (s.val = 4 ∧ (t.val = 0 ∨ t.val = 1)) ∨
  (s.val = 5 ∧ (t.val = 2 ∨ t.val = 6)) ∨
  (s.val = 6 ∧ (t.val = 3 ∨ t.val = 5)) ∨
  (s.val = 7 ∧ (t.val = 3 ∨ t.val = 4)) ∨
  (s.val = 8 ∧ (t.val = 2 ∨ t.val = 7)) ∨
  (s.val = 9 ∧ (t.val = 0 ∨ t.val = 5)) ∨
  (s.val = 10 ∧ (t.val = 1 ∨ t.val = 6))
instance (s t : Vertex) : Decidable (missing s t) :=
  inferInstanceAs (Decidable (_ ∨ _))

def edge (s t : Vertex) : Prop := s ≠ t ∧ ¬ missing s t
instance (s t : Vertex) : Decidable (edge s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem witnesses : RobustTwoMove.Witnesses edge edge := by
  unfold RobustTwoMove.Witnesses
  decide +kernel

theorem all_pairs_actual_delivery {s t c : Vertex} (initial : c ≠ s)
    (cop : PursuerPolicy Vertex) (legal : LegalPursuer edge cop)
    (history : History Vertex) :
    play edge t cop 2 history s c = .delivered := by
  exact RobustTwoMove.envelope_actual_delivery (fun _ _ h => h)
    (fun _ _ h => h) witnesses initial cop legal history

def allPairs : List (Vertex × Vertex) :=
  (List.finRange 11).flatMap fun s => (List.finRange 11).map fun t => (s,t)

theorem arc_count :
    (allPairs.filter fun p => decide (edge p.1 p.2)).length = 88 := by
  decide +kernel

theorem indirect_count :
    (allPairs.filter fun p => decide (p.1 ≠ p.2 ∧ ¬ edge p.1 p.2)).length = 22 := by
  decide +kernel

#print axioms witnesses
#print axioms all_pairs_actual_delivery
#print axioms arc_count
#print axioms indirect_count
end Delivery.ElevenVertexDense
