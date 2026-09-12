import FourCubeCompression

/-! Full physical diagonal normal form for every budget word on the 4-cube.
This module does not yet interpret the 292-state optimal-time certificate. -/
set_option maxRecDepth 20000

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.ProductCompression

attribute [local irreducible] iterateMap

 def operators : List (Operator adj) :=
  [op 0 false,op 0 true,op 1 false,op 1 true,op 2 false,op 2 true]

theorem operators_good : ∀ C ∈ operators, EnergyGood C energy := by
  intro C h
  simp only [operators,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h <;> subst C <;> apply op_energy

theorem operators_size : ∀ C ∈ operators, ∀ A, card (C.map A)=card A := by
  intro C h
  simp only [operators,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h | h | h <;> subst C <;> apply op_size

def normalizer : Princess.StrategyCompression.Compression adj where
  map := (normalize operators 1152).map
  mono := (normalize operators 1152).mono
  size := by
    intro A
    exact iterate_card (cycle operators) card (cycle_card operators card operators_size) 1152 A
  neighbors := (normalize operators 1152).neighbors

theorem normalizer_idempotent (A : Region Room) :
    normalizer.map (normalizer.map A)=normalizer.map A :=
  normalize_idempotent operators energy 1152 operators_good energy_bound A

theorem normalizer_common_fixed (A : Region Room) :
    ∀ C ∈ operators, C.map (normalizer.map A)=normalizer.map A :=
  normalized_common_fixed operators energy 1152 operators_good energy_bound A

theorem fixed_common (A : Region Room) (fixed : normalizer.map A=A) :
    ∀ C ∈ operators, C.map A=A := by
  have h := normalizer_common_fixed A
  rwa [fixed] at h

theorem full_fixed : normalizer.map (fun _ => True) = (fun _ => True) := by
  have hc := normalizer.size (fun _ => True)
  have fullcard : card (fun _ : Room => True) = 64 := (card_full_iff _).mpr (fun _ => trivial)
  rw [fullcard] at hc
  have hf := (card_full_iff _).mp hc
  funext v
  exact propext ⟨fun _ => trivial,fun _ => hf v⟩

theorem no_dead_ends : ∀ v : Room, ∃ w : Room, adj v w := by decide

/-- Every arbitrary finite daily budget word admits the common diagonal normal
form from any state fixed by the normalizer, in particular the full board. -/
theorem exact_budget_word_normal_form (ms : List Nat) (A : Region Room)
    (fixed : normalizer.map A=A) :
    Princess.StrategyCompression.wins adj ms A ↔
      Princess.StrategyCompression.fixedWins adj normalizer ms A :=
  Princess.StrategyCompression.fixed_winning_iff normalizer normalizer_idempotent ms A fixed

/-- Actual target walks on the 64 physical cube rooms, zero-based final round t. -/
theorem actual_capture_iff_normal_form (m t : Nat) :
    (∃ shots : Nat → Region Room,
      (∀ i, i < t+1 → card (shots i) ≤ m) ∧ GuaranteesAt adj (fun _ => True) shots t) ↔
      Princess.StrategyCompression.fixedWins adj normalizer (List.replicate (t+1) m) (fun _ => True) := by
  exact (Princess.StrategyCompression.fixed_iff_actual_capture adj no_dead_ends normalizer
    normalizer_idempotent m t (fun _ => True) full_fixed).symm

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.actual_capture_iff_normal_form
#print axioms Princess.FourCubeCompression.normalizer_common_fixed
