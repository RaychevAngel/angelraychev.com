import FourCubePotentialState

namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality
open Princess.StrategyCompression
attribute [local irreducible] Princess.ProductCompression.iterateMap

theorem normal_form_lower (ms : List Nat) (A : Region Room)
    (budgets : ∀ m∈ms, m≤8) (win : fixedWins adj normalizer ms A) :
    statePotential A ≤ 2*ms.length := by
  induction ms generalizing A with
  | nil =>
      rw [state_empty A win.2]
      exact Nat.le_refl 0
  | cons m ms ih =>
      obtain ⟨fixed,S,budget,rfix,tail⟩ := win
      have nextBound := ih (next adj A S) (fun k hk => budgets k (List.mem_cons_of_mem m hk)) tail
      have step := state_step A S (fixed_down_mask A fixed)
        (fixed_down_mask (fun v => A v ∧ ¬S v) rfix)
        (Nat.le_trans budget (budgets m List.mem_cons_self))
      simp only [List.length_cons]
      omega

theorem actual_lower_40 (last : Nat) (shots : Nat → Region Room)
    (budget : ∀ t, t<last+1 → card (shots t)≤8)
    (capture : GuaranteesAt adj (fun _ => True) shots last) : 40≤last+1 := by
  have normal := (actual_capture_iff_normal_form 8 last).mp ⟨shots,budget,capture⟩
  have bound := normal_form_lower (List.replicate (last+1) 8) (fun _ => True)
    (by intro m hm; have := List.eq_of_mem_replicate hm; omega) normal
  rw [state_full,List.length_replicate] at bound
  omega

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.actual_lower_40
