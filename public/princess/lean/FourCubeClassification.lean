import FourCubeAllLower
import FourCubeAllUpper

/-! Complete physical classification of the 4×4×4 box for every daily budget.
Zero in `turns` is the infeasibility sentinel, never a zero-day capture claim. -/
namespace Princess.FourCubeCompression
open Princess.CaptureRecurrence Princess.LadderCardinality
attribute [local irreducible] Princess.ProductCompression.iterateMap

def turns (m : Nat) : Nat :=
  if m≤7 then 0 else if m=8 then 40 else if m=9 then 20 else if m=10 then 16
  else if m=11 then 12 else if m=12 then 10 else if m≤14 then 8 else if m=15 then 7
  else if m≤17 then 6 else if m=18 then 5 else if m≤25 then 4 else if m≤31 then 3
  else if m≤63 then 2 else 1

theorem turns_large (m : Nat) (h : 64≤m) : turns m=1 := by
  simp only [turns,if_neg (show ¬m≤7 by omega),if_neg (show m≠8 by omega),
    if_neg (show m≠9 by omega),if_neg (show m≠10 by omega),if_neg (show m≠11 by omega),
    if_neg (show m≠12 by omega),if_neg (show ¬m≤14 by omega),if_neg (show m≠15 by omega),
    if_neg (show ¬m≤17 by omega),if_neg (show m≠18 by omega),if_neg (show ¬m≤25 by omega),
    if_neg (show ¬m≤31 by omega),if_neg (show ¬m≤63 by omega)]

theorem turns_two (m : Nat) (low : 32≤m) (high : m<64) : turns m=2 := by
  have h : ∀ m : Fin 64, 32≤m.val → turns m.val=2 := by decide
  exact h ⟨m,high⟩ low

theorem turns_positive (m : Nat) (h : 8≤m) : 0<turns m := by
  by_cases small : m<64
  · have hcheck : ∀ m : Fin 64, 8≤m.val → 0<turns m.val := by decide
    exact hcheck ⟨m,small⟩ h
  · rw [turns_large m (by omega)]; omega

theorem lower_selector : ∀ m : Fin 32, 9≤m.val → ∃ kind : Fin 10,
    m.val≤FourCubeTimeCounter.budget kind ∧ FourCubeTimeCounter.turns kind=turns m.val := by decide

theorem upper_selector : ∀ m : Fin 64, 8≤m.val → ∃ kind : Fin 12,
    upperBudget kind≤m.val ∧ upperTurns kind=turns m.val := by decide

theorem actual_lower_all (m last : Nat) (shots : Nat → Region Room)
    (budget : ∀ t, t<last+1 → card (shots t)≤m)
    (capture : GuaranteesAt adj (fun _ => True) shots last) : turns m≤last+1 := by
  by_cases impossible : m≤7
  · exact False.elim (actual_impossible_7 last shots
      (fun t ht => Nat.le_trans (budget t ht) impossible) capture)
  by_cases critical : m=8
  · subst m
    exact actual_lower_40 last shots budget capture
  by_cases small : m<32
  · have hm9 : 9≤m := by omega
    obtain ⟨kind,limit,hturns⟩ := lower_selector ⟨m,small⟩ hm9
    have h := actual_endpoint_lower kind last shots
      (fun t ht => Nat.le_trans (budget t ht) limit) capture
    rwa [hturns] at h
  by_cases middle : m<64
  · rw [turns_two m (by omega) middle]
    exact actual_lower_two m last shots middle budget capture
  · rw [turns_large m (by omega)]
    omega

theorem actual_upper_all (m : Nat) (feasible : 8≤m) : ∃ shots : Nat → Region Room,
    (∀ t, t<turns m → card (shots t)≤m) ∧
      GuaranteesAt adj (fun _ => True) shots (turns m-1) := by
  by_cases small : m<64
  · obtain ⟨kind,limit,hturns⟩ := upper_selector ⟨m,small⟩ feasible
    obtain ⟨shots,budget,capture⟩ := actual_endpoint_upper kind
    refine ⟨shots,?_,?_⟩
    · intro t ht
      exact Nat.le_trans (budget t (by rwa [hturns])) limit
    · rwa [hturns] at capture
  · rw [turns_large m (by omega)]
    exact actual_one_day m (by omega)

theorem can_capture_iff (m : Nat) :
    (∃ last : Nat, ∃ shots : Nat → Region Room,
      (∀ t, t<last+1 → card (shots t)≤m) ∧ GuaranteesAt adj (fun _ => True) shots last) ↔ 8≤m := by
  constructor
  · rintro ⟨last,shots,budget,capture⟩
    by_cases h : 8≤m
    · exact h
    · exact False.elim (actual_impossible_7 last shots
        (fun t ht => Nat.le_trans (budget t ht) (by omega)) capture)
  · intro h
    obtain ⟨shots,budget,capture⟩ := actual_upper_all m h
    refine ⟨turns m-1,shots,?_,capture⟩
    intro t ht
    have pos := turns_positive m h
    exact budget t (by omega)

/-- Matching construction and lower bound for every feasible natural budget. -/
theorem exact_minimum (m : Nat) (feasible : 8≤m) :
    (∃ shots : Nat → Region Room,
      (∀ t, t<turns m → card (shots t)≤m) ∧
        GuaranteesAt adj (fun _ => True) shots (turns m-1)) ∧
    (∀ last : Nat, ∀ shots : Nat → Region Room,
      (∀ t, t<last+1 → card (shots t)≤m) →
        GuaranteesAt adj (fun _ => True) shots last → turns m≤last+1) :=
  ⟨actual_upper_all m feasible,actual_lower_all m⟩

end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.can_capture_iff
#print axioms Princess.FourCubeCompression.exact_minimum
