import PathEvenRank
import PathOddBridge

/-! The complete original path classification, with actual finite-walk
semantics and an unrestricted global daily inspection budget. All geometric,
cardinality, rank, arithmetic, and construction obligations are proved in the
imported modules. Path size and inspection budget are positive. -/
namespace Princess.PathClassification
open Princess.PathGeometry Princess.PathSweep Princess.LadderCardinality
open Princess.CaptureRecurrence

/-- An arbitrary strategy guaranteeing capture by round k needs at least the
claimed number of days. Time zero denotes the first inspection round. -/
theorem actual_path_lower (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (probes : Nat → Region (Fin n)) (budget : ∀ i, card (probes i) ≤ m)
    (k : Nat) (capture : Princess.GuaranteesAt adj (fun _ => True) probes k) :
    PathUpper.turns n m ≤ k + 1 := by
  by_cases hn1 : n = 1
  · subst n
    simp only [PathUpper.turns, hm, if_true]
    omega
  · have hn2 : 2 ≤ n := by omega
    have empty := (Princess.guarantees_iff_next_empty adj (fun _ => True) probes
      (no_dead_ends hn2) k).mp capture
    by_cases even : n % 2 = 0
    · exact PathEvenRank.path_even_lower n m hn2 hm even probes budget (k + 1) empty
    · exact PathOddBridge.path_odd_lower n m hn2 hm (by omega) probes budget (k + 1) empty

theorem winning_later {n : Nat} (m t : Nat) (B : Region (Fin n))
    (hw : winning adj (legal m) t B) (extra : Nat) :
    winning adj (legal m) (t + extra) B := by
  induction extra with
  | zero => exact hw
  | succ extra ih =>
      have inhabited : ∃ S : Region (Fin n), legal m S := by
        refine ⟨fun _ => False, ?_⟩
        change card (fun _ : Fin n => False) ≤ m
        rw [card_empty]; omega
      exact winning_succ adj (legal m) inhabited (t + extra) B ih

/-- Exact minimum-time classification. Days are counted starting at one;
translations to the semantics therefore inspect at time days-1. -/
theorem can_capture_iff (n m days : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hdays : 1 ≤ days) :
    (∃ probes : Nat → Region (Fin n),
      (∀ i, card (probes i) ≤ m) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes (days - 1)) ↔
    PathUpper.turns n m ≤ days := by
  constructor
  · rintro ⟨probes, budget, capture⟩
    have h := actual_path_lower n m hn hm probes budget (days - 1) capture
    omega
  · intro bound
    by_cases hn1 : n = 1
    · subst n
      refine ⟨fun _ _ => True, ?_, fun _ _ => True.intro⟩
      intro i
      rw [PathUpper.card_full]
      exact hm
    · have hn2 : 2 ≤ n := by omega
      have hw := winning_later m (PathUpper.turns n m) (fun _ : Fin n => True)
        (PathUpper.path_upper n m hn2 hm) (days - PathUpper.turns n m)
      have hsum : PathUpper.turns n m + (days - PathUpper.turns n m) = days := by omega
      rw [hsum] at hw
      obtain ⟨probes, budget, empty⟩ := PathUpper.winning_schedule_all m days _ hw
      refine ⟨probes, budget, ?_⟩
      apply (Princess.guarantees_iff_next_empty adj (fun _ => True) probes
        (no_dead_ends hn2) (days - 1)).mpr
      have ht : days - 1 + 1 = days := by omega
      rw [ht]
      exact empty

/-- The prepared formula has both a physical witness and universal optimality. -/
theorem exact_minimum (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∃ probes : Nat → Region (Fin n),
      (∀ i, card (probes i) ≤ m) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes (PathUpper.turns n m - 1)) ∧
    (∀ probes : Nat → Region (Fin n), (∀ i, card (probes i) ≤ m) →
      ∀ k, Princess.GuaranteesAt adj (fun _ => True) probes k →
        PathUpper.turns n m ≤ k + 1) :=
  ⟨PathUpper.actual_path_upper n m hn hm, actual_path_lower n m hn hm⟩

end Princess.PathClassification
#print axioms Princess.PathClassification.actual_path_lower
#print axioms Princess.PathClassification.can_capture_iff
#print axioms Princess.PathClassification.exact_minimum
