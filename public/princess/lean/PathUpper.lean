import PathSweep

/-! Complete actual-room upper bound for every positive path size and budget.
The matching arbitrary-strategy lower theorem remains a separate obligation.
-/

namespace Princess.PathUpper

open Princess.PathGeometry
open Princess.PathSweep
open Princess.LadderCardinality
open Princess.CaptureRecurrence

def turns (n m : Nat) : Nat :=
  if n ≤ m then 1
  else if m = 1 then if n = 2 then 2 else 2 * n - 4
  else PathUpperArithmetic.correctedCeiling n m

theorem card_full (n : Nat) : card (fun _ : Fin n => True) = n := by
  exact (card_full_iff _).mpr (fun _ => True.intro)

theorem one_day_upper (n m : Nat) (hnm : n ≤ m) :
    winning adj (legal m) 1 (fun _ : Fin n => True) := by
  refine ⟨fun _ => True, ?_, ?_⟩
  · change card (fun _ : Fin n => True) ≤ m
    rw [card_full]; exact hnm
  · rintro v ⟨u, ⟨_, hu⟩, _⟩
    exact hu True.intro

theorem single_probe_upper (n : Nat) (hn : 3 ≤ n) :
    winning adj (legal 1) (2 * n - 4) (fun _ : Fin n => True) := by
  have run := first_batches (n := n) (m := 1) (q := n - 3) (R := n - 1)
    (p := n % 2) (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)
  have hend : n - 1 - (n - 3) * (2 * 1 - 1) = 2 := by omega
  have hpar : (n % 2 + (n - 3)) % 2 = 1 := by omega
  rw [hend, hpar] at run
  have start : (fun v : Fin n => parityPrefix (n - 1) v ∨ fullParity (n % 2) v) =
      (fun _ => True) := by
    rw [full_parity_prefix (by omega)]
    exact full_prefix_union (by omega)
  rw [start] at run
  have tail : winning adj (legal 1) (n - 2 + 1)
      (fun v : Fin n => parityPrefix 2 v ∨ fullParity 1 v) := by
    apply finish_first _ _ (fun _ => False)
    · rw [card_prefix 2 (by omega), card_empty]
      decide
    · have heq : next adj (fullParity (n := n) 1) (fun _ => False) = fullParity 0 := by
        unfold next
        simp only [not_false_eq_true, and_true]
        exact move_full_parity (by omega) 1 (by decide)
      rw [heq]
      apply full_sweep (by omega) (by decide) (by decide) (by omega)
      unfold bestFrontier
      split <;> omega
  have win := run.then_winning tail
  have count : n - 3 + (n - 2 + 1) = 2 * n - 4 := by omega
  rw [count] at win
  exact win

theorem single_edge_upper :
    winning adj (legal 1) 2 (fun _ : Fin 2 => True) := by
  have start : (fun v : Fin 2 => parityPrefix 1 v ∨ fullParity 0 v) =
      (fun _ => True) := by
    have h := full_prefix_union (n := 2) (by decide)
    have hp := full_parity_prefix (n := 2) (by decide)
    rw [← hp] at h
    exact h
  rw [← start]
  apply finish_first _ _ (fun _ => False)
  · rw [card_prefix 1 (by decide), card_empty]; decide
  · have heq : next adj (fullParity (n := 2) 0) (fun _ => False) = fullParity 1 := by
      unfold next
      simp only [not_false_eq_true, and_true]
      exact move_full_parity (by decide) 0 (by decide)
    rw [heq]
    exact full_sweep (by decide) (by decide) (by decide) (by decide) (by decide)

theorem path_upper (n m : Nat) (hn : 2 ≤ n) (hm : 1 ≤ m) :
    winning adj (legal m) (turns n m) (fun _ : Fin n => True) := by
  unfold turns
  split
  · exact one_day_upper n m ‹n ≤ m›
  · split
    · rename_i hm1
      subst m
      split
      · rename_i hn2; subst n; exact single_edge_upper
      · exact single_probe_upper n (by omega)
    · exact corrected_ceiling_upper n m (by omega) (by omega)

theorem winning_schedule_all {n : Nat} (m t : Nat) (B : Region (Fin n))
    (hw : winning adj (legal m) t B) :
    ∃ probes : Nat → Region (Fin n),
      (∀ i, legal m (probes i)) ∧ Empty (Princess.possible adj B probes t) := by
  induction t generalizing B with
  | zero =>
      exact ⟨fun _ _ => False, fun _ => by
        change card (fun _ : Fin n => False) ≤ m
        rw [card_empty]; omega, hw⟩
  | succ t ih =>
      obtain ⟨S, hS, tail⟩ := hw
      obtain ⟨probes, budget, clears⟩ := ih (next adj B S) tail
      refine ⟨prepend S probes, ?_, ?_⟩
      · intro i
        cases i with
        | zero => exact hS
        | succ i => exact budget i
      · rw [possible_prepend]
        exact clears

/-- Global budget on every round, and capture of every actual avoiding walk
by the claimed day. The isolated one-room path is handled without moving it. -/
theorem actual_path_upper (n m : Nat) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ probes : Nat → Region (Fin n),
      (∀ i, card (probes i) ≤ m) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes (turns n m - 1) := by
  by_cases hn1 : n = 1
  · subst n
    refine ⟨fun _ _ => True, ?_, ?_⟩
    · intro i; rw [card_full]; exact hm
    · intro v _
      exact True.intro
  · have hn2 : 2 ≤ n := by omega
    have hw := path_upper n m hn2 hm
    have positive : 1 ≤ turns n m := by
      by_cases hz : turns n m = 0
      · rw [hz] at hw
        exact False.elim (hw ⟨0, by omega⟩ True.intro)
      · omega
    obtain ⟨probes, budget, clears⟩ := winning_schedule_all m (turns n m) _ hw
    refine ⟨probes, budget, ?_⟩
    apply (Princess.guarantees_iff_next_empty adj (fun _ => True) probes
      (no_dead_ends hn2) (turns n m - 1)).mpr
    have ht : turns n m - 1 + 1 = turns n m := by omega
    rw [ht]
    exact clears

end Princess.PathUpper

#print axioms Princess.PathUpper.path_upper
#print axioms Princess.PathUpper.actual_path_upper
