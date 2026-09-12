import ThreeCubeLower

/-! Concrete exact-time upper schedules for the 3×3×3 grid. The schedules are
finite room lists whose complete neighborhood replay is checked by the Lean
kernel. No strategy-compression theorem is assumed. -/
namespace Princess.ThreeCubeTimeUpper
open Princess.ThreeCubeTrap Princess.ThreeCubeLower Princess.LadderCardinality
open Princess.CaptureRecurrence

def turns (m : Nat) : Nat :=
  if m ≤ 4 then 0 else if m = 5 then 18 else if m = 6 then 10
  else if m ≤ 8 then 6 else if m ≤ 11 then 4 else if m = 12 then 3
  else if m ≤ 26 then 2 else 1

def schedule6 : List (List Room) :=
  [[8, 14, 16, 20, 22, 26], [5, 7, 11, 13, 19, 25], [2, 4, 10, 16, 22, 24], [1, 7, 13, 15, 19, 21], [0, 4, 6, 10, 12, 18], [8, 14, 16, 20, 22, 26], [5, 7, 11, 13, 19, 25], [2, 4, 10, 16, 22, 24], [1, 7, 13, 15, 19, 21], [0, 4, 6, 10, 12, 18]]

theorem schedule6_length : schedule6.length = 10 := by decide
theorem schedule6_budget : ∀ S ∈ schedule6, S.length ≤ 6 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule6_empty : run (List.finRange 27) schedule6 = [] := by decide

def schedule7 : List (List Room) :=
  [[8, 14, 16, 20, 22, 24, 26], [5, 7, 11, 13, 15, 19, 21], [0, 2, 4, 6, 10, 12, 18], [8, 14, 16, 20, 22, 24, 26], [5, 7, 11, 13, 15, 19, 21], [0, 2, 4, 6, 10, 12, 18]]

theorem schedule7_length : schedule7.length = 6 := by decide
theorem schedule7_budget : ∀ S ∈ schedule7, S.length ≤ 7 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule7_empty : run (List.finRange 27) schedule7 = [] := by decide

def schedule9 : List (List Room) :=
  [[2, 4, 8, 14, 16, 20, 22, 24, 26], [1, 3, 7, 9, 11, 13, 15, 19, 21], [5, 7, 11, 13, 15, 17, 19, 23, 25], [0, 2, 4, 6, 10, 12, 18, 22, 24]]

theorem schedule9_length : schedule9.length = 4 := by decide
theorem schedule9_budget : ∀ S ∈ schedule9, S.length ≤ 9 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule9_empty : run (List.finRange 27) schedule9 = [] := by decide

def schedule12 : List (List Room) :=
  [[2, 4, 6, 8, 10, 12, 14, 16, 20, 22, 24, 26], [8, 14, 16, 20, 22, 24, 26, 1, 3, 9, 19, 21], [1, 3, 5, 7, 9, 11, 13, 15, 19, 21]]

theorem schedule12_length : schedule12.length = 3 := by decide
theorem schedule12_budget : ∀ S ∈ schedule12, S.length ≤ 12 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule12_empty : run (List.finRange 27) schedule12 = [] := by decide

def schedule13 : List (List Room) :=
  [[1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25], [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25]]

theorem schedule13_length : schedule13.length = 2 := by decide
theorem schedule13_budget : ∀ S ∈ schedule13, S.length ≤ 13 := by decide
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule13_empty : run (List.finRange 27) schedule13 = [] := by decide

theorem run_winning (m : Nat) (shots : List (List Room)) (B : List Room)
    (budget : ∀ S ∈ shots, S.length ≤ m) (clears : run B shots = []) :
    winning adj (atMost m) shots.length (fun v => v ∈ B) := by
  induction shots generalizing B with
  | nil =>
      change B = [] at clears
      subst B
      intro v hv
      exact List.not_mem_nil hv
  | cons S shots ih =>
      have tailBudget : ∀ Q ∈ shots, Q.length ≤ m :=
        fun Q hQ => budget Q (List.mem_cons_of_mem S hQ)
      have tailWin := ih (step B S) tailBudget clears
      have eqnext : (fun v => v ∈ step B S) =
          next adj (fun v => v ∈ B) (fun v => v ∈ S) := by
        funext v
        exact propext (step_membership B S v)
      rw [eqnext] at tailWin
      refine ⟨fun v => v ∈ S, ?_, tailWin⟩
      exact Nat.le_trans (list_bounds_card (fun v => v ∈ S) S (fun _ => Iff.rfl))
        (budget S List.mem_cons_self)

theorem schedule_winning (m : Nat) (shots : List (List Room))
    (budget : ∀ S ∈ shots, S.length ≤ m)
    (clears : run (List.finRange 27) shots = []) :
    winning adj (atMost m) shots.length (fun _ => True) := by
  have hw := run_winning m shots (List.finRange 27) budget clears
  have heq : (fun v : Room => v ∈ List.finRange 27) = (fun _ => True) := by
    funext v
    exact propext ⟨fun _ => True.intro, fun _ => List.mem_finRange v⟩
  rw [heq] at hw
  exact hw

theorem upper_5 (m : Nat) (hm : 5 ≤ m) :
    winning adj (atMost m) 18 (fun _ => True) := by
  have hw := schedule_winning m ThreeCubeTrap.schedule (by
    intro S hS; exact Nat.le_trans (ThreeCubeTrap.schedule_budget S hS) hm) ThreeCubeTrap.schedule_empty
  rw [ThreeCubeTrap.schedule_length] at hw
  exact hw

theorem upper_6 (m : Nat) (hm : 6 ≤ m) :
    winning adj (atMost m) 10 (fun _ => True) := by
  have hw := schedule_winning m schedule6 (by
    intro S hS; exact Nat.le_trans (schedule6_budget S hS) hm) schedule6_empty
  rw [schedule6_length] at hw
  exact hw

theorem upper_7 (m : Nat) (hm : 7 ≤ m) :
    winning adj (atMost m) 6 (fun _ => True) := by
  have hw := schedule_winning m schedule7 (by
    intro S hS; exact Nat.le_trans (schedule7_budget S hS) hm) schedule7_empty
  rw [schedule7_length] at hw
  exact hw

theorem upper_9 (m : Nat) (hm : 9 ≤ m) :
    winning adj (atMost m) 4 (fun _ => True) := by
  have hw := schedule_winning m schedule9 (by
    intro S hS; exact Nat.le_trans (schedule9_budget S hS) hm) schedule9_empty
  rw [schedule9_length] at hw
  exact hw

theorem upper_12 (m : Nat) (hm : 12 ≤ m) :
    winning adj (atMost m) 3 (fun _ => True) := by
  have hw := schedule_winning m schedule12 (by
    intro S hS; exact Nat.le_trans (schedule12_budget S hS) hm) schedule12_empty
  rw [schedule12_length] at hw
  exact hw

theorem upper_13 (m : Nat) (hm : 13 ≤ m) :
    winning adj (atMost m) 2 (fun _ => True) := by
  have hw := schedule_winning m schedule13 (by
    intro S hS; exact Nat.le_trans (schedule13_budget S hS) hm) schedule13_empty
  rw [schedule13_length] at hw
  exact hw

theorem upper_one (m : Nat) (hm : 27 ≤ m) :
    winning adj (atMost m) 1 (fun _ => True) := by
  refine ⟨fun _ => True, ?_, ?_⟩
  · have hc : card (fun _ : Room => True) = 27 :=
      (card_full_iff _).mpr (fun _ => True.intro)
    change card (fun _ : Room => True) ≤ m
    rw [hc]; exact hm
  · rintro v ⟨u, ⟨_, hu⟩, _⟩
    exact hu True.intro

theorem turns_positive (m : Nat) (hm : 5 ≤ m) : 1 ≤ turns m := by
  unfold turns
  split <;> (try split) <;> (try split) <;> (try split) <;>
    (try split) <;> (try split) <;> (try split) <;> omega

theorem winning_upper (m : Nat) (hm : 5 ≤ m) :
    winning adj (atMost m) (turns m) (fun _ => True) := by
  unfold turns
  split
  · omega
  · split
    · exact upper_5 m (by omega)
    · split
      · exact upper_6 m (by omega)
      · split
        · exact upper_7 m (by omega)
        · split
          · exact upper_9 m (by omega)
          · split
            · exact upper_12 m (by omega)
            · split
              · exact upper_13 m (by omega)
              · exact upper_one m (by omega)

theorem winning_schedule_all (m t : Nat) (B : Region Room)
    (hw : winning adj (atMost m) t B) :
    ∃ probes : Nat → Region Room,
      (∀ i, atMost m (probes i)) ∧ Empty (Princess.possible adj B probes t) := by
  induction t generalizing B with
  | zero =>
      exact ⟨fun _ _ => False, fun _ => by
        change card (fun _ : Room => False) ≤ m
        classical
        simp [card, cardOn], hw⟩
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

theorem actual_upper (m : Nat) (hm : 5 ≤ m) :
    ∃ probes : Nat → Region Room,
      (∀ i, atMost m (probes i)) ∧
      Princess.GuaranteesAt adj (fun _ => True) probes (turns m - 1) := by
  have hw := winning_upper m hm
  obtain ⟨probes, budget, clears⟩ := winning_schedule_all m (turns m) _ hw
  refine ⟨probes, budget, ?_⟩
  apply (Princess.guarantees_iff_next_empty adj (fun _ => True) probes
    no_dead_ends (turns m - 1)).mpr
  have positive := turns_positive m hm
  have ht : turns m - 1 + 1 = turns m := by omega
  rw [ht]
  exact clears

end Princess.ThreeCubeTimeUpper

#print axioms Princess.ThreeCubeTimeUpper.winning_upper
#print axioms Princess.ThreeCubeTimeUpper.actual_upper
