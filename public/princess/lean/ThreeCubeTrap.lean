import CaptureRecurrence

/-! A small, kernel-evaluated geometric certificate for the 3 × 3 × 3 grid.
Rooms are the 27 coordinate triples encoded in base three. This file proves
the triple-neighborhood lemma and an actual-walk capture strategy using five
probes and eighteen rounds. The complete four-probe impossibility argument
from the cardinality invariant is written separately, not formalized here.
-/

namespace Princess.ThreeCubeTrap

abbrev Room := Fin 27

def x (v : Room) := v.val / 9
def y (v : Room) := v.val / 3 % 3
def z (v : Room) := v.val % 3
def color (v : Room) := (x v + y v + z v) % 2

def unit (a b : Nat) : Prop := a + 1 = b ∨ b + 1 = a

def adj (u v : Room) : Prop :=
  (unit (x u) (x v) ∧ y u = y v ∧ z u = z v) ∨
  (x u = x v ∧ unit (y u) (y v) ∧ z u = z v) ∨
  (x u = x v ∧ y u = y v ∧ unit (z u) (z v))

instance (a b : Nat) : Decidable (unit a b) := inferInstanceAs (Decidable (_ ∨ _))
instance (u v : Room) : Decidable (adj u v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def tripleNeighbors (a b c : Room) : Nat :=
  (List.finRange 27).countP (fun v => decide (adj a v ∨ adj b v ∨ adj c v))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem triple_neighborhood_seven :
    ∀ a b c : Room, a ≠ b → a ≠ c → b ≠ c →
      color a = color b → color a = color c → 7 ≤ tripleNeighbors a b c := by
  decide

def step (B S : List Room) : List Room :=
  (List.finRange 27).filter (fun v => decide (∃ u : Room, u ∈ B ∧ u ∉ S ∧ adj u v))

def run (B : List Room) : List (List Room) → List Room
  | [] => B
  | S :: rest => run (step B S) rest

def phase : List (List Room) :=
  [[1, 3, 5, 9, 11], [4, 6, 10, 12, 18], [5, 7, 11, 13, 15],
   [8, 10, 12, 14, 16], [9, 11, 13, 15, 17], [10, 12, 14, 16, 18],
   [11, 13, 15, 19, 21], [8, 14, 16, 20, 22], [15, 17, 21, 23, 25]]

def schedule := phase ++ phase

theorem schedule_length : schedule.length = 18 := by decide
theorem schedule_budget : ∀ S ∈ schedule, S.length ≤ 5 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem schedule_empty : run (List.finRange 27) schedule = [] := by decide

theorem no_dead_ends : ∀ v : Room, ∃ w, adj v w := by decide

/-- A set is legal exactly when some list of at most five rooms enumerates it.
Duplicates, if present, do not increase the number of inspected rooms. -/
def legal (S : Region Room) : Prop :=
  ∃ rooms : List Room, rooms.length ≤ 5 ∧ ∀ v, S v ↔ v ∈ rooms

theorem step_membership (B S : List Room) (v : Room) :
    v ∈ step B S ↔ CaptureRecurrence.next adj (fun u => u ∈ B) (fun u => u ∈ S) v := by
  simp only [step, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, hs, hadj⟩
    exact ⟨u, ⟨hu, hs⟩, hadj⟩
  · rintro ⟨u, ⟨hu, hs⟩, hadj⟩
    exact ⟨u, hu, hs, hadj⟩

theorem run_winning (shots : List (List Room)) (B : List Room)
    (budget : ∀ S ∈ shots, S.length ≤ 5) (clears : run B shots = []) :
    CaptureRecurrence.winning adj legal shots.length (fun v => v ∈ B) := by
  induction shots generalizing B with
  | nil =>
      change B = [] at clears
      subst B
      intro v hv
      exact List.not_mem_nil hv
  | cons S shots ih =>
      have tailBudget : ∀ Q ∈ shots, Q.length ≤ 5 :=
        fun Q hQ => budget Q (List.mem_cons_of_mem S hQ)
      have tailWin := ih (step B S) tailBudget clears
      have eqnext : (fun v => v ∈ step B S) =
          CaptureRecurrence.next adj (fun v => v ∈ B) (fun v => v ∈ S) := by
        funext v
        exact propext (step_membership B S v)
      rw [eqnext] at tailWin
      exact ⟨fun v => v ∈ S, ⟨S, budget S (List.mem_cons_self), fun _ => Iff.rfl⟩, tailWin⟩

theorem full_board_clears_eighteen :
    CaptureRecurrence.winning adj legal 18 (fun _ => True) := by
  have hw := run_winning schedule (List.finRange 27) schedule_budget schedule_empty
  have heq : (fun v : Room => v ∈ List.finRange 27) = (fun _ => True) := by
    funext v
    exact propext ⟨fun _ => True.intro, fun _ => List.mem_finRange v⟩
  rw [schedule_length, heq] at hw
  exact hw

theorem full_board_actual_capture :
    ∃ probes : Nat → Region Room,
      (∀ i, i < 18 → legal (probes i)) ∧ Princess.GuaranteesAt adj (fun _ => True) probes 17 :=
  (CaptureRecurrence.winning_iff_guarantees adj legal no_dead_ends 17 (fun _ => True)).mp
    full_board_clears_eighteen

end Princess.ThreeCubeTrap

#print axioms Princess.ThreeCubeTrap.triple_neighborhood_seven
#print axioms Princess.ThreeCubeTrap.schedule_empty
#print axioms Princess.ThreeCubeTrap.full_board_clears_eighteen
#print axioms Princess.ThreeCubeTrap.full_board_actual_capture
