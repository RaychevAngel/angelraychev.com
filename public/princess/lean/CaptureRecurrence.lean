import BeliefSemantics

/-!
Exact recurrences and obstruction sets for invisible-target capture.

The admissible probes are an arbitrary predicate `legal`. In the finite graph
application this is `card S ≤ m`. The generic theorems assume neither a proposed
strategy shape nor a numerical capture-time formula. `winning t B` means that
some legal sequence makes the belief empty after exactly `t` transitions.
The final theorem connects this with actual walks, under the necessary
no-dead-ends hypothesis.
-/

namespace Princess.CaptureRecurrence

def Subset {V : Type} (A B : Region V) : Prop := ∀ v, A v → B v

def Empty {V : Type} (B : Region V) : Prop := ∀ v, ¬ B v

def next {V : Type} (adj : V → V → Prop) (B S : Region V) : Region V :=
  Princess.move adj (fun v => B v ∧ ¬ S v)

def winning {V : Type} (adj : V → V → Prop) (legal : Region V → Prop) :
    Nat → Region V → Prop
  | 0, B => Empty B
  | t + 1, B => ∃ S, legal S ∧ winning adj legal t (next adj B S)

def losing {V : Type} (adj : V → V → Prop) (legal : Region V → Prop)
    (B : Region V) : Prop := ∀ t, ¬ winning adj legal t B

def Trap {V : Type} (adj : V → V → Prop) (legal : Region V → Prop)
    (U : Region V → Prop) : Prop :=
  (∀ B, U B → ¬ Empty B) ∧
  (∀ B S, U B → legal S → U (next adj B S))

theorem next_mono {V : Type} (adj : V → V → Prop) (A B S : Region V)
    (h : Subset A B) : Subset (next adj A S) (next adj B S) := by
  intro v hv
  obtain ⟨u, ⟨hu, hs⟩, hadj⟩ := hv
  exact ⟨u, ⟨h u hu, hs⟩, hadj⟩

theorem winning_downward {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (t : Nat) (A B : Region V)
    (hAB : Subset A B) (hB : winning adj legal t B) : winning adj legal t A := by
  induction t generalizing A B with
  | zero => exact fun v hv => hB v (hAB v hv)
  | succ t ih =>
      obtain ⟨S, hS, hB⟩ := hB
      exact ⟨S, hS, ih (next adj A S) (next adj B S) (next_mono adj A B S hAB) hB⟩

theorem losing_upward {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (A B : Region V) (hAB : Subset A B)
    (hA : losing adj legal A) : losing adj legal B := by
  intro t hB
  exact hA t (winning_downward adj legal t A B hAB hB)

theorem losing_is_trap {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) : Trap adj legal (losing adj legal) := by
  constructor
  · intro B hB hEmpty
    exact hB 0 hEmpty
  · intro B S hB hS t ht
    exact hB (t + 1) ⟨S, hS, ht⟩

theorem trap_excludes_winning {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (U : Region V → Prop) (hU : Trap adj legal U)
    (t : Nat) (B : Region V) (hB : U B) : ¬ winning adj legal t B := by
  induction t generalizing B with
  | zero => exact hU.1 B hB
  | succ t ih =>
      intro hw
      obtain ⟨S, hS, hw⟩ := hw
      exact ih (next adj B S) (hU.2 B S hB hS) hw

theorem losing_iff_trap {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (B : Region V) :
    losing adj legal B ↔ ∃ U, Trap adj legal U ∧ U B := by
  constructor
  · intro hB
    exact ⟨losing adj legal, losing_is_trap adj legal, hB⟩
  · rintro ⟨U, hU, hB⟩ t
    exact trap_excludes_winning adj legal U hU t B hB

/-- The losing set is the greatest probe-closed set excluding the empty belief. -/
theorem every_trap_subset_losing {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (U : Region V → Prop) (hU : Trap adj legal U) :
    ∀ B, U B → losing adj legal B := by
  intro B hB t
  exact trap_excludes_winning adj legal U hU t B hB

def upward {V : Type} (F : Region V → Prop) (B : Region V) : Prop :=
  ∃ A, F A ∧ Subset A B

/-- A small family of incomparable lower barriers can certify impossibility.
Only transitions out of the generators need checking; monotonicity supplies
all their supersets. Incomparability is useful for compression, not required. -/
theorem trap_from_generators {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (F : Region V → Prop)
    (hne : ∀ A, F A → ¬ Empty A)
    (hclosed : ∀ A S, F A → legal S → upward F (next adj A S)) :
    Trap adj legal (upward F) := by
  constructor
  · rintro B ⟨A, hA, hAB⟩ hB
    exact hne A hA (fun v hv => hB v (hAB v hv))
  · rintro B S ⟨A, hA, hAB⟩ hS
    obtain ⟨C, hC, hCA⟩ := hclosed A S hA hS
    exact ⟨C, hC, fun v hv => next_mono adj A B S hAB v (hCA v hv)⟩

theorem winning_succ {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (inhabited : ∃ S, legal S)
    (t : Nat) (B : Region V) (h : winning adj legal t B) :
    winning adj legal (t + 1) B := by
  induction t generalizing B with
  | zero =>
      obtain ⟨S, hS⟩ := inhabited
      refine ⟨S, hS, ?_⟩
      rintro v ⟨u, ⟨hu, _⟩, _⟩
      exact h u hu
  | succ t ih =>
      obtain ⟨S, hS, hW⟩ := h
      exact ⟨S, hS, ih (next adj B S) hW⟩

/-- The inverse of open neighborhood inclusion, using outgoing edges. -/
def erosion {V : Type} (adj : V → V → Prop) (D : Region V) : Region V :=
  fun v => ∀ w, adj v w → D w

theorem next_subset_iff {V : Type} (adj : V → V → Prop) (B S D : Region V) :
    Subset (next adj B S) D ↔ Subset B (fun v => erosion adj D v ∨ S v) := by
  classical
  constructor
  · intro h v hv
    by_cases hs : S v
    · exact Or.inr hs
    · exact Or.inl (fun w hadj => h w ⟨v, ⟨hv, hs⟩, hadj⟩)
  · intro h w hw
    obtain ⟨v, ⟨hv, hs⟩, hadj⟩ := hw
    rcases h v hv with he | hS
    · exact he w hadj
    · exact False.elim (hs hS)

/-- Exact backward recurrence; no optimality of any geometric order is assumed. -/
theorem winning_backward {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (t : Nat) (B : Region V) :
    winning adj legal (t + 1) B ↔
      ∃ D, winning adj legal t D ∧
        ∃ S, legal S ∧ Subset B (fun v => erosion adj D v ∨ S v) := by
  constructor
  · rintro ⟨S, hS, hW⟩
    exact ⟨next adj B S, hW, S, hS,
      (next_subset_iff adj B S (next adj B S)).mp (fun _ h => h)⟩
  · rintro ⟨D, hD, S, hS, hBD⟩
    exact ⟨S, hS, winning_downward adj legal t (next adj B S) D
      ((next_subset_iff adj B S D).mpr hBD) hD⟩

/-- Any generating family for the downward-closed winning set can be used.
In a finite graph one may take precisely its inclusion-maximal beliefs. -/
theorem winning_generators {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (t : Nat) (F : Region V → Prop)
    (hF : ∀ B, winning adj legal t B ↔ ∃ D, F D ∧ Subset B D)
    (B : Region V) :
    winning adj legal (t + 1) B ↔
      ∃ D, F D ∧ ∃ S, legal S ∧ Subset B (fun v => erosion adj D v ∨ S v) := by
  constructor
  · rintro ⟨S, hS, hW⟩
    obtain ⟨D, hD, hBD⟩ := (hF (next adj B S)).mp hW
    exact ⟨D, hD, S, hS, (next_subset_iff adj B S D).mp hBD⟩
  · rintro ⟨D, hD, S, hS, hBD⟩
    exact ⟨S, hS, (hF (next adj B S)).mpr
      ⟨D, hD, (next_subset_iff adj B S D).mpr hBD⟩⟩

def prepend {V : Type} (S : Region V) (probes : Nat → Region V) : Nat → Region V
  | 0 => S
  | i + 1 => probes i

theorem possible_prepend {V : Type} (adj : V → V → Prop) (B S : Region V)
    (probes : Nat → Region V) (t : Nat) :
    Princess.possible adj B (prepend S probes) (t + 1) =
      Princess.possible adj (next adj B S) probes t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change (Princess.move adj (fun v =>
        Princess.possible adj B (prepend S probes) (t + 1) v ∧ ¬ probes t v)) =
        Princess.move adj (fun v =>
          Princess.possible adj (next adj B S) probes t v ∧ ¬ probes t v)
      rw [ih]

theorem possible_tail {V : Type} (adj : V → V → Prop) (B : Region V)
    (probes : Nat → Region V) (t : Nat) :
    Princess.possible adj B probes (t + 1) =
      Princess.possible adj (next adj B (probes 0)) (fun i => probes (i + 1)) t := by
  have heq : probes = prepend (probes 0) (fun i => probes (i + 1)) := by
    funext i
    cases i <;> rfl
  calc
    Princess.possible adj B probes (t + 1) =
        Princess.possible adj B (prepend (probes 0) (fun i => probes (i + 1))) (t + 1) :=
      congrArg (fun p => Princess.possible adj B p (t + 1)) heq
    _ = _ := possible_prepend adj B (probes 0) (fun i => probes (i + 1)) t

theorem winning_iff_schedule {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (t : Nat) (B : Region V) :
    winning adj legal t B ↔
      ∃ probes : Nat → Region V,
        (∀ i, i < t → legal (probes i)) ∧ Empty (Princess.possible adj B probes t) := by
  induction t generalizing B with
  | zero =>
      constructor
      · intro h
        exact ⟨fun _ _ => False, fun i hi => False.elim (Nat.not_lt_zero i hi), h⟩
      · rintro ⟨_, _, h⟩
        exact h
  | succ t ih =>
      constructor
      · rintro ⟨S, hS, hW⟩
        obtain ⟨probes, hlegal, hempty⟩ := (ih (next adj B S)).mp hW
        refine ⟨prepend S probes, ?_, ?_⟩
        · intro i hi
          cases i with
          | zero => exact hS
          | succ i => exact hlegal i (Nat.lt_of_succ_lt_succ hi)
        · rw [possible_prepend]
          exact hempty
      · rintro ⟨probes, hlegal, hempty⟩
        refine ⟨probes 0, hlegal 0 (Nat.zero_lt_succ t), ?_⟩
        apply (ih (next adj B (probes 0))).mpr
        refine ⟨fun i => probes (i + 1), ?_, ?_⟩
        · intro i hi
          exact hlegal (i + 1) (Nat.succ_lt_succ hi)
        · rw [possible_tail] at hempty
          exact hempty

/-- End-to-end interpretation as capture of every actual surviving walk.
The day index is zero-based: `t + 1` transitions correspond to rounds `0,...,t`. -/
theorem winning_iff_guarantees {V : Type} (adj : V → V → Prop)
    (legal : Region V → Prop) (noDeadEnds : ∀ v, ∃ w, adj v w)
    (t : Nat) (B : Region V) :
    winning adj legal (t + 1) B ↔
      ∃ probes : Nat → Region V,
        (∀ i, i < t + 1 → legal (probes i)) ∧ Princess.GuaranteesAt adj B probes t := by
  rw [winning_iff_schedule]
  constructor
  · rintro ⟨probes, hlegal, hempty⟩
    exact ⟨probes, hlegal,
      (Princess.guarantees_iff_next_empty adj B probes noDeadEnds t).mpr hempty⟩
  · rintro ⟨probes, hlegal, hcapture⟩
    exact ⟨probes, hlegal,
      (Princess.guarantees_iff_next_empty adj B probes noDeadEnds t).mp hcapture⟩

end Princess.CaptureRecurrence

#print axioms Princess.CaptureRecurrence.winning_downward
#print axioms Princess.CaptureRecurrence.losing_iff_trap
#print axioms Princess.CaptureRecurrence.every_trap_subset_losing
#print axioms Princess.CaptureRecurrence.trap_from_generators
#print axioms Princess.CaptureRecurrence.winning_succ
#print axioms Princess.CaptureRecurrence.next_subset_iff
#print axioms Princess.CaptureRecurrence.winning_backward
#print axioms Princess.CaptureRecurrence.winning_generators
#print axioms Princess.CaptureRecurrence.winning_iff_schedule
#print axioms Princess.CaptureRecurrence.winning_iff_guarantees
