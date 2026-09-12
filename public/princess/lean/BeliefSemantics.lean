import Std

/-!
General semantics for the invisible moving-target game.

A probe round occurs before the compulsory edge move. Time zero is the
first round. `Reachable` describes an actual finite legal walk avoiding all
earlier probes; `possible` is the set-valued computation. The equivalence
below is the semantic bridge, independent of any particular graph or solver.
No classification or running-time formula is assumed here.
-/

namespace Princess

abbrev Region (V : Type) := V → Prop

def move {V : Type} (adj : V → V → Prop) (B : Region V) : Region V :=
  fun v => ∃ u, B u ∧ adj u v

def possible {V : Type} (adj : V → V → Prop) (initial : Region V)
    (probes : Nat → Region V) : Nat → Region V
  | 0 => initial
  | t + 1 => move adj (fun v => possible adj initial probes t v ∧ ¬ probes t v)

/-- An actual legal walk arriving at time `t`, having missed rounds `0,...,t-1`. -/
inductive Reachable {V : Type} (adj : V → V → Prop) (initial : Region V)
    (probes : Nat → Region V) : Nat → V → Prop
  | start {v} : initial v → Reachable adj initial probes 0 v
  | step {t u v} : Reachable adj initial probes t u → ¬ probes t u →
      adj u v → Reachable adj initial probes (t + 1) v

theorem possible_iff_reachable {V : Type} (adj : V → V → Prop)
    (initial : Region V) (probes : Nat → Region V) (t : Nat) (v : V) :
    possible adj initial probes t v ↔ Reachable adj initial probes t v := by
  induction t generalizing v with
  | zero =>
      constructor
      · exact Reachable.start
      · intro h
        cases h with
        | start hi => exact hi
  | succ t ih =>
      constructor
      · intro h
        obtain ⟨u, ⟨hu, hm⟩, he⟩ := h
        exact Reachable.step ((ih u).mp hu) hm he
      · intro h
        cases h with
        | step hr hm he => exact ⟨_, ⟨(ih _).mpr hr, hm⟩, he⟩

/-- Every actual trajectory surviving to this round is captured in this round. -/
def GuaranteesAt {V : Type} (adj : V → V → Prop) (initial : Region V)
    (probes : Nat → Region V) (t : Nat) : Prop :=
  ∀ v, Reachable adj initial probes t v → probes t v

theorem guarantees_iff_belief_covered {V : Type} (adj : V → V → Prop)
    (initial : Region V) (probes : Nat → Region V) (t : Nat) :
    GuaranteesAt adj initial probes t ↔
      ∀ v, possible adj initial probes t v → probes t v := by
  constructor
  · intro h v hv
    exact h v ((possible_iff_reachable adj initial probes t v).mp hv)
  · intro h v hv
    exact h v ((possible_iff_reachable adj initial probes t v).mpr hv)

/-- On graphs without dead ends, capture now is equivalent to an empty next belief.
The hypothesis is essential: an isolated surviving target must not be counted
as captured merely because it has no legal move. -/
theorem guarantees_iff_next_empty {V : Type} (adj : V → V → Prop)
    (initial : Region V) (probes : Nat → Region V)
    (noDeadEnds : ∀ v, ∃ w, adj v w) (t : Nat) :
    GuaranteesAt adj initial probes t ↔
      ∀ v, ¬ possible adj initial probes (t + 1) v := by
  rw [guarantees_iff_belief_covered]
  constructor
  · intro h v hv
    obtain ⟨u, ⟨hu, hm⟩, _⟩ := hv
    exact hm (h u hu)
  · intro h u hu
    apply Classical.byContradiction
    intro hm
    obtain ⟨v, he⟩ := noDeadEnds u
    exact h v ⟨u, ⟨hu, hm⟩, he⟩

theorem possible_mono_initial {V : Type} (adj : V → V → Prop)
    (A B : Region V) (probes : Nat → Region V)
    (hAB : ∀ v, A v → B v) (t : Nat) :
    ∀ v, possible adj A probes t v → possible adj B probes t v := by
  induction t with
  | zero => exact hAB
  | succ t ih =>
      intro v hv
      obtain ⟨u, ⟨hu, hm⟩, he⟩ := hv
      exact ⟨u, ⟨ih u hu, hm⟩, he⟩

theorem possible_union {V : Type} (adj : V → V → Prop)
    (A B : Region V) (probes : Nat → Region V) (t : Nat) (v : V) :
    possible adj (fun u => A u ∨ B u) probes t v ↔
      possible adj A probes t v ∨ possible adj B probes t v := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
      constructor
      · intro h
        obtain ⟨u, ⟨hu, hm⟩, he⟩ := h
        rcases (ih u).mp hu with hA | hB
        · exact Or.inl ⟨u, ⟨hA, hm⟩, he⟩
        · exact Or.inr ⟨u, ⟨hB, hm⟩, he⟩
      · intro h
        rcases h with hA | hB
        · obtain ⟨u, ⟨hu, hm⟩, he⟩ := hA
          exact ⟨u, ⟨(ih u).mpr (Or.inl hu), hm⟩, he⟩
        · obtain ⟨u, ⟨hu, hm⟩, he⟩ := hB
          exact ⟨u, ⟨(ih u).mpr (Or.inr hu), hm⟩, he⟩

theorem possible_mono_probes {V : Type} (adj : V → V → Prop)
    (initial : Region V) (small large : Nat → Region V)
    (hprobe : ∀ t v, small t v → large t v) (t : Nat) :
    ∀ v, possible adj initial large t v → possible adj initial small t v := by
  induction t with
  | zero => exact fun _ h => h
  | succ t ih =>
      intro v hv
      obtain ⟨u, ⟨hu, hm⟩, he⟩ := hv
      exact ⟨u, ⟨ih u hu, fun hs => hm (hprobe t u hs)⟩, he⟩

end Princess

#print axioms Princess.possible_iff_reachable
#print axioms Princess.guarantees_iff_belief_covered
#print axioms Princess.guarantees_iff_next_empty
#print axioms Princess.possible_mono_initial
#print axioms Princess.possible_union
#print axioms Princess.possible_mono_probes
