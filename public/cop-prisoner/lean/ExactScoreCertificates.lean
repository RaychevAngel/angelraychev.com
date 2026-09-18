import Extremal

/-! Exact mixed scores from finite winning and losing certificates.
The generic interface checks each missing pair in one of two directions;
it does not take its score or its guaranteed-pair predicate as a premise.
Concrete tables below come from an existing four-vertex witness, and their
local game obligations are checked by kernel reduction. -/
namespace Delivery.ExactScoreCertificates
open FiniteGame Extremal

variable {V : Type}

structure Classification (E : Graph V) where
  accepted : V → V → Bool
  winning : ∀ t, WinningRegion E t
  losing : ∀ t, LosingRegion E t
  yes : ∀ s t, s ≠ t → ¬ E s t → accepted s t = true →
    ∀ c, c ≠ s → (winning t).region s c
  no : ∀ s t, s ≠ t → ¬ E s t → accepted s t = false →
    ∃ c, c ≠ s ∧ (losing t).region s c

theorem accepted_iff_guaranteed {E : Graph V} (cert : Classification E)
    {s t : V} (distinct : s ≠ t) (missing : ¬ E s t) :
    cert.accepted s t = true ↔ Guaranteed E s t := by
  constructor
  · intro yes c initial
    exact ⟨_, winningRegion_winning (cert.winning t) s c
      (cert.yes s t distinct missing yes c initial) (Ne.symm initial)⟩
  · intro guaranteed
    by_cases yes : cert.accepted s t = true
    · exact yes
    · have no : cert.accepted s t = false := by
        cases h : cert.accepted s t <;> simp_all
      obtain ⟨c, initial, inside⟩ := cert.no s t distinct missing no
      exact False.elim (losingRegion_not_guaranteed (cert.losing t) inside initial guaranteed)

theorem indirect_iff_accepted {E : Graph V} (cert : Classification E) (s t : V) :
    Indirect E s t ↔ s ≠ t ∧ ¬ E s t ∧ cert.accepted s t = true := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, (accepted_iff_guaranteed cert h.1 h.2.1).mpr h.2.2⟩
  · intro h
    exact ⟨h.1, h.2.1, (accepted_iff_guaranteed cert h.1 h.2.1).mp h.2.2⟩

/-- Exact score from an executable count of the accepted missing pairs. -/
theorem exact_score {n : Nat} {E : Graph (Fin n)} [DecidableRel E]
    (cert : Classification E) : score E =
      ((allPairs n).filter fun p =>
        decide (p.1 ≠ p.2 ∧ ¬ E p.1 p.2 ∧ cert.accepted p.1 p.2 = true)).length := by
  classical
  unfold score
  apply congrArg (fun p => ((allPairs n).filter p).length)
  funext p
  exact decide_eq_decide.mpr (indirect_iff_accepted cert p.1 p.2)

/-- A checked exact witness and a separately proved unrestricted upper bound
establish the extremal cell. Completeness of any upper search is not assumed. -/
theorem maximum_from_classification {n m value : Nat} {E : Graph (Fin n)}
    [DecidableRel E] (cert : Classification E) (loopless : Loopless E)
    (arcs : arcCount E = m)
    (count : ((allPairs n).filter fun p =>
      decide (p.1 ≠ p.2 ∧ ¬ E p.1 p.2 ∧ cert.accepted p.1 p.2 = true)).length = value)
    (upper : ∀ F : Graph (Fin n), Loopless F → arcCount F = m → score F ≤ value) :
    IsMaximum n m value :=
  ⟨upper, E, loopless, arcs, (exact_score cert).trans count⟩

-- BEGIN LITERAL FOUR-VERTEX CERTIFICATE
namespace FourVertex
/-- Literal six-arrow witness at budget six in solver-enumeration-n4.json.
The source catalogue's claimed maximum is not used as an assumption. -/
def edge (s t : Fin 4) : Prop :=
  (s.val = 0 ∧ t.val = 3) ∨
  (s.val = 1 ∧ t.val = 2) ∨
  (s.val = 1 ∧ t.val = 3) ∨
  (s.val = 2 ∧ t.val = 0) ∨
  (s.val = 2 ∧ t.val = 1) ∨
  (s.val = 3 ∧ t.val = 0)
instance (s t : Fin 4) : Decidable (edge s t) := inferInstanceAs (Decidable (_ ∨ _))
instance (s t : Fin 4) : Decidable (Legal edge s t) :=
  inferInstanceAs (Decidable (s = t ∨ edge s t))

def signedRank (t r c : Fin 4) : Int :=
  match t.val, r.val, c.val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 3
  | 0, 1, 1 => -1
  | 0, 1, 2 => 3
  | 0, 1, 3 => 3
  | 0, 2, 0 => 1
  | 0, 2, 1 => 1
  | 0, 2, 2 => -1
  | 0, 2, 3 => 1
  | 0, 3, 0 => 1
  | 0, 3, 1 => 1
  | 0, 3, 2 => 1
  | 0, 3, 3 => -1
  | 1, 0, 0 => -1
  | 1, 0, 1 => -1
  | 1, 0, 2 => -1
  | 1, 0, 3 => -1
  | 1, 1, 0 => 0
  | 1, 1, 1 => 0
  | 1, 1, 2 => 0
  | 1, 1, 3 => 0
  | 1, 2, 0 => 1
  | 1, 2, 1 => 1
  | 1, 2, 2 => -1
  | 1, 2, 3 => 1
  | 1, 3, 0 => -1
  | 1, 3, 1 => -1
  | 1, 3, 2 => -1
  | 1, 3, 3 => -1
  | 2, 0, 0 => -1
  | 2, 0, 1 => -1
  | 2, 0, 2 => -1
  | 2, 0, 3 => -1
  | 2, 1, 0 => 1
  | 2, 1, 1 => -1
  | 2, 1, 2 => 1
  | 2, 1, 3 => 1
  | 2, 2, 0 => 0
  | 2, 2, 1 => 0
  | 2, 2, 2 => 0
  | 2, 2, 3 => 0
  | 2, 3, 0 => -1
  | 2, 3, 1 => -1
  | 2, 3, 2 => -1
  | 2, 3, 3 => -1
  | 3, 0, 0 => -1
  | 3, 0, 1 => 1
  | 3, 0, 2 => 1
  | 3, 0, 3 => 1
  | 3, 1, 0 => 1
  | 3, 1, 1 => -1
  | 3, 1, 2 => 1
  | 3, 1, 3 => 1
  | 3, 2, 0 => 3
  | 3, 2, 1 => 3
  | 3, 2, 2 => -1
  | 3, 2, 3 => 3
  | 3, 3, 0 => 0
  | 3, 3, 1 => 0
  | 3, 3, 2 => 0
  | 3, 3, 3 => 0
  | _, _, _ => 0

def moveIndex (t r c : Fin 4) : Nat :=
  match t.val, r.val, c.val with
  | 0, 0, 0 => 0
  | 0, 0, 1 => 0
  | 0, 0, 2 => 0
  | 0, 0, 3 => 0
  | 0, 1, 0 => 2
  | 0, 1, 1 => 1
  | 0, 1, 2 => 3
  | 0, 1, 3 => 2
  | 0, 2, 0 => 0
  | 0, 2, 1 => 0
  | 0, 2, 2 => 2
  | 0, 2, 3 => 0
  | 0, 3, 0 => 0
  | 0, 3, 1 => 0
  | 0, 3, 2 => 0
  | 0, 3, 3 => 3
  | 1, 0, 0 => 0
  | 1, 0, 1 => 0
  | 1, 0, 2 => 0
  | 1, 0, 3 => 0
  | 1, 1, 0 => 1
  | 1, 1, 1 => 1
  | 1, 1, 2 => 1
  | 1, 1, 3 => 1
  | 1, 2, 0 => 1
  | 1, 2, 1 => 1
  | 1, 2, 2 => 2
  | 1, 2, 3 => 1
  | 1, 3, 0 => 3
  | 1, 3, 1 => 3
  | 1, 3, 2 => 3
  | 1, 3, 3 => 3
  | 2, 0, 0 => 0
  | 2, 0, 1 => 0
  | 2, 0, 2 => 0
  | 2, 0, 3 => 0
  | 2, 1, 0 => 2
  | 2, 1, 1 => 1
  | 2, 1, 2 => 2
  | 2, 1, 3 => 2
  | 2, 2, 0 => 2
  | 2, 2, 1 => 2
  | 2, 2, 2 => 2
  | 2, 2, 3 => 2
  | 2, 3, 0 => 3
  | 2, 3, 1 => 3
  | 2, 3, 2 => 3
  | 2, 3, 3 => 3
  | 3, 0, 0 => 0
  | 3, 0, 1 => 3
  | 3, 0, 2 => 3
  | 3, 0, 3 => 3
  | 3, 1, 0 => 3
  | 3, 1, 1 => 1
  | 3, 1, 2 => 3
  | 3, 1, 3 => 3
  | 3, 2, 0 => 1
  | 3, 2, 1 => 0
  | 3, 2, 2 => 2
  | 3, 2, 3 => 1
  | 3, 3, 0 => 3
  | 3, 3, 1 => 3
  | 3, 3, 2 => 3
  | 3, 3, 3 => 3
  | _, _, _ => 0

def winRegion (t r c : Fin 4) : Prop := 0 ≤ signedRank t r c
def loseRegion (t r c : Fin 4) : Prop := signedRank t r c < 0
def rank (t r c : Fin 4) : Nat := (signedRank t r c).toNat
def move (t r c : Fin 4) : Fin 4 :=
  ⟨moveIndex t r c % 4, Nat.mod_lt _ (by decide)⟩
instance (t r c : Fin 4) : Decidable (winRegion t r c) :=
  inferInstanceAs (Decidable (0 ≤ _))
instance (t r c : Fin 4) : Decidable (loseRegion t r c) :=
  inferInstanceAs (Decidable (_ < 0))

theorem winning_valid : ∀ t r c : Fin 4, winRegion t r c → r ≠ t → r ≠ c →
    Legal edge r (move t r c) ∧ (move t r c = t ∨
      (move t r c ≠ c ∧ ∀ c', Legal edge c c' →
        move t r c ≠ c' ∧ winRegion t (move t r c) c' ∧
        rank t (move t r c) c' < rank t r c)) := by
  decide +kernel

theorem losing_nonterminal : ∀ t r c : Fin 4, loseRegion t r c → r ≠ t := by
  decide +kernel

theorem losing_closed : ∀ t r c : Fin 4, loseRegion t r c → r ≠ c →
    ∀ z, Legal edge r z → z ≠ t ∧
      (z = c ∨ ∃ c', Legal edge c c' ∧ (z = c' ∨ loseRegion t z c')) := by
  decide +kernel

def winning (t : Fin 4) : WinningRegion edge t where
  region := winRegion t
  rank := rank t
  move := move t
  valid := winning_valid t

def losing (t : Fin 4) : LosingRegion edge t where
  region := loseRegion t
  nonterminal := losing_nonterminal t
  closed := losing_closed t

def accepted (s t : Fin 4) : Bool :=
  (s.val == 1 && t.val == 0) || (s.val == 2 && t.val == 3)

theorem accepted_starts : ∀ s t : Fin 4, s ≠ t → ¬ edge s t →
    accepted s t = true → ∀ c, c ≠ s → winRegion t s c := by
  decide +kernel

theorem rejected_start : ∀ s t : Fin 4, s ≠ t → ¬ edge s t →
    accepted s t = false → ∃ c, c ≠ s ∧ loseRegion t s c := by
  decide +kernel

def classification : Classification edge where
  accepted := accepted
  winning := winning
  losing := losing
  yes := accepted_starts
  no := rejected_start

theorem score_two : score edge = 2 := by
  rw [exact_score classification]
  decide +kernel

theorem loopless : Loopless edge := by
  unfold Loopless
  decide +kernel

theorem arcs_six : arcCount edge = 6 := by
  rw [arcCount_eq]
  decide +kernel

theorem missing_six : missingCount edge = 6 := by
  rw [missingCount_eq]
  decide +kernel

/-- This is a mixed classification: (1,0) is guaranteed, while (0,1)
is a missing pair with a checked losing initial cop position. -/
theorem mixed_outcomes : Guaranteed edge 1 0 ∧ ¬ Guaranteed edge 0 1 := by
  constructor
  · exact (accepted_iff_guaranteed classification (by decide) (by decide)).mp (by decide)
  · intro h
    have yes := (accepted_iff_guaranteed classification (by decide : (0 : Fin 4) ≠ 1)
      (by decide : ¬ edge 0 1)).mpr h
    contradiction

end FourVertex
#print axioms exact_score
#print axioms maximum_from_classification
#print axioms FourVertex.winning_valid
#print axioms FourVertex.losing_closed
#print axioms FourVertex.score_two
#print axioms FourVertex.mixed_outcomes
end Delivery.ExactScoreCertificates
