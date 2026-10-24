import FiniteGame
import RobustTwoMove

/-! Closed losing regions valid throughout an adjacency envelope. The
messenger is allowed every upper-graph move, while the pursuer uses only
lower-graph moves. This is a sound upper-bound certificate for all completions
of a partial graph; no optimistic search result is assumed. -/
namespace Delivery.RobustLosingRegion
open FiniteGame RobustTwoMove
universe u
variable {V : Type u}

structure Certificate (upper lower : Graph V) (t : V) where
  region : V → V → Prop
  nonterminal : ∀ r c, region r c → r ≠ t
  closed : ∀ r c, region r c → r ≠ c → ∀ z, Legal upper r z →
    z ≠ t ∧ (z = c ∨ ∃ c', Legal lower c c' ∧ (z = c' ∨ region z c'))

def Certificate.toLosingRegion {upper lower E : Graph V} {t : V}
    (cert : Certificate upper lower t)
    (lo : Subgraph lower E) (hi : Subgraph E upper) : LosingRegion E t where
  region := cert.region
  nonterminal := cert.nonterminal
  closed := by
    intro r c inside safe z move
    have lifted : Legal upper r z := move.elim Or.inl (fun h => Or.inr (hi r z h))
    obtain ⟨notTarget,capture | ⟨c',reply,outcome⟩⟩ := cert.closed r c inside safe z lifted
    · exact ⟨notTarget,Or.inl capture⟩
    · exact ⟨notTarget,Or.inr ⟨c',reply.elim Or.inl (fun h => Or.inr (lo c c' h)),outcome⟩⟩

theorem not_guaranteed {upper lower E : Graph V} {s t c : V}
    (cert : Certificate upper lower t) (lo : Subgraph lower E) (hi : Subgraph E upper)
    (inside : cert.region s c) (initial : c ≠ s) : ¬ Guaranteed E s t :=
  losingRegion_not_guaranteed (cert.toLosingRegion lo hi) inside initial

#print axioms Certificate.toLosingRegion
#print axioms not_guaranteed
end Delivery.RobustLosingRegion
