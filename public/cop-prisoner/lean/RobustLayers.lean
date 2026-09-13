import SafeBranching
import RobustTwoMove

/-! Safe ranks and routing layers for arbitrary base/envelope graphs.
The concrete circle arithmetic and hub code conditions are supplied premises,
not asserted by this file. The conclusion is actual alternating delivery. -/
namespace Delivery.RobustLayers
universe u
variable {V : Type u}

/-- Every nonterminal source either reaches the recipient directly or has,
against every cop location, a safe base move to a strictly lower source rank. -/
def SourceRanks (B E : Graph V) (t : V) (rank : V → Nat) : Prop :=
  ∀ s, s ≠ t →
    (B s t ∧ 1 ≤ rank s) ∨
    (∀ c, c ≠ s → ∃ z, B s z ∧ ¬ Legal E c z ∧ rank z < rank s)

theorem ranked_envelope_universal {B E G : Graph V} {t : V} {rank : V → Nat}
    (lower : RobustTwoMove.Subgraph B G) (upper : RobustTwoMove.Subgraph G E)
    (ranks : SourceRanks B E t rank) (s : V) : Universal G t (rank s) s := by
  have step : ∀ k, ∀ x, rank x = k → Universal G t k x := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro x hx
      by_cases terminal : x = t
      · subst x
        exact universal_target G t k
      · rcases ranks x terminal with direct | branch
        · exact universal_mono (universal_direct (lower x t direct.1)) (by omega)
        · intro c hc
          obtain ⟨z, move, safe, smaller⟩ := branch c hc
          have child := ih (rank z) (by omega) z rfl
          have safeG : ¬ Legal G c z := by
            intro reachable
            apply safe
            cases reachable with
            | inl eq => exact Or.inl eq
            | inr edge => exact Or.inr (upper c z edge)
          exact winning_mono
            (safe_successor (Ne.symm hc) (lower x z move) safeG child) (by omega)
  exact step (rank s) s rfl

theorem ranked_envelope_actual_delivery [DecidableEq V]
    {B E G : Graph V} {t s c : V} {rank : V → Nat}
    (lower : RobustTwoMove.Subgraph B G) (upper : RobustTwoMove.Subgraph G E)
    (ranks : SourceRanks B E t rank) (initial : c ≠ s)
    (cop : PursuerPolicy V) (legal : LegalPursuer G cop) (history : History V) :
    play G t cop (rank s) history s c = .delivered := by
  exact winning_play_delivers
    (ranked_envelope_universal lower upper ranks s c initial) cop legal history

/-- A safe entry into a routing region adds one messenger move, including
the intervening pursuer response and its capture check. -/
theorem safe_routing_layer {B E G : Graph V} {t : V} {region : V → Prop} {k : Nat}
    (lower : RobustTwoMove.Subgraph B G) (upper : RobustTwoMove.Subgraph G E)
    (inside : ∀ z, region z → Universal G t k z)
    (entry : ∀ s, ¬ region s → ∀ c, c ≠ s →
      ∃ z, region z ∧ B s z ∧ ¬ Legal E c z)
    (s : V) : Universal G t (k+1) s := by
  by_cases member : region s
  · exact universal_mono (inside s member) (Nat.le_succ k)
  · intro c hc
    obtain ⟨z, hz, move, safe⟩ := entry s member c hc
    apply safe_successor (Ne.symm hc) (lower s z move) _ (inside z hz)
    intro reachable
    apply safe
    cases reachable with
    | inl eq => exact Or.inl eq
    | inr edge => exact Or.inr (upper c z edge)

#print axioms ranked_envelope_actual_delivery
#print axioms safe_routing_layer
end Delivery.RobustLayers
