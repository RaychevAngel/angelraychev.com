import DenseCounting

/-! A single semantic envelope lemma for explicit constructions.
The messenger uses only base arrows; the pursuer is allowed every envelope
arrow. The construction and its witnesses must be supplied, not assumed to
exist by this module. Direct pairs need no intermediate witness. -/
namespace Delivery.RobustTwoMove
universe u
variable {V : Type u}

def Subgraph (B E : Graph V) : Prop := ∀ x y, B x y → E x y

def Witnesses (B E : Graph V) : Prop :=
  ∀ s t c, s ≠ t → c ≠ s → ¬ B s t →
    ∃ z, B s z ∧ B z t ∧ z ≠ c ∧ ¬ E c z

/-- Arbitrary intermediate graphs retain two-move delivery. -/
theorem envelope_universal {B E G : Graph V}
    (lower : Subgraph B G) (upper : Subgraph G E)
    (witnesses : Witnesses B E) (s t : V) : Universal G t 2 s := by
  intro c initial
  by_cases same : s = t
  · subst s
    exact Winning.delivered
  · by_cases direct : B s t
    · exact Winning.finish (Ne.symm initial) (Or.inr (lower s t direct))
    · obtain ⟨z, first, last, different, absent⟩ :=
        witnesses s t c same initial direct
      apply DenseCounting.safe_intermediate_winning (Ne.symm initial)
        (lower s z first) (lower z t last)
      intro reachable
      cases reachable with
      | inl equality => exact different equality.symm
      | inr edge => exact absent (upper c z edge)

theorem envelope_actual_delivery [DecidableEq V] {B E G : Graph V}
    (lower : Subgraph B G) (upper : Subgraph G E)
    (witnesses : Witnesses B E) {s t c : V} (initial : c ≠ s)
    (cop : PursuerPolicy V) (legal : LegalPursuer G cop)
    (history : History V) : play G t cop 2 history s c = .delivered := by
  exact winning_play_delivers
    (envelope_universal lower upper witnesses s t c initial) cop legal history

#print axioms envelope_universal
#print axioms envelope_actual_delivery
end Delivery.RobustTwoMove
