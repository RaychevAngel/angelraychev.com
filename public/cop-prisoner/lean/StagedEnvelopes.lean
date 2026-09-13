import DeliveryGame
import RobustTwoMove

/-! Position-dependent rank envelopes for successive sparse stages.
The messenger policy may use the current stage B and must tolerate every
pursuer move in the next envelope E. Concrete ranks, adjacency and stage
coverage are supplied premises, not formalized existence assertions here. -/
namespace Delivery.StagedEnvelopes

universe u
variable {V : Type u}

/-- A rank may depend on both positions. Receipt wins before collision. -/
structure RankEnvelope (B E : Graph V) (t : V) where
  rank : V → V → Nat
  move : V → V → V
  valid : ∀ r c, r ≠ t → r ≠ c →
    Legal B r (move r c) ∧ (move r c = t ∨
      (move r c ≠ c ∧ ∀ c', Legal E c c' →
        move r c ≠ c' ∧ rank (move r c) c' < rank r c))

theorem legal_subgraph {B G : Graph V}
    (inclusion : RobustTwoMove.Subgraph B G) {x y : V}
    (legal : Legal B x y) : Legal G x y := by
  cases legal with
  | inl same => exact Or.inl same
  | inr edge => exact Or.inr (inclusion x y edge)

/-- The same policy and two-position ranks certify every intermediate graph. -/
def RankEnvelope.intermediate {B E G : Graph V} {t : V}
    (cert : RankEnvelope B E t)
    (lower : RobustTwoMove.Subgraph B G)
    (upper : RobustTwoMove.Subgraph G E) : RankCertificate G t where
  rank := cert.rank
  move := cert.move
  valid := by
    intro r c notTarget distinct
    obtain ⟨moveLegal, finish | ⟨safeNow, future⟩⟩ :=
      cert.valid r c notTarget distinct
    · exact ⟨legal_subgraph lower moveLegal, Or.inl finish⟩
    · refine ⟨legal_subgraph lower moveLegal, Or.inr ⟨safeNow, ?_⟩⟩
      intro c' reply
      exact future c' (legal_subgraph upper reply)

theorem envelope_winning {B E G : Graph V} {t r c : V}
    (cert : RankEnvelope B E t)
    (lower : RobustTwoMove.Subgraph B G)
    (upper : RobustTwoMove.Subgraph G E) (initial : r ≠ c) :
    Winning G t (cert.rank r c + 1) r c :=
  rankCertificate_winning (cert.intermediate lower upper) r c initial

/-- Every legal history-dependent cop produces actual terminal delivery. -/
theorem envelope_actual_delivery [DecidableEq V] {B E G : Graph V} {t r c : V}
    (cert : RankEnvelope B E t)
    (lower : RobustTwoMove.Subgraph B G)
    (upper : RobustTwoMove.Subgraph G E) (initial : r ≠ c)
    (cop : PursuerPolicy V) (legal : LegalPursuer G cop) (history : History V) :
    play G t cop (cert.rank r c + 1) history r c = .delivered :=
  winning_play_delivers (envelope_winning cert lower upper initial) cop legal history

#print axioms envelope_winning
#print axioms envelope_actual_delivery
end Delivery.StagedEnvelopes
