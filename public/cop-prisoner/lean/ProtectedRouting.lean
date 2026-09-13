import DenseCounting

/-!
The semantic part of protected routing.  All arrows touching the protected
set are fixed; arrows whose two endpoints lie outside it may change freely.
Safe two-arrow witnesses are hypotheses, not an asserted existence theorem.
Probability, exact arc budgets, and the construction of witnesses are not
formalized in this module.
-/
namespace Delivery.ProtectedRouting

universe u
variable {V : Type u}

/-- Agreement includes incoming and outgoing arrows at every protected vertex. -/
def IncidentAgreement (H : V → Prop) (E F : Graph V) : Prop :=
  ∀ x y, H x ∨ H y → (E x y ↔ F x y)

/-- A protected safe intermediary for every distinct source and recipient,
and every legal initial pursuer position.  The pursuer may start at the
recipient.  The intermediary is chosen after that initial position is known. -/
def ProtectedWitnesses (H : V → Prop) (E : Graph V) : Prop :=
  ∀ s t c, s ≠ t → c ≠ s →
    ∃ z, H z ∧ E s z ∧ E z t ∧ z ≠ c ∧ ¬ E c z

/-- One witness remains safe after arbitrary changes wholly outside H.
The inequality excludes pursuer waiting; the absent arrow excludes moving
to the intermediary. -/
theorem protected_witness_winning {H : V → Prop} {E F : Graph V}
    (agreement : IncidentAgreement H E F) {s t c z : V}
    (initial : c ≠ s) (protected_vertex : H z)
    (first : E s z) (last : E z t) (different : z ≠ c)
    (absent : ¬ E c z) : Winning F t 2 s c := by
  have firstF : F s z := (agreement s z (Or.inr protected_vertex)).mp first
  have lastF : F z t := (agreement z t (Or.inl protected_vertex)).mp last
  have unreachable : ¬ Legal F c z := by
    intro reachable
    cases reachable with
    | inl same => exact different same.symm
    | inr edge =>
        exact absent ((agreement c z (Or.inr protected_vertex)).mpr edge)
  exact DenseCounting.safe_intermediate_winning (Ne.symm initial)
    firstF lastF unreachable

/-- Universality survives every modification outside the protected set.
The s=t case is already delivered, consistent with receipt-before-capture. -/
theorem protected_routing_universal {H : V → Prop} {E F : Graph V}
    (agreement : IncidentAgreement H E F)
    (witnesses : ProtectedWitnesses H E) (s t : V) :
    Universal F t 2 s := by
  intro c initial
  by_cases same : s = t
  · subst s
    exact Winning.delivered
  · obtain ⟨z, hz, first, last, different, absent⟩ :=
      witnesses s t c same initial
    exact protected_witness_winning agreement initial hz first last
      different absent

/-- Actual delivery within two messenger moves against every legal
history-dependent pursuer, including pursuers who wait or start at t.
This uses the existing concrete game and its selected messenger strategy. -/
theorem protected_routing_actual_delivery [DecidableEq V]
    {H : V → Prop} {E F : Graph V}
    (agreement : IncidentAgreement H E F)
    (witnesses : ProtectedWitnesses H E) {s t c : V}
    (initial : c ≠ s) (cop : PursuerPolicy V)
    (legal : LegalPursuer F cop) (history : History V) :
    play F t cop 2 history s c = .delivered := by
  exact winning_play_delivers
    (protected_routing_universal agreement witnesses s t c initial)
    cop legal history

#print axioms protected_witness_winning
#print axioms protected_routing_universal
#print axioms protected_routing_actual_delivery

end Delivery.ProtectedRouting
