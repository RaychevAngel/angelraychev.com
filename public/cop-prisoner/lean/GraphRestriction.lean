import FiniteGame
import Extremal

/-! Winning strategies descend to induced vertex sets when a source or sink
is removed. Waiting is preserved and receipt remains terminal before capture. -/
namespace Delivery.GraphRestriction
open FiniteGame Extremal

variable {V : Type}

def induced (E : Graph V) (P : V → Prop) : Graph {x // P x} :=
  fun s t => E s.val t.val

def ForwardClosed (E : Graph V) (P : V → Prop) : Prop :=
  ∀ x y, P x → E x y → P y

def BackwardClosed (E : Graph V) (P : V → Prop) : Prop :=
  ∀ x y, P y → E x y → P x

theorem legal_iff {E : Graph V} {P : V → Prop} (s t : {x // P x}) :
    Legal (induced E P) s t ↔ Legal E s.val t.val := by
  constructor
  · rintro (same | edge)
    · exact Or.inl (congrArg Subtype.val same)
    · exact Or.inr edge
  · rintro (same | edge)
    · exact Or.inl (Subtype.ext same)
    · exact Or.inr edge

/-- A winning route to a backward-closed target set must already be in it.
The induction follows a stationary legal pursuer reply, so waiting cannot
supply a way out of a deleted sink. -/
theorem winning_source_mem {E : Graph V} {P : V → Prop}
    (closed : BackwardClosed E P) {t r c : V} {k : Nat}
    (win : Winning E t k r c) (target : P t) : P r := by
  induction win with
  | delivered => exact target
  | finish _ move =>
    rcases move with same | edge
    · exact same ▸ target
    · exact closed _ _ target edge
  | @step k r c z _ move _ _ next ih =>
    have hz := ih c (legal_wait E c)
    rcases move with same | edge
    · exact same ▸ hz
    · exact closed _ _ hz edge

/-- The internal restriction argument only needs the first winning move
to remain in the retained set against a stationary retained pursuer. -/
theorem winning_restrict {E : Graph V} {P : V → Prop} {t : V}
    (retain : ∀ r c z k, P r → P c → Legal E r z → Winning E t k z c → P z)
    {r c : V} {k : Nat} (win : Winning E t k r c) :
    ∀ (target : P t) (source : P r) (cop : P c),
      Winning (induced E P) ⟨t,target⟩ k ⟨r,source⟩ ⟨c,cop⟩ := by
  induction win with
  | delivered => intro target source cop; exact Winning.delivered
  | finish distinct move =>
    intro target source cop
    exact Winning.finish (fun same => distinct (congrArg Subtype.val same))
      ((legal_iff _ _).mpr move)
  | @step k r c z distinct move safeNow safeReply next ih =>
    intro target source cop
    have hz : P z := retain r c z k source cop move (next c (legal_wait E c))
    apply Winning.step (z := ⟨z,hz⟩)
      (fun same => distinct (congrArg Subtype.val same)) ((legal_iff _ _).mpr move)
      (fun same => safeNow (congrArg Subtype.val same))
    · intro c' reply same
      exact safeReply c'.val ((legal_iff _ _).mp reply) (congrArg Subtype.val same)
    · intro c' reply
      exact ih c'.val ((legal_iff _ _).mp reply) target hz c'.property

theorem winning_forward {E : Graph V} {P : V → Prop}
    (closed : ForwardClosed E P) {t r c : V} {k : Nat}
    (win : Winning E t k r c) (target : P t) (source : P r) (cop : P c) :
    Winning (induced E P) ⟨t,target⟩ k ⟨r,source⟩ ⟨c,cop⟩ := by
  apply winning_restrict (win := win) _ target source cop
  intro r c z k hr _ move _
  rcases move with same | edge
  · exact same.symm ▸ hr
  · exact closed r z hr edge

theorem winning_backward {E : Graph V} {P : V → Prop}
    (closed : BackwardClosed E P) {t r c : V} {k : Nat}
    (win : Winning E t k r c) (target : P t) (source : P r) (cop : P c) :
    Winning (induced E P) ⟨t,target⟩ k ⟨r,source⟩ ⟨c,cop⟩ := by
  apply winning_restrict (win := win) _ target source cop
  intro r c z k _ _ _ next
  exact winning_source_mem closed next target

theorem guaranteed_forward {E : Graph V} {P : V → Prop}
    (closed : ForwardClosed E P) (s t : {x // P x})
    (guaranteed : Guaranteed E s.val t.val) : Guaranteed (induced E P) s t := by
  intro c initial
  have different : c.val ≠ s.val := fun same => initial (Subtype.ext same)
  obtain ⟨k,win⟩ := guaranteed c.val different
  exact ⟨k,winning_forward closed win t.property s.property c.property⟩

theorem guaranteed_backward {E : Graph V} {P : V → Prop}
    (closed : BackwardClosed E P) (s t : {x // P x})
    (guaranteed : Guaranteed E s.val t.val) : Guaranteed (induced E P) s t := by
  intro c initial
  have different : c.val ≠ s.val := fun same => initial (Subtype.ext same)
  obtain ⟨k,win⟩ := guaranteed c.val different
  exact ⟨k,winning_backward closed win t.property s.property c.property⟩

theorem indirect_forward {E : Graph V} {P : V → Prop}
    (closed : ForwardClosed E P) (s t : {x // P x})
    (pair : Indirect E s.val t.val) : Indirect (induced E P) s t :=
  ⟨fun same => pair.1 (congrArg Subtype.val same),pair.2.1,
    guaranteed_forward closed s t pair.2.2⟩

theorem indirect_backward {E : Graph V} {P : V → Prop}
    (closed : BackwardClosed E P) (s t : {x // P x})
    (pair : Indirect E s.val t.val) : Indirect (induced E P) s t :=
  ⟨fun same => pair.1 (congrArg Subtype.val same),pair.2.1,
    guaranteed_backward closed s t pair.2.2⟩

/-- Deleting an actual source preserves every old-endpoint guarantee. -/
theorem delete_source {E : Graph V} (v : V) (source : ∀ x, ¬ E x v)
    (s t : {x // x ≠ v}) (pair : Indirect E s.val t.val) :
    Indirect (induced E (fun x => x ≠ v)) s t := by
  apply indirect_forward (s := s) (t := t) _ pair
  intro x y _ edge same
  exact source x (same ▸ edge)

/-- Deleting an actual sink preserves every old-endpoint guarantee. -/
theorem delete_sink {E : Graph V} (v : V) (sink : ∀ x, ¬ E v x)
    (s t : {x // x ≠ v}) (pair : Indirect E s.val t.val) :
    Indirect (induced E (fun x => x ≠ v)) s t := by
  apply indirect_backward (s := s) (t := t) _ pair
  intro x y _ edge same
  exact sink y (same ▸ edge)

/-- A route starting in a forward-closed set can only deliver inside it. -/
theorem winning_target_mem {E : Graph V} {P : V → Prop}
    (closed : ForwardClosed E P) {t r c : V} {k : Nat}
    (win : Winning E t k r c) : P r → P t := by
  induction win with
  | delivered => exact id
  | finish _ move =>
    intro source
    rcases move with same | edge
    · exact same.symm ▸ source
    · exact closed _ _ source edge
  | @step k r c z _ move _ _ next ih =>
    intro source
    have hz : P z := by
      rcases move with same | edge
      · exact same.symm ▸ source
      · exact closed _ _ source edge
    exact ih c (legal_wait E c) hz

/-- The deleted source contributes no recipient column. -/
theorem no_indirect_to_source {E : Graph V} (v : V) (source : ∀ x, ¬ E x v)
    (s : V) : ¬ Indirect E s v := by
  intro pair
  obtain ⟨k,win⟩ := pair.2.2 v (Ne.symm pair.1)
  have closed : ForwardClosed E (fun x => x ≠ v) := by
    intro x y _ edge same
    exact source x (same ▸ edge)
  exact winning_target_mem closed win pair.1 rfl

/-- The deleted sink contributes no source row. -/
theorem no_indirect_from_sink {E : Graph V} (v : V) (sink : ∀ x, ¬ E v x)
    (t : V) : ¬ Indirect E v t := by
  intro pair
  obtain ⟨k,win⟩ := pair.2.2 t (Ne.symm pair.1)
  have closed : BackwardClosed E (fun x => x ≠ v) := by
    intro x y _ edge same
    exact sink y (same ▸ edge)
  exact winning_source_mem closed win (Ne.symm pair.1) rfl

#print axioms winning_source_mem
#print axioms winning_restrict
#print axioms delete_source
#print axioms delete_sink
#print axioms no_indirect_to_source
#print axioms no_indirect_from_sink
end Delivery.GraphRestriction
