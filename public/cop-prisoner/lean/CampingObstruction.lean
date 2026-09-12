import DeliveryGame

namespace Delivery

universe u
variable {V : Type u}

/-- A pursuer camping at c, whose closed outgoing neighborhood covers every
predecessor of t, prevents all indirect delivery. This proves the obstruction
used to audit the original layered construction. -/
theorem camping_winning_is_direct {E : Graph V} {t r c : V} {k : Nat}
    (win : Winning E t k r c)
    (cover : ∀ z, E z t → Legal E c z) : r = t ∨ E r t := by
  induction win with
  | delivered => exact Or.inl rfl
  | finish _ he => exact he
  | @step k r c z _ he _ safe next ih =>
      have hz := ih c (legal_wait E c) cover
      cases hz with
      | inl hzt => subst z; exact he
      | inr hzt => exact False.elim (safe z (cover z hzt) rfl)

theorem camping_predecessor_obstruction {E : Graph V} {t r c : V} {k : Nat}
    (hrt : r ≠ t) (hindirect : ¬ E r t)
    (cover : ∀ z, E z t → Legal E c z) : ¬ Winning E t k r c := by
  intro win
  exact (camping_winning_is_direct win cover).elim hrt hindirect

theorem undirected_no_indirect_guarantee {E : Graph V}
    (symmetric : ∀ u v, E u v → E v u) {r t : V} {k : Nat}
    (hrt : r ≠ t) (hindirect : ¬ E r t) : ¬ Universal E t k r := by
  intro win
  exact camping_predecessor_obstruction hrt hindirect
    (fun z hz => Or.inr (symmetric z t hz)) (win t (Ne.symm hrt))

theorem single_predecessor_no_indirect_guarantee {E : Graph V}
    {r t p : V} {k : Nat} (hrt : r ≠ t) (hrp : r ≠ p)
    (hindirect : ¬ E r t) (unique : ∀ z, E z t → z = p) :
    ¬ Universal E t k r := by
  intro win
  apply camping_predecessor_obstruction hrt hindirect
      (fun z hz => Or.inl (unique z hz).symm)
  exact win p (Ne.symm hrp)

end Delivery
