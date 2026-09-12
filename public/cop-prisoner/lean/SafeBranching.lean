import DeliveryGame

namespace Delivery

universe u
variable {V : Type u}

/-- Distinct closed outgoing neighborhoods have at most one common vertex. -/
def ClosedOverlapAtMostOne (E : Graph V) : Prop :=
  ∀ r c, r ≠ c → ∀ x y,
    Legal E r x → Legal E c x → Legal E r y → Legal E c y → x = y

theorem universal_mono {E : Graph V} {t r : V} {k l : Nat}
    (h : Universal E t k r) (hle : k ≤ l) : Universal E t l r :=
  fun c hc => winning_mono (h c hc) hle

theorem universal_target (E : Graph V) (t : V) (k : Nat) :
    Universal E t k t := fun _ _ => Winning.delivered

theorem universal_direct {E : Graph V} {r t : V} (edge : E r t) :
    Universal E t 1 r := fun c hc => direct_delivery (Ne.symm hc) edge

/-- One demonstrably safe move into a universally winning source can be
concatenated, with the intervening pursuer turn and its capture check included. -/
theorem safe_successor {E : Graph V} {t r c z : V} {k : Nat}
    (hrc : r ≠ c) (edge : E r z) (safe : ¬ Legal E c z)
    (child : Universal E t k z) : Winning E t (k+1) r c := by
  have hzc : z ≠ c := by
    intro hz
    subst z
    exact safe (legal_wait E c)
  have hnext : ∀ c', Legal E c c' → z ≠ c' := by
    intro c' hc' hz
    subst c'
    exact safe hc'
  exact Winning.step hrc (Or.inr edge) hzc hnext
    (fun c' hc' => child c' (Ne.symm (hnext c' hc')))

/-- The bootstrap rule behind the circulant construction. It is a theorem
about actual alternating pursuit, not a numerical proxy for that game. -/
theorem safe_branching {E : Graph V} {t r x y : V} {k : Nat}
    (overlap : ClosedOverlapAtMostOne E) (hx : E r x) (hy : E r y)
    (distinct : x ≠ y) (winx : Universal E t k x) (winy : Universal E t k y) :
    Universal E t (k+1) r := by
  intro c hcr
  have hrc := Ne.symm hcr
  by_cases hcx : Legal E c x
  · have hcy : ¬ Legal E c y := by
      intro hcy
      exact distinct (overlap r c hrc x y (Or.inr hx) hcx (Or.inr hy) hcy)
    exact safe_successor hrc hy hcy winy
  · exact safe_successor hrc hx hcx winx

/-- Finite bootstrap certificates whose only rules are receipt, direct arcs,
and the proved safe-branching rule. No circular or infinitary proof is admitted. -/
inductive Bootstrap (E : Graph V) (t : V) : Nat → V → Prop
  | target : Bootstrap E t 0 t
  | direct {r} : E r t → Bootstrap E t 1 r
  | lift {k r} : Bootstrap E t k r → Bootstrap E t (k+1) r
  | branch {k r x y} : E r x → E r y → x ≠ y →
      Bootstrap E t k x → Bootstrap E t k y → Bootstrap E t (k+1) r

theorem bootstrap_sound {E : Graph V} {t r : V} {k : Nat}
    (overlap : ClosedOverlapAtMostOne E) (cert : Bootstrap E t k r) :
    Universal E t k r := by
  induction cert with
  | target => exact universal_target E t 0
  | direct h => exact universal_direct h
  | lift _ ih => exact universal_mono ih (Nat.le_succ _)
  | branch hx hy hd _ _ ihx ihy => exact safe_branching overlap hx hy hd ihx ihy

/-- End-to-end bootstrap interpretation against arbitrary legal pursuer history.
The collision exception at the target and finite delivery are inherited from
`play`, rather than supplied as assumptions on an abstract game interface. -/
theorem bootstrap_actual_delivery [DecidableEq V] {E : Graph V} {t r c : V}
    {k : Nat} (overlap : ClosedOverlapAtMostOne E) (cert : Bootstrap E t k r)
    (hcr : c ≠ r) (cop : PursuerPolicy V) (legal : LegalPursuer E cop)
    (history : History V) : play E t cop k history r c = .delivered :=
  winning_play_delivers (bootstrap_sound overlap cert c hcr) cop legal history

end Delivery
