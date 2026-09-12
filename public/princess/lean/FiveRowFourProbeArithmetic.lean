import Std

/-! Pure arithmetic for four probes on an even-length five-row board.
Transition is supplied by the ordinary geometric lemmas, not by this file. -/
namespace Princess.FiveRowFourProbeArithmetic

def core (b z : Nat) : Nat :=
  if b ≤ 4 then b else if b = 5 ∧ z = 0 then 6 else
    if b%3 = 0 then 8*(b/3)-8 else
    if b%3 = 1 then 8*(b/3)-(if z = 0 then 5 else 4) else
    8*(b/3)-(if z = 0 then 4 else 1)

def last (h : Nat) : Nat :=
  if h%3 = 0 then 8*(h/3)-12 else
  if h%3 = 1 then 8*(h/3)-9 else 8*(h/3)-5

def initial (h : Nat) : Nat :=
  if h%3 = 0 then 8*(h/3)-10 else
  if h%3 = 1 then 8*(h/3)-8 else 8*(h/3)-4

def value (h b z : Nat) : Nat :=
  if b = h then initial h else if b = h-1 then last h else core b z

def Valid (h b z : Nat) : Prop :=
  b ≤ h ∧ (b = 0 ∨ 2 ≤ b) ∧ z ≤ 1 ∧ (z = 1 → 5 ≤ b ∧ b ≤ h-3)

def Transition (h b z p b' z' : Nat) : Prop :=
  (b ≤ p ∧ b' = 0 ∧ z' = 0) ∨
  (p = 0 ∧ b = h ∧ b' = h ∧ z' = 0) ∨
  (1 ≤ b-p ∧ (b-p = 1 ∨ b-p = h-2 ∨ b-p = h-1) ∧
    z = 0 ∧ b' = b-p+1 ∧ z' = 0) ∨
  (1 ≤ b-p ∧ b-p+2 ≤ h ∧ b' = b-p+2 ∧
    z' = (if 3 ≤ b-p ∧ b-p ≤ h-5 then 1 else 0) ∧
    ¬ (z = 1 ∧ 3 ≤ b-p ∧ b-p ≤ h-5)) ∨
  (1 ≤ b-p ∧ b-p+3 ≤ b' ∧ z' = 0)

set_option maxHeartbeats 12000000 in
theorem potential_step (h b z p b' z' : Nat) (hh : 15 ≤ h)
    (valid : Valid h b z) (next_cap : b' ≤ h) (hp : p ≤ 4)
    (trans : Transition h b z p b' z') :
    value h b z ≤ p + value h b' z' := by
  obtain ⟨bh,bsmall,zsmall,marked⟩ := valid
  have zcases : z = 0 ∨ z = 1 := by omega
  rcases zcases with rfl | rfl
  all_goals
    rcases trans with ⟨hc,hb,hz⟩ | ⟨hc,hb,hnext,hz⟩ |
      ⟨hr,hcase,hmark,hb,hz⟩ | ⟨hr,hcap,hb,hz,hguard⟩ | ⟨hr,hb,hz⟩
  all_goals try (split at hz)
  all_goals subst_vars
  all_goals
    simp only [value,initial,last,core,Nat.reduceEqDiff,if_true,if_false]
    split <;> (try omega) <;> (try split) <;> (try omega) <;> (try split) <;> (try omega) <;> (try split) <;>
      (try omega) <;> (try split) <;> (try omega) <;> (try split) <;> (try omega) <;> (try split) <;>
      (try omega) <;> (try split) <;> (try omega) <;> (try split) <;> (try omega) <;> (try split) <;>
      (try omega) <;> (try split) <;> (try omega) <;> (try split) <;>
      (try omega) <;> (try split) <;> (try omega) <;> (try split) <;>
      (try omega) <;> (try split) <;> (try omega) <;> (try split) <;> (first | omega | simp_all only [and_false])

theorem value_zero (h : Nat) (hh : 15 ≤ h) : value h 0 0 = 0 := by
  simp only [value,core]
  split <;> (try omega) <;> (try split) <;> (try omega) <;> (try split) <;> omega

end Princess.FiveRowFourProbeArithmetic
#print axioms Princess.FiveRowFourProbeArithmetic.potential_step
