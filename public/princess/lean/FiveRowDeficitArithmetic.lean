import Std

/-! Scalar row-deficit consequences used in the all-budget five-row research.
This does not formalize the geometric interpretation of the five deficits. -/
namespace Princess.FiveRowDeficitArithmetic

def e0 (a b : Nat) := min a b
def e1 (a b c : Nat) := min (min a (b-1)) c
def e2 (b c d : Nat) := min (min b c) d
def e3 (c d e : Nat) := min (min c (d-1)) e
def e4 (d e : Nat) := min d e

def Two (a b c d e : Nat) : Prop :=
  a+b+c+d+e = e0 a b + e1 a b c + e2 b c d + e3 c d e + e4 d e + 2

set_option maxHeartbeats 4000000 in
theorem endpoint (a b c d e : Nat) (two : Two a b c d e)
    (zero : e0 a b = 0 ∨ e4 d e = 0) : a+b+c+d+e ≤ 6 := by
  simp only [Two,e0,e1,e2,e3,e4,Nat.min_def] at *
  split at two <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (simp_all <;> omega)

set_option maxHeartbeats 4000000 in
theorem three_rows (a b c d e : Nat) (two : Two a b c d e)
    (zero : (e0 a b = 0 ∧ e1 a b c = 0 ∧ e2 b c d = 0) ∨
      (e2 b c d = 0 ∧ e3 c d e = 0 ∧ e4 d e = 0)) :
    a+b+c+d+e ≤ 5 := by
  simp only [Two,e0,e1,e2,e3,e4,Nat.min_def] at *
  split at two <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (simp_all <;> omega)

set_option maxHeartbeats 4000000 in
theorem alternating_rows (a b c d e : Nat) (two : Two a b c d e)
    (zero : e0 a b = 0 ∧ e2 b c d = 0 ∧ e4 d e = 0) :
    a+b+c+d+e ≤ 2 := by
  simp only [Two,e0,e1,e2,e3,e4,Nat.min_def] at *
  split at two <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (try split at two) <;>
    (try split at two) <;> (try split at two) <;> (simp_all <;> omega)

end Princess.FiveRowDeficitArithmetic
#print axioms Princess.FiveRowDeficitArithmetic.endpoint
#print axioms Princess.FiveRowDeficitArithmetic.three_rows
#print axioms Princess.FiveRowDeficitArithmetic.alternating_rows
