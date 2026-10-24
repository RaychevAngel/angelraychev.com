import CircleConstruction

/-! Prescribed arithmetic parameters for every order divisible by four.
The three branches are the manuscript's formulas; gcd and range conditions
are proved symbolically, without a parameter search or graph search. -/
namespace Delivery.CircleParameters
open FiniteGame Extremal

def parameter (n : Nat) : Nat :=
  if n%8=0 then n/2-1
  else if (n/4)%4=1 then n/4+2 else n/4+4

private theorem gcd_two {h : Nat} (odd : h%2=1) : Nat.gcd 2 h=1 := by
  rw [Nat.gcd_rec 2 h,odd]
  rfl

private theorem gcd_eight {h : Nat} (residue : h%4=3) : Nat.gcd 8 h=1 := by
  have cases : h%8=3 ∨ h%8=7 := by omega
  rcases cases with eq | eq <;> rw [Nat.gcd_rec 8 h,eq] <;> decide

private theorem gcd_sixteen {h : Nat} (residue : h%4=3) : Nat.gcd 16 h=1 := by
  have cases : h%16=3 ∨ h%16=7 ∨ h%16=11 ∨ h%16=15 := by omega
  rcases cases with eq | eq | eq | eq <;> rw [Nat.gcd_rec 16 h,eq] <;> decide

theorem valid {n : Nat} (large : 16≤n) (multiple : n%4=0) :
    7≤parameter n ∧ (parameter n)%4=3 ∧ 2*(parameter n)+2≤n ∧
      Nat.Coprime n (parameter n) := by
  unfold parameter
  by_cases eight : n%8=0
  · rw [if_pos eight]
    have hlarge : 7≤n/2-1 := by omega
    have residue : (n/2-1)%4=3 := by omega
    refine ⟨hlarge,residue,by omega,?_⟩
    change Nat.gcd n (n/2-1)=1
    have order : n=2*(n/2-1)+2 := by omega
    apply Eq.trans (congrArg (fun x => Nat.gcd x (n/2-1)) order)
    rw [Nat.gcd_mul_right_add_left]
    exact gcd_two (by omega)
  · rw [if_neg eight]
    by_cases one : (n/4)%4=1
    · rw [if_pos one]
      have residue : (n/4+2)%4=3 := by omega
      refine ⟨by omega,residue,by omega,?_⟩
      change Nat.gcd n (n/4+2)=1
      have order : n=4*(n/4+2)-8 := by omega
      apply Eq.trans (congrArg (fun x => Nat.gcd x (n/4+2)) order)
      rw [Nat.gcd_mul_right_sub_left (by omega : 8≤4*(n/4+2))]
      exact gcd_eight residue
    · rw [if_neg one]
      have three : (n/4)%4=3 := by omega
      have residue : (n/4+4)%4=3 := by omega
      refine ⟨by omega,residue,by omega,?_⟩
      change Nat.gcd n (n/4+4)=1
      have order : n=4*(n/4+4)-16 := by omega
      apply Eq.trans (congrArg (fun x => Nat.gcd x (n/4+4)) order)
      rw [Nat.gcd_mul_right_sub_left (by omega : 16≤4*(n/4+4))]
      exact gcd_sixteen residue

/-- Every divisible-by-four order at least sixteen has an explicit attaining
prefix graph throughout the complete five-offset interval. -/
theorem maximum {n m : Nat} (large : 16≤n) (multiple : n%4=0)
    (low : 5*n≤m) (high : m≤n*(n/2-1)) : IsMaximum n m (n*(n-1)-m) := by
  obtain ⟨hh,residue,room,coprime⟩ := valid large multiple
  exact CircleConstruction.full_maximum hh residue room multiple coprime low high

#print axioms valid
#print axioms maximum
end Delivery.CircleParameters
