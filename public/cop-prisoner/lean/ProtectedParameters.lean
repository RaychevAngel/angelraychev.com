import ProtectedConstruction

/-! Arithmetic parameter closure for the protected circle at every n≥25.
The proof follows the manuscript's elementary odd-part cases. -/
namespace Delivery.ProtectedParameters
open FiniteGame Extremal

private theorem odd_decomposition (x : Nat) (positive : 0<x) :
    ∃ e d, d%2=1 ∧ x=2^e*d := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    by_cases odd : x%2=1
    · exact ⟨0,x,odd,by simp⟩
    · have small : x/2<x := by omega
      obtain ⟨e,d,hd,eq⟩ := ih (x/2) small (by omega)
      refine ⟨e+1,d,hd,?_⟩
      have twice : x=2*(x/2) := by omega
      rw [twice,eq,Nat.pow_succ]
      simp only [Nat.mul_comm,Nat.mul_left_comm]

private theorem pow_seven (e : Nat) : 2^e%7=1 ∨ 2^e%7=2 ∨ 2^e%7=4 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [Nat.pow_succ,Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> decide

private theorem pow_three (e : Nat) : 2^e%3=if e%2=0 then 1 else 2 := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [Nat.pow_succ,Nat.mul_mod,ih]
    by_cases even : e%2=0
    · rw [if_pos even,if_neg (by omega)]
    · rw [if_neg even,if_pos (by omega)]

private theorem pow_eleven (e : Nat) (even : e%2=0) :
    2^e%11=1 ∨ 2^e%11=3 ∨ 2^e%11=4 ∨ 2^e%11=5 ∨ 2^e%11=9 := by
  have powers (j : Nat) : 4^j%11=1 ∨ 4^j%11=3 ∨ 4^j%11=4 ∨ 4^j%11=5 ∨ 4^j%11=9 := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [Nat.pow_succ,Nat.mul_mod]
      rcases ih with h | h | h | h | h <;> rw [h] <;> decide
  have eq : e=2*(e/2) := by omega
  rw [eq,Nat.pow_mul]
  exact powers (e/2)

private theorem gcd_small {h c : Nat} (small : c=3 ∨ c=7 ∨ c=11) (nonzero : h%c≠0) :
    Nat.gcd c h=1 := by
  rcases small with rfl | rfl | rfl
  · rw [Nat.gcd_rec]
    have kernel : ∀ r : Fin 3, r.val≠0→Nat.gcd r.val 3=1 := by decide +kernel
    exact kernel ⟨h%3,Nat.mod_lt _ (by decide)⟩ nonzero
  · rw [Nat.gcd_rec]
    have kernel : ∀ r : Fin 7, r.val≠0→Nat.gcd r.val 7=1 := by decide +kernel
    exact kernel ⟨h%7,Nat.mod_lt _ (by decide)⟩ nonzero
  · rw [Nat.gcd_rec]
    have kernel : ∀ r : Fin 11, r.val≠0→Nat.gcd r.val 11=1 := by decide +kernel
    exact kernel ⟨h%11,Nat.mod_lt _ (by decide)⟩ nonzero

private theorem half_parameter {n c : Nat} (large : 25≤n) (one : n%4=1)
    (csmall : c=3 ∨ c=7 ∨ c=11) (notDiv : n%c≠0) :
    7≤(n-c)/2 ∧ ((n-c)/2)%2=1 ∧ 2*((n-c)/2)<n ∧ Nat.Coprime n ((n-c)/2) := by
  have cr : c%4=3 ∧ c≤11 := by rcases csmall with rfl | rfl | rfl <;> decide
  have order : n=2*((n-c)/2)+c := by omega
  refine ⟨by omega,by omega,by omega,?_⟩
  change Nat.gcd n ((n-c)/2)=1
  apply Eq.trans (congrArg (fun x => Nat.gcd x ((n-c)/2)) order)
  rw [Nat.gcd_mul_right_add_left]
  apply gcd_small csmall
  intro bad
  have zero : n%c=0 := by
    rw [order,Nat.add_mod,Nat.mul_mod,bad]
    simp
  exact notDiv zero

/-- The arithmetic existence statement uses only explicit formulas and
halving n−1 to its odd part, never a graph or game search. -/
theorem exists_parameter {n : Nat} (large : 25≤n) :
    ∃ h, 7≤h ∧ h%2=1 ∧ 2*h<n ∧ Nat.Coprime n h := by
  by_cases zero : n%4=0
  · let h := n/2-1
    have odd : h%2=1 := by dsimp [h]; omega
    refine ⟨h,by dsimp [h]; omega,odd,by dsimp [h]; omega,?_⟩
    have order : n=2*h+2 := by dsimp [h]; omega
    change Nat.gcd n h=1
    rw [order,Nat.gcd_mul_right_add_left,Nat.gcd_rec,odd]
    rfl
  by_cases two : n%4=2
  · let h := n/2-2
    have odd : h%2=1 := by dsimp [h]; omega
    refine ⟨h,by dsimp [h]; omega,odd,by dsimp [h]; omega,?_⟩
    have order : n=2*h+4 := by dsimp [h]; omega
    change Nat.gcd n h=1
    rw [order,Nat.gcd_mul_right_add_left,Nat.gcd_rec]
    have cases : h%4=1 ∨ h%4=3 := by omega
    rcases cases with eq | eq <;> rw [eq] <;> rfl
  by_cases three : n%4=3
  · let h := (n-1)/2
    refine ⟨h,by dsimp [h]; omega,by dsimp [h]; omega,by dsimp [h]; omega,?_⟩
    have order : n=2*h+1 := by dsimp [h]; omega
    change Nat.gcd n h=1
    rw [order,Nat.gcd_mul_right_add_left]
    exact Nat.gcd_one_left h
  have one : n%4=1 := by omega
  obtain ⟨e,d,odd,decomposition⟩ := odd_decomposition (n-1) (by omega)
  have order : n=2^e*d+1 := by omega
  have four : 4≤2^e := by
    have even : (2^e*d)%4=0 := by omega
    have pos : 0<2^e := Nat.two_pow_pos e
    by_cases e0 : e=0
    · subst e
      simp only [Nat.pow_zero,Nat.one_mul] at even
      omega
    have ege : 1≤e := by omega
    by_cases e1 : e=1
    · subst e
      simp only [Nat.pow_one] at even
      omega
    have ege2 : 2≤e := by omega
    exact Nat.pow_le_pow_right (by decide : 0<2) ege2
  by_cases big : 7≤d
  · refine ⟨d,big,odd,?_,?_⟩
    · have bound := Nat.mul_le_mul_right d four
      omega
    · change Nat.gcd n d=1
      rw [order,Nat.gcd_mul_right_add_left]
      exact Nat.gcd_one_left d
  by_cases threeN : n%3≠0
  · exact ⟨(n-3)/2,half_parameter large one (Or.inl rfl) threeN⟩
  have divisible3 : n%3=0 := by omega
  have cases : d=1 ∨ d=3 ∨ d=5 := by omega
  rcases cases with rfl | rfl | rfl
  · have nonseven : n%7≠0 := by
      have powers := pow_seven e
      rw [order,Nat.mul_one,Nat.add_mod]
      omega
    exact ⟨(n-7)/2,half_parameter large one (Or.inr (Or.inl rfl)) nonseven⟩
  · have impossible : n%3=1 := by rw [order,Nat.add_mod,Nat.mul_mod]; simp
    omega
  · have even : e%2=0 := by
      have powers := pow_three e
      rw [order,Nat.add_mod,Nat.mul_mod,powers] at divisible3
      split at divisible3 <;> omega
    have noneleven : n%11≠0 := by
      have powers := pow_eleven e even
      rw [order,Nat.add_mod,Nat.mul_mod]
      omega
    exact ⟨(n-11)/2,half_parameter large one (Or.inr (Or.inr rfl)) noneleven⟩

/-- Arithmetic-only parameter selection in increasing order. The loop checks
integers and gcds; its success is proved above for every n≥25. -/
def parameter (n : Nat) : Nat :=
  ((List.range n).find? fun h => decide (7≤h ∧ h%2=1 ∧ 2*h<n ∧ Nat.Coprime n h)).getD 0

theorem parameter_valid {n : Nat} (large : 25≤n) :
    7≤parameter n ∧ (parameter n)%2=1 ∧ 2*(parameter n)<n ∧ Nat.Coprime n (parameter n) := by
  obtain ⟨h,hh,odd,room,coprime⟩ := exists_parameter large
  unfold parameter
  cases eq : (List.range n).find? (fun h => decide (7≤h ∧ h%2=1 ∧ 2*h<n ∧ Nat.Coprime n h)) with
  | none =>
    have impossible := List.find?_eq_none.mp eq h (List.mem_range.mpr (by omega))
    exact False.elim (impossible (by simp only [decide_eq_true_eq]; exact ⟨hh,odd,room,coprime⟩))
  | some p =>
    have good := List.find?_some eq
    simpa only [decide_eq_true_eq,Option.getD_some] using good

/-- The full protected-circle interval at every order at least twenty-five. -/
theorem maximum {n m : Nat} (large : 25≤n) (low : 3*n≤m)
    (high : m≤n*((n+6)/7-1)) : IsMaximum n m (n*(n-1)-m) := by
  let h := parameter n
  obtain ⟨hh,odd,room,coprime⟩ := parameter_valid large
  change 7≤h at hh
  change h%2=1 at odd
  change 2*h<n at room
  change Nat.Coprime n h at coprime
  have shape : h=2*((h-1)/2)+1 := by omega
  apply ProtectedConstruction.maximum (a := (h-1)/2) (by omega) (by omega) ?_ low high
  simpa only [← shape] using coprime

#print axioms exists_parameter
#print axioms maximum
end Delivery.ProtectedParameters
