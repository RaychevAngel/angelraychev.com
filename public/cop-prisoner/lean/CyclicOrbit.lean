import CyclicArithmetic
import FiniteHall

/-! Coprime cyclic steps visit every residue, with a strictly bounded index. -/
namespace Delivery.CyclicOrbit
open CyclicArithmetic

theorem mul_mod_injective {n h : Nat} (coprime : Nat.Coprime n h)
    (x y : Fin n) (same : (h*x.val)%n=(h*y.val)%n) : x=y := by
  have xy : n ∣ x.val-y.val := by
    apply coprime.dvd_of_dvd_mul_left
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq same)
  have yx : n ∣ y.val-x.val := by
    apply coprime.dvd_of_dvd_mul_left
    rw [Nat.mul_sub_left_distrib]
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq same.symm)
  have smallxy : x.val-y.val<n := by have := x.isLt; omega
  have smallyx : y.val-x.val<n := by have := y.isLt; omega
  have zero1 := Nat.mod_eq_zero_of_dvd xy
  have zero2 := Nat.mod_eq_zero_of_dvd yx
  rw [Nat.mod_eq_of_lt smallxy] at zero1
  rw [Nat.mod_eq_of_lt smallyx] at zero2
  apply Fin.ext
  omega

theorem shift_orbit {n h : Nat} (coprime : Nat.Coprime n h)
    (start target : Fin n) : ∃ i : Fin n, shift start (h*i.val) = target := by
  apply FiniteHall.injective_surjective (fun i : Fin n => shift start (h*i.val)) _ target
  intro x y same
  exact mul_mod_injective coprime x y ((shift_eq_iff start _ _).mp same)

#print axioms mul_mod_injective
#print axioms shift_orbit

theorem retreat_orbit {n h : Nat} (coprime : Nat.Coprime n h) (small : h ≤ n)
    (start target : Fin n) : ∃ i : Fin n, shift start (i.val*(n-h)) = target := by
  have backward : Nat.Coprime n (n-h) := by
    change Nat.gcd n (n-h) = 1
    rw [Nat.gcd_self_sub_right small]
    exact coprime
  obtain ⟨i,found⟩ := shift_orbit backward start target
  exact ⟨i,by simpa only [Nat.mul_comm] using found⟩

#print axioms retreat_orbit
end Delivery.CyclicOrbit
