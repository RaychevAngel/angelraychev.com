import FiniteExclusionConjugacy
import CyclicArithmetic

/-! Rotation normalization for the Hamiltonian first permutation. A minimum
second-factor displacement is moved to vertex zero by a graph isomorphism. -/
namespace Delivery.FiniteExclusion.HamiltonianNormalization
open FiniteGame Extremal CyclicArithmetic

def up (v x : Fin 9) : Fin 9 := shift x v.val
def down (v x : Fin 9) : Fin 9 := ⟨(x.val+9-v.val)%9,by omega⟩

theorem down_up (v x : Fin 9) : down v (up v x)=x := by
  apply Fin.ext
  change (((x.val+v.val)%9)+9-v.val)%9=x.val
  have := x.isLt
  have := v.isLt
  omega

theorem up_down (v x : Fin 9) : up v (down v x)=x := by
  apply Fin.ext
  change (((x.val+9-v.val)%9)+v.val)%9=x.val
  have := x.isLt
  have := v.isLt
  omega

def rotation (a : Assignment 9) (cycle : ∀ x, a x=shift x 1) (v : Fin 9) : Conjugacy a a where
  toFun := down v
  invFun := up v
  left_inv := up_down v
  right_inv := down_up v
  commute := by
    intro x
    rw [cycle,cycle]
    apply Fin.ext
    change (((x.val+1)%9)+9-v.val)%9=(((x.val+9-v.val)%9)+1)%9
    have := x.isLt
    have := v.isLt
    omega

def displacement (b : Assignment 9) (s : Fin 9) : Nat := ((b s).val+9-s.val)%9

theorem shift_displacement (a b : Assignment 9) (cycle : ∀ x, a x=shift x 1)
    (v s : Fin 9) : displacement ((rotation a cycle v).push b) s=displacement b (up v s) := by
  let c:=up v s
  have cs : c.val=(s.val+v.val)%9 := rfl
  have small := (b c).isLt
  have sv := s.isLt
  have vv := v.isLt
  change (((b c).val+9-v.val)%9+9-s.val)%9=((b c).val+9-c.val)%9
  omega

theorem zero_displacement (b : Assignment 9) : displacement b 0=(b 0).val := by
  unfold displacement
  simp only [Fin.val_zero,Nat.sub_zero,Nat.add_mod_right,Nat.mod_eq_of_lt (b 0).isLt]

theorem minimum_on_list {α : Type} (f : α → Nat) (xs : List α) (nonempty : xs≠[]) :
    ∃ x∈xs, ∀ y∈xs, f x≤f y := by
  induction xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs ih =>
    by_cases empty : xs=[]
    · subst xs
      refine ⟨x,by simp,?_⟩
      intro y member
      have same : y=x := List.mem_singleton.mp member
      subst y
      exact Nat.le_refl _
    · obtain ⟨z,member,smallest⟩ := ih empty
      by_cases order : f x≤f z
      · refine ⟨x,by simp,?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with same | tail
        · subst y; exact Nat.le_refl _
        · exact Nat.le_trans order (smallest y tail)
      · refine ⟨z,List.mem_cons_of_mem x member,?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with same | tail
        · subst y; omega
        · exact smallest y tail

theorem normalized_cover (a b : Assignment 9) (cycle : ∀ x, a x=shift x 1)
    (valid : Valid a b) : ∃ b' : Assignment 9, Valid a b' ∧
      (∀ s, (b' 0).val≤displacement b' s) ∧ score (edgeOf a b')=score (edgeOf a b) := by
  obtain ⟨v,_,minimal⟩ := minimum_on_list (displacement b) (List.finRange 9) (by decide)
  let e:=rotation a cycle v
  refine ⟨e.push b,e.valid_push b valid,?_,(e.score_eq b).symm⟩
  intro s
  have upzero : up v 0=v := by
    apply Fin.ext
    change (0+v.val)%9=v.val
    simp [Nat.mod_eq_of_lt v.isLt]
  have atzero := shift_displacement a b cycle v 0
  rw [zero_displacement,upzero] at atzero
  have other := shift_displacement a b cycle v s
  have lower := minimal (up v s) (List.mem_finRange _)
  change ((rotation a cycle v).push b 0).val ≤ displacement ((rotation a cycle v).push b) s
  omega

#print axioms normalized_cover
end Delivery.FiniteExclusion.HamiltonianNormalization
