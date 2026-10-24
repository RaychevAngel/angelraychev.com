import DegreeProfileRelabeling
import IrregularNine14Base
import SparseDeletion

/-! Complete degree-histogram reduction for positive support nine at budget
fourteen. The reduction uses actual graph counts and arbitrary relabelings. -/
namespace Delivery.IrregularNine14Profile
open FiniteGame Extremal DenseCombinatorics ConstructionCounts SparseSupport
open IrregularNine14

theorem sum_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map fun x => f x+g x).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

theorem degree_le_three (d : Fin 9 → Nat) (positive : ∀ x, 1≤d x)
    (total : ((List.finRange 9).map d).sum=14)
    (active : 4≤card (fun x => 2≤d x)) : ∀ x, d x≤3 := by
  classical
  intro x
  let base := fun y => if 2≤d y then 2 else 1
  have bound := sum_mono (List.finRange 9)
    (f:=fun y => base y + if y=x then d x-base x else 0) (g:=d) (by
      intro y
      by_cases same : y=x
      · subst y; dsimp [base]; split <;> simp <;> have := positive x <;> omega
      · simp only [if_neg same,Nat.add_zero]; dsimp [base]; split <;> have := positive y <;> omega)
  rw [sum_add] at bound
  have baseline : ((List.finRange 9).map base).sum=9+card (fun x => 2≤d x) := by
    dsimp [base]
    rw [one_or_two,List.length_finRange]
    rw [card_eq]
  rw [baseline,indicator_sum,SparseDeletion.card_singleton,Nat.mul_one,total] at bound
  have small : base x≤2 := by dsimp [base]; split <;> omega
  omega

theorem degree_three_count (d : Fin 9 → Nat) (positive : ∀ x, 1≤d x)
    (small : ∀ x, d x≤3) (total : ((List.finRange 9).map d).sum=14) :
    card (fun x => 2≤d x)+card (fun x => d x=3)=5 := by
  classical
  have formula (x) : d x=(if 2≤d x then 2 else 1)+(if d x=3 then 1 else 0) := by
    have := positive x; have := small x
    split <;> split <;> omega
  have rewrite : (List.finRange 9).map d=(List.finRange 9).map
      (fun x => (if 2≤d x then 2 else 1)+(if d x=3 then 1 else 0)) :=
    List.map_congr_left (fun x _ => formula x)
  rw [rewrite,sum_add,one_or_two,List.length_finRange,indicator_sum,Nat.one_mul] at total
  rw [←card_eq] at total
  omega

theorem split_three {n : Nat} (P : Fin n → Prop) (d : Fin n → Nat)
    (positive : ∀ x, 1≤d x) (small : ∀ x, d x≤3) :
    card P=card (fun x => P x ∧ d x=1)+card (fun x => P x ∧ d x=2)+
      card (fun x => P x ∧ d x=3) := by
  have first := card_partition P (fun x => d x=1)
  have second := card_partition (fun x => P x ∧ d x≠1) (fun x => d x=2)
  have a : card (fun x => (P x ∧ d x≠1) ∧ d x=2)=card (fun x => P x ∧ d x=2) :=
    card_congr (fun x => by constructor <;> intro h; exact ⟨h.1.1,h.2⟩; exact ⟨⟨h.1,by omega⟩,h.2⟩)
  have b : card (fun x => (P x ∧ d x≠1) ∧ ¬ d x=2)=card (fun x => P x ∧ d x=3) := by
    apply card_congr
    intro x
    have := positive x; have := small x
    constructor
    · rintro ⟨⟨hp,h1⟩,h2⟩; exact ⟨hp,by omega⟩
    · rintro ⟨hp,h3⟩; exact ⟨⟨hp,by omega⟩,by omega⟩
  rw [a,b] at second
  calc
    card P = card (fun x => P x ∧ d x=1)+card (fun x => P x ∧ d x≠1) := first.symm
    _ = card (fun x => P x ∧ d x=1)+(card (fun x => P x ∧ d x=2)+card (fun x => P x ∧ d x=3)) :=
      congrArg (fun z => card (fun x => P x ∧ d x=1)+z) second.symm
    _ = _ := by omega

theorem active_cases (E : Graph (Fin 9)) (loopless : Loopless E)
    (budget : arcCount E=14) (posOut : ∀ x, 1≤outdegree E x)
    (posIn : ∀ x, 1≤indegree E x) (large : 13<score E) :
    (card (ActiveOut E)=4 ∧ card (ActiveIn E)=5 ∧ card (fun x => ActiveOut E x ∧ ActiveIn E x)≤1) ∨
    (card (ActiveOut E)=5 ∧ card (ActiveIn E)=4 ∧ card (fun x => ActiveOut E x ∧ ActiveIn E x)≤1) ∨
    (card (ActiveOut E)=5 ∧ card (ActiveIn E)=5) := by
  have counts := positive_support_counts E posOut posIn
  have rect := eligible_rectangle E loopless
  have qa : card (ActiveOut E)≤5 := by omega
  have qb : card (ActiveIn E)≤5 := by omega
  have qa4 : 4≤card (ActiveOut E) := by
    apply Classical.byContradiction
    intro no
    have cases : card (ActiveOut E)=0 ∨ card (ActiveOut E)=1 ∨ card (ActiveOut E)=2 ∨ card (ActiveOut E)=3 := by omega
    rcases cases with h | h | h | h <;> rw [h] at rect counts <;> omega
  have qb4 : 4≤card (ActiveIn E) := by
    apply Classical.byContradiction
    intro no
    have cases : card (ActiveIn E)=0 ∨ card (ActiveIn E)=1 ∨ card (ActiveIn E)=2 ∨ card (ActiveIn E)=3 := by omega
    rcases cases with h | h | h | h <;> rw [h] at rect counts <;> omega
  have casA : card (ActiveOut E)=4 ∨ card (ActiveOut E)=5 := by omega
  have casB : card (ActiveIn E)=4 ∨ card (ActiveIn E)=5 := by omega
  rcases casA with a | a <;> rcases casB with b | b <;> rw [a,b] at counts rect ⊢ <;> omega

noncomputable def joint (d e : Fin 9 → Nat) (a b : Nat) : Nat :=
  card (fun x => d x=a ∧ e x=b)

def matrix (a b c d e f g h i : Nat) (x y : Fin 3) : Nat :=
  match x.val,y.val with
  | 0,0 => a | 0,1 => b | 0,_ => c
  | 1,0 => d | 1,1 => e | 1,_ => f
  | _,0 => g | _,1 => h | _,_ => i

def profileMatrix (p : Fin 11) : Fin 3 → Fin 3 → Nat :=
  match p.val with
  | 0 => matrix 1 4 0 3 0 0 0 1 0
  | 1 => matrix 1 4 0 2 1 0 1 0 0
  | 2 => matrix 0 5 0 3 0 0 1 0 0
  | 3 => matrix 1 3 0 4 0 1 0 0 0
  | 4 => matrix 4 0 0 0 5 0 0 0 0
  | 5 => matrix 3 1 0 1 4 0 0 0 0
  | 6 => matrix 2 2 0 2 3 0 0 0 0
  | 7 => matrix 1 3 0 3 2 0 0 0 0
  | 8 => matrix 1 2 1 4 1 0 0 0 0
  | 9 => matrix 0 4 0 4 1 0 0 0 0
  | _ => matrix 0 3 1 5 0 0 0 0 0

theorem profile_matrix (p : Fin 11) (a b : Fin 3) :
    joint (D p) (R p) (a.val+1) (b.val+1)=profileMatrix p a b := by
  unfold joint
  rw [card_eq]
  revert p a b
  decide +kernel

theorem profile_bounded (p : Fin 11) (x : Fin 9) :
    1≤D p x ∧ D p x≤3 ∧ 1≤R p x ∧ R p x≤3 := by
  revert p x
  decide +kernel

theorem active_count (d : Fin 9 → Nat) (small : ∀ x, d x≤3) :
    card (fun x => 2≤d x)=card (fun x => d x=2)+card (fun x => d x=3) := by
  have same : card (fun x => 2≤d x)=card (fun x => d x=2 ∨ d x=3) :=
    card_congr (fun x => by have := small x; omega)
  rw [same]
  exact card_disjoint_union (fun _ h2 h3 => by omega)

theorem overlap_count (d e : Fin 9 → Nat) (sd : ∀ x, d x≤3) (se : ∀ x, e x≤3) :
    card (fun x => 2≤d x ∧ 2≤e x)=joint d e 2 2+joint d e 2 3+
      joint d e 3 2+joint d e 3 3 := by
  have same : card (fun x => 2≤d x ∧ 2≤e x)=card (fun x =>
      ((d x=2 ∧ e x=2) ∨ (d x=2 ∧ e x=3)) ∨ ((d x=3 ∧ e x=2) ∨ (d x=3 ∧ e x=3))) :=
    card_congr (fun x => by have := sd x; have := se x; omega)
  rw [same,card_disjoint_union (fun _ ha hb => by rcases ha with ha|ha <;> rcases hb with hb|hb <;> omega),
    card_disjoint_union (fun _ ha hb => by omega),card_disjoint_union (fun _ ha hb => by omega)]
  unfold joint
  omega

set_option maxHeartbeats 800000 in
theorem histogram_cases (d e : Fin 9 → Nat) (pd : ∀ x, 1≤d x) (pe : ∀ x, 1≤e x)
    (sd : ∀ x, d x≤3) (se : ∀ x, e x≤3)
    (td : ((List.finRange 9).map d).sum=14) (te : ((List.finRange 9).map e).sum=14)
    (shapes :
      (card (fun x => 2≤d x)=4 ∧ card (fun x => 2≤e x)=5 ∧ card (fun x => 2≤d x ∧ 2≤e x)≤1) ∨
      (card (fun x => 2≤d x)=5 ∧ card (fun x => 2≤e x)=4 ∧ card (fun x => 2≤d x ∧ 2≤e x)≤1) ∨
      (card (fun x => 2≤d x)=5 ∧ card (fun x => 2≤e x)=5)) :
    ∃ p : Fin 11, ∀ a b : Fin 3, joint d e (a.val+1) (b.val+1)=profileMatrix p a b := by
  have row (a : Nat) : card (fun x => d x=a)=joint d e a 1+joint d e a 2+joint d e a 3 :=
    split_three (fun x => d x=a) e pe se
  have col (b : Nat) : card (fun x => e x=b)=joint d e 1 b+joint d e 2 b+joint d e 3 b := by
    have eq := split_three (fun x => e x=b) d pd sd
    have swap (a) : card (fun x => e x=b ∧ d x=a)=joint d e a b :=
      card_congr (fun _ => and_comm)
    rw [swap,swap,swap] at eq
    exact eq
  have total : card (fun x => d x=1)+card (fun x => d x=2)+card (fun x => d x=3)=9 := by
    have eq := split_three (fun _ => True) d pd sd
    simpa only [card_true,true_and] using eq.symm
  have da := active_count d sd
  have ea := active_count e se
  have dt := degree_three_count d pd sd td
  have et := degree_three_count e pe se te
  have overlap := overlap_count d e sd se
  rw [row 1,row 2,row 3] at total
  rw [row 2,row 3] at da
  rw [col 2,col 3] at ea
  rw [row 3] at dt
  rw [col 3] at et
  rw [overlap] at shapes
  have cases :
    (joint d e 1 1=1 ∧ joint d e 1 2=4 ∧ joint d e 1 3=0 ∧ joint d e 2 1=3 ∧ joint d e 2 2=0 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=1 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=1 ∧ joint d e 1 2=4 ∧ joint d e 1 3=0 ∧ joint d e 2 1=2 ∧ joint d e 2 2=1 ∧ joint d e 2 3=0 ∧ joint d e 3 1=1 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=0 ∧ joint d e 1 2=5 ∧ joint d e 1 3=0 ∧ joint d e 2 1=3 ∧ joint d e 2 2=0 ∧ joint d e 2 3=0 ∧ joint d e 3 1=1 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=1 ∧ joint d e 1 2=3 ∧ joint d e 1 3=0 ∧ joint d e 2 1=4 ∧ joint d e 2 2=0 ∧ joint d e 2 3=1 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=4 ∧ joint d e 1 2=0 ∧ joint d e 1 3=0 ∧ joint d e 2 1=0 ∧ joint d e 2 2=5 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=3 ∧ joint d e 1 2=1 ∧ joint d e 1 3=0 ∧ joint d e 2 1=1 ∧ joint d e 2 2=4 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=2 ∧ joint d e 1 2=2 ∧ joint d e 1 3=0 ∧ joint d e 2 1=2 ∧ joint d e 2 2=3 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=1 ∧ joint d e 1 2=3 ∧ joint d e 1 3=0 ∧ joint d e 2 1=3 ∧ joint d e 2 2=2 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=1 ∧ joint d e 1 2=2 ∧ joint d e 1 3=1 ∧ joint d e 2 1=4 ∧ joint d e 2 2=1 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=0 ∧ joint d e 1 2=4 ∧ joint d e 1 3=0 ∧ joint d e 2 1=4 ∧ joint d e 2 2=1 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) ∨
    (joint d e 1 1=0 ∧ joint d e 1 2=3 ∧ joint d e 1 3=1 ∧ joint d e 2 1=5 ∧ joint d e 2 2=0 ∧ joint d e 2 3=0 ∧ joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0) := by
    rcases shapes with h | h | h
    · have z : joint d e 1 3=0 ∧ joint d e 2 3=0 ∧ joint d e 3 3=0 := by omega
      have cases : (joint d e 2 2=0 ∧ joint d e 3 2=0) ∨
          (joint d e 2 2=0 ∧ joint d e 3 2=1) ∨
          (joint d e 2 2=1 ∧ joint d e 3 2=0) := by omega
      rcases cases with c | c | c
      · apply Or.inr; apply Or.inr; apply Or.inl; omega
      · apply Or.inl; omega
      · apply Or.inr; apply Or.inl; omega
    · have z : joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0 := by omega
      have cases : (joint d e 2 2=0 ∧ joint d e 2 3=0) ∨
          (joint d e 2 2=0 ∧ joint d e 2 3=1) ∨
          (joint d e 2 2=1 ∧ joint d e 2 3=0) := by omega
      rcases cases with c | c | c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega))))))))))
      · apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl; omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))
    · have z : joint d e 3 1=0 ∧ joint d e 3 2=0 ∧ joint d e 3 3=0 ∧
          joint d e 1 3=0 ∧ joint d e 2 3=0 := by omega
      have cases : joint d e 2 2=1 ∨ joint d e 2 2=2 ∨ joint d e 2 2=3 ∨
          joint d e 2 2=4 ∨ joint d e 2 2=5 := by omega
      rcases cases with c | c | c | c | c
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · refine ⟨0,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=1
      omega
    · change joint d e 1 2=4
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=3
      omega
    · change joint d e 2 2=0
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=1
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨1,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=1
      omega
    · change joint d e 1 2=4
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=2
      omega
    · change joint d e 2 2=1
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=1
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨2,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=0
      omega
    · change joint d e 1 2=5
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=3
      omega
    · change joint d e 2 2=0
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=1
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨3,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=1
      omega
    · change joint d e 1 2=3
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=4
      omega
    · change joint d e 2 2=0
      omega
    · change joint d e 2 3=1
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨4,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=4
      omega
    · change joint d e 1 2=0
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=0
      omega
    · change joint d e 2 2=5
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨5,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=3
      omega
    · change joint d e 1 2=1
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=1
      omega
    · change joint d e 2 2=4
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨6,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=2
      omega
    · change joint d e 1 2=2
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=2
      omega
    · change joint d e 2 2=3
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨7,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=1
      omega
    · change joint d e 1 2=3
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=3
      omega
    · change joint d e 2 2=2
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨8,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=1
      omega
    · change joint d e 1 2=2
      omega
    · change joint d e 1 3=1
      omega
    · change joint d e 2 1=4
      omega
    · change joint d e 2 2=1
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨9,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=0
      omega
    · change joint d e 1 2=4
      omega
    · change joint d e 1 3=0
      omega
    · change joint d e 2 1=4
      omega
    · change joint d e 2 2=1
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega
  · refine ⟨10,?_⟩
    intro a b
    have ca : a=0 ∨ a=1 ∨ a=2 := by omega
    have cb : b=0 ∨ b=1 ∨ b=2 := by omega
    rcases ca with rfl | rfl | rfl <;> rcases cb with rfl | rfl | rfl
    · change joint d e 1 1=0
      omega
    · change joint d e 1 2=3
      omega
    · change joint d e 1 3=1
      omega
    · change joint d e 2 1=5
      omega
    · change joint d e 2 2=0
      omega
    · change joint d e 2 3=0
      omega
    · change joint d e 3 1=0
      omega
    · change joint d e 3 2=0
      omega
    · change joint d e 3 3=0
      omega

#print axioms degree_le_three
#print axioms degree_three_count
#print axioms active_cases
#print axioms histogram_cases

/-- Equality of the nine bounded degree cells gives equality of all labelled
fibres, including labels outside the degree range. -/
theorem histogram_labels (d e : Fin 9 → Nat) (p : Fin 11)
    (pd : ∀ x, 1≤d x) (pe : ∀ x, 1≤e x)
    (sd : ∀ x, d x≤3) (se : ∀ x, e x≤3)
    (counts : ∀ a b : Fin 3,
      joint d e (a.val+1) (b.val+1)=profileMatrix p a b) :
    ∀ label : Nat × Nat,
      card (fun x => (d x,e x)=label)=
      card (fun x => (D p x,R p x)=label) := by
  intro label
  have lhs : card (fun x => (d x,e x)=label)=joint d e label.1 label.2 :=
    card_congr (fun _ => by constructor; intro h; exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩; rintro ⟨h1,h2⟩; exact Prod.ext h1 h2)
  have rhs : card (fun x => (D p x,R p x)=label)=joint (D p) (R p) label.1 label.2 :=
    card_congr (fun _ => by constructor; intro h; exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩; rintro ⟨h1,h2⟩; exact Prod.ext h1 h2)
  rw [lhs,rhs]
  by_cases range : 1≤label.1 ∧ label.1≤3 ∧ 1≤label.2 ∧ label.2≤3
  · let a : Fin 3 := ⟨label.1-1,by omega⟩
    let b : Fin 3 := ⟨label.2-1,by omega⟩
    have av : a.val+1=label.1 := by dsimp [a]; omega
    have bv : b.val+1=label.2 := by dsimp [b]; omega
    have hc := counts a b
    have hp := profile_matrix p a b
    rw [av,bv] at hc hp
    exact hc.trans hp.symm
  · have leftZero : joint d e label.1 label.2=0 := by
      apply card_eq_zero.mpr
      intro x hx
      have := pd x; have := pe x; have := sd x; have := se x
      exact range (by omega)
    have rightZero : joint (D p) (R p) label.1 label.2=0 := by
      apply card_eq_zero.mpr
      intro x hx
      have := profile_bounded p x
      exact range (by omega)
    omega

/-- Every positive-degree nine-vertex counterexample at budget fourteen
has one of the eleven prescribed joint-degree profiles, up to relabeling.
The profile exclusions are separate finite certificates. -/
theorem normalize (E : Graph (Fin 9)) (loopless : Loopless E)
    (budget : arcCount E=14) (posOut : ∀ x, 1≤outdegree E x)
    (posIn : ∀ x, 1≤indegree E x) (large : 13<score E) :
    ∃ p : Fin 11, ∃ F : Graph (Fin 9),
      Nonempty (GraphRelabeling.Iso E F) ∧ RowPrefix.Prescribed (D p) (R p) F := by
  have shapes := active_cases E loopless budget posOut posIn large
  have outFour : 4≤card (ActiveOut E) := by
    rcases shapes with h|h|h <;> omega
  have inFour : 4≤card (ActiveIn E) := by
    rcases shapes with h|h|h <;> omega
  have outTotal : ((List.finRange 9).map (outdegree E)).sum=14 := by
    exact (SparseSupport.arc_rows E).symm.trans budget
  have inTotal : ((List.finRange 9).map (indegree E)).sum=14 := by
    exact (SparseSupport.arc_columns E).symm.trans budget
  have outSmall := degree_le_three (outdegree E) posOut outTotal outFour
  have inSmall := degree_le_three (indegree E) posIn inTotal inFour
  obtain ⟨p,counts⟩ := histogram_cases (outdegree E) (indegree E)
    posOut posIn outSmall inSmall outTotal inTotal shapes
  obtain ⟨f,g,left,right,labels⟩ := DegreeProfileRelabeling.labelled_bijection
    (fun x => (outdegree E x,indegree E x)) (fun x => (D p x,R p x))
    (histogram_labels (outdegree E) (indegree E) p posOut posIn outSmall inSmall counts)
  let F : Graph (Fin 9) := fun s t => E (f s) (f t)
  let iso : GraphRelabeling.Iso F E := ⟨f,g,left,right,fun _ _ => Iff.rfl⟩
  refine ⟨p,F,⟨iso.symm⟩,iso.symm.loopless loopless,?_,?_⟩
  · intro i
    have counted := IrregularTenProfile.card_pullback f g left right (E (f i))
    change outdegree F i=outdegree E (f i) at counted
    exact counted.trans (congrArg Prod.fst (labels i))
  · intro i
    have counted := IrregularTenProfile.card_pullback f g left right (fun s => E s (f i))
    change indegree F i=indegree E (f i) at counted
    exact counted.trans (congrArg Prod.snd (labels i))

#print axioms normalize

end Delivery.IrregularNine14Profile
