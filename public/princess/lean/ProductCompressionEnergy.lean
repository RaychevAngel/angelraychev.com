import ProductCompressionNormalization

/-! Finite weighted energies and their fiberwise lifting. -/
namespace Princess.ProductCompression
open Princess.CaptureRecurrence Princess.LadderCardinality Princess.SurvivorEnvelope

noncomputable def weightedOn {V : Type} (xs : List V) (weight : V → Nat)
    (A : Region V) : Nat := by
  classical
  exact (xs.map (fun v => if A v then weight v else 0)).sum

theorem weightedOn_cons {V : Type} (v : V) (vs : List V) (weight : V → Nat)
    (A : Region V) [Decidable (A v)] :
    weightedOn (v::vs) weight A = (if A v then weight v else 0) + weightedOn vs weight A := by
  classical
  simp [weightedOn]

theorem weightedOn_congr {V : Type} (xs : List V) (weight : V → Nat)
    (A B : Region V) (h : ∀ v ∈ xs, A v ↔ B v) :
    weightedOn xs weight A = weightedOn xs weight B := by
  classical
  unfold weightedOn
  congr 1
  apply List.map_congr_left
  intro v hv
  simp only [h v hv]

theorem weightedOn_split {V : Type} (xs : List V) (weight : V → Nat)
    (A B : Region V) : weightedOn xs weight A =
      weightedOn xs weight (fun v => A v ∧ B v) +
      weightedOn xs weight (fun v => A v ∧ ¬ B v) := by
  classical
  induction xs with
  | nil => simp [weightedOn]
  | cons v vs ih =>
      rw [weightedOn_cons,weightedOn_cons,weightedOn_cons]
      by_cases ha : A v <;> by_cases hb : B v <;>
        simp only [ha,hb,and_true,and_false,not_true_eq_false,not_false_eq_true,↓reduceIte] <;> omega

theorem weightedOn_map {V W : Type} (xs : List V) (f : V → W) (weight : W → Nat)
    (A : Region W) : weightedOn (xs.map f) weight A =
      weightedOn xs (fun v => weight (f v)) (fun v => A (f v)) := by
  simp only [weightedOn,List.map_map]
  rfl

theorem weightedOn_perm {V : Type} (xs ys : List V) (weight : V → Nat)
    (A : Region V) (perm : xs.Perm ys) : weightedOn xs weight A = weightedOn ys weight A := by
  classical
  induction perm with
  | nil => rfl
  | cons v h ih => simp only [weightedOn_cons,ih]
  | swap u v vs => simp only [weightedOn_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem sum_le_eq {V : Type} (xs : List V) (f g : V → Nat)
    (h : ∀ v ∈ xs, f v ≤ g v) :
    (xs.map f).sum ≤ (xs.map g).sum ∧
    ((xs.map f).sum = (xs.map g).sum → ∀ v ∈ xs, f v = g v) := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
      have hv := h v List.mem_cons_self
      have ht := ih (fun u hu => h u (List.mem_cons_of_mem v hu))
      simp only [List.map_cons,List.sum_cons]
      constructor
      · omega
      · intro he u hu
        rcases List.mem_cons.mp hu with hu | hu
        · subst u; omega
        · exact ht.2 (by omega) u hu

noncomputable def fiberEnergy {a b : Nat} (energy : Region (Fin a) → Nat)
    (weight : Fin b → Nat) (A : Region (Fin a × Fin b)) : Nat :=
  ((List.finRange b).map (fun j => energy (fiber A j) + weight j * card (fiber A j))).sum

theorem lift_energy {a b : Nat} {left : Fin a → Fin a → Prop}
    (C : Operator left) (right : Fin b → Fin b → Prop)
    (energy : Region (Fin a) → Nat) (weight : Fin b → Nat)
    (good : EnergyGood C energy) (size : ∀ A, card (C.map A) = card A) :
    EnergyGood (lift C right) (fiberEnergy energy weight) := by
  intro A
  let f := fun j : Fin b => energy (C.map (fiber A j)) + weight j * card (C.map (fiber A j))
  let g := fun j : Fin b => energy (fiber A j) + weight j * card (fiber A j)
  have point (j : Fin b) : f j ≤ g j := by
    dsimp [f,g]
    rw [size]
    have h := (good (fiber A j)).1
    omega
  have hs := sum_le_eq (List.finRange b) f g (fun j _ => point j)
  constructor
  · exact hs.1
  · intro he
    have each := hs.2 he
    funext v
    have h := each v.2 (List.mem_finRange v.2)
    dsimp [f,g] at h
    rw [size] at h
    have hfix := (good (fiber A v.2)).2 (by omega)
    exact congrFun hfix v.1

theorem weightedOn_append {V : Type} (xs ys : List V) (weight : V → Nat) (A : Region V) :
    weightedOn (xs ++ ys) weight A = weightedOn xs weight A + weightedOn ys weight A := by
  classical
  simp only [weightedOn,List.map_append,List.sum_append]

theorem weightedOn_add_constant {V : Type} (xs : List V) (weight : V → Nat)
    (constant : Nat) (A : Region V) :
    weightedOn xs (fun v => weight v + constant) A =
      weightedOn xs weight A + constant * cardOn xs A := by
  classical
  induction xs with
  | nil => simp [weightedOn,cardOn]
  | cons v vs ih =>
      rw [weightedOn_cons,weightedOn_cons,cardOn_cons]
      by_cases hv : A v <;> simp only [hv,↓reduceIte,Nat.mul_add,Nat.mul_one,Nat.mul_zero] <;> rw [ih] <;> omega

theorem weightedOn_product {V W : Type} (xs : List V) (ys : List W)
    (small : V → Nat) (large : W → Nat) (A : Region (V × W)) :
    weightedOn (ys.flatMap (fun j => xs.map (fun i => (i,j))))
      (fun v => small v.1 + large v.2) A =
    (ys.map (fun j => weightedOn xs small (fiber A j) + large j * cardOn xs (fiber A j))).sum := by
  classical
  induction ys with
  | nil => simp [weightedOn]
  | cons j js ih =>
      simp only [List.flatMap_cons,weightedOn_append,weightedOn_map,List.map_cons,List.sum_cons,ih]
      congr 1
      exact weightedOn_add_constant xs small (large j) (fiber A j)

theorem product_energy {a b : Nat} (small : Fin a → Nat) (large : Fin b → Nat)
    (A : Region (Fin a × Fin b)) :
    weightedOn (productList a b) (fun v => small v.1 + large v.2) A =
      fiberEnergy (weightedOn (List.finRange a) small) large A :=
  weightedOn_product (List.finRange a) (List.finRange b) small large A

theorem weightedOn_bound {V : Type} (xs : List V) (weight : V → Nat) (A : Region V)
    (bound : Nat) (h : ∀ v ∈ xs, weight v ≤ bound) :
    weightedOn xs weight A ≤ xs.length * bound := by
  classical
  induction xs with
  | nil => simp [weightedOn]
  | cons v vs ih =>
      rw [weightedOn_cons,List.length_cons,Nat.add_mul]
      have hv := h v List.mem_cons_self
      have ht := ih (fun u hu => h u (List.mem_cons_of_mem v hu))
      by_cases ha : A v <;> simp only [ha,↓reduceIte] <;> omega

end Princess.ProductCompression
#print axioms Princess.ProductCompression.lift_energy
