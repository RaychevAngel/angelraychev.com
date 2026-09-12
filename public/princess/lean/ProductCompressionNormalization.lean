import ProductCompression

/-! Uniform finite-family normalization. The finite iteration count is independent
of the input set, preserving monotonicity and neighborhood subcommutation. -/
namespace Princess.ProductCompression

open Princess.CaptureRecurrence

def EnergyGood {V : Type} {adj : V → V → Prop} (C : Operator adj)
    (energy : Region V → Nat) : Prop :=
  ∀ A, energy (C.map A) ≤ energy A ∧ (energy (C.map A) = energy A → C.map A = A)

theorem energyGood_compose {V : Type} {adj : V → V → Prop}
    (C D : Operator adj) (energy : Region V → Nat)
    (hC : EnergyGood C energy) (hD : EnergyGood D energy) :
    EnergyGood (compose C D) energy := by
  intro A
  have hc := hC (D.map A)
  have hd := hD A
  constructor
  · exact Nat.le_trans hc.1 hd.1
  · intro he
    change energy (C.map (D.map A)) = energy A at he
    have hda : D.map A = A := hd.2 (by omega)
    have hcd : C.map (D.map A) = D.map A := hc.2 (by omega)
    exact hcd.trans hda

def cycle {V : Type} {adj : V → V → Prop} : List (Operator adj) → Operator adj
  | [] => identity adj
  | C :: Cs => compose (cycle Cs) C

theorem cycle_energy {V : Type} {adj : V → V → Prop}
    (Cs : List (Operator adj)) (energy : Region V → Nat)
    (good : ∀ C ∈ Cs, EnergyGood C energy) : EnergyGood (cycle Cs) energy := by
  induction Cs with
  | nil => exact fun _ => ⟨Nat.le_refl _,fun _ => rfl⟩
  | cons C Cs ih =>
      exact energyGood_compose (cycle Cs) C energy
        (ih (fun D hD => good D (List.mem_cons_of_mem C hD)))
        (good C (List.mem_cons_self))

theorem cycle_fixed_iff {V : Type} {adj : V → V → Prop}
    (Cs : List (Operator adj)) (energy : Region V → Nat)
    (good : ∀ C ∈ Cs, EnergyGood C energy) (A : Region V) :
    (cycle Cs).map A = A ↔ ∀ C ∈ Cs, C.map A = A := by
  induction Cs with
  | nil => simp [cycle,identity]
  | cons C Cs ih =>
      have hg := good C List.mem_cons_self
      have htail := fun D hD => good D (List.mem_cons_of_mem C hD)
      have hcy := cycle_energy Cs energy htail
      constructor
      · intro h
        have hc := hg A
        have ht := hcy (C.map A)
        have he : energy ((cycle Cs).map (C.map A)) = energy A := congrArg energy h
        have hca : C.map A = A := hc.2 (by omega)
        have hta : (cycle Cs).map A = A := by
          change (cycle Cs).map (C.map A) = A at h
          simpa only [hca] using h
        intro D hD
        rcases List.mem_cons.mp hD with hD | hD
        · subst D; exact hca
        · exact (ih htail).mp hta D hD
      · intro h
        have hca := h C List.mem_cons_self
        have hta := (ih htail).mpr (fun D hD => h D (List.mem_cons_of_mem C hD))
        change (cycle Cs).map (C.map A) = A
        rw [hca,hta]

def iterateMap {V : Type} {adj : V → V → Prop} (C : Operator adj) : Nat → Region V → Region V
  | 0, A => A
  | k+1, A => iterateMap C k (C.map A)

theorem iterateMap_mono {V : Type} {adj : V → V → Prop} (C : Operator adj)
    (k : Nat) (A B : Region V) (h : Subset A B) :
    Subset (iterateMap C k A) (iterateMap C k B) := by
  induction k generalizing A B with
  | zero => exact h
  | succ k ih => exact ih _ _ (C.mono A B h)

def iterate {V : Type} {adj : V → V → Prop} (C : Operator adj) (k : Nat) : Operator adj where
  map := iterateMap C k
  mono := iterateMap_mono C k
  neighbors := by
    induction k with
    | zero => exact fun _ _ h => h
    | succ k ih =>
        intro A v hv
        have h := ih (C.map A) v hv
        exact iterateMap_mono C k _ _ (C.neighbors A) v h

theorem iterate_fixed {V : Type} {adj : V → V → Prop} (C : Operator adj)
    (A : Region V) (fixed : C.map A = A) (k : Nat) : (iterate C k).map A = A := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change (iterate C k).map (C.map A) = A
      rw [fixed,ih]

theorem iterate_reaches_fixed {V : Type} {adj : V → V → Prop} (C : Operator adj)
    (energy : Region V → Nat) (good : EnergyGood C energy) (k : Nat) (A : Region V)
    (bound : energy A ≤ k) : C.map ((iterate C k).map A) = (iterate C k).map A := by
  classical
  induction k generalizing A with
  | zero =>
      exact (good A).2 (by have := (good A).1; omega)
  | succ k ih =>
      by_cases hfix : C.map A = A
      · rw [iterate_fixed C A hfix (k+1)]
        exact hfix
      · have hg := good A
        have strict : energy (C.map A) < energy A := by
          apply Classical.byContradiction
          intro h
          exact hfix (hg.2 (by omega))
        exact ih (C.map A) (by omega)

theorem iterate_card {V : Type} {adj : V → V → Prop} (C : Operator adj)
    (measure : Region V → Nat) (size : ∀ A, measure (C.map A) = measure A)
    (k : Nat) (A : Region V) : measure ((iterate C k).map A) = measure A := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
      change measure ((iterate C k).map (C.map A)) = measure A
      rw [ih,size]

theorem cycle_card {V : Type} {adj : V → V → Prop} (Cs : List (Operator adj))
    (measure : Region V → Nat) (size : ∀ C ∈ Cs, ∀ A, measure (C.map A) = measure A)
    (A : Region V) : measure ((cycle Cs).map A) = measure A := by
  induction Cs generalizing A with
  | nil => rfl
  | cons C Cs ih =>
      change measure ((cycle Cs).map (C.map A)) = measure A
      rw [ih (fun D hD => size D (List.mem_cons_of_mem C hD))]
      exact size C List.mem_cons_self A

def normalize {V : Type} {adj : V → V → Prop} (Cs : List (Operator adj)) (bound : Nat) :
    Operator adj := iterate (cycle Cs) bound

theorem normalized_common_fixed {V : Type} {adj : V → V → Prop}
    (Cs : List (Operator adj)) (energy : Region V → Nat) (bound : Nat)
    (good : ∀ C ∈ Cs, EnergyGood C energy) (bounded : ∀ A, energy A ≤ bound)
    (A : Region V) : ∀ C ∈ Cs, C.map ((normalize Cs bound).map A) = (normalize Cs bound).map A := by
  apply (cycle_fixed_iff Cs energy good _).mp
  exact iterate_reaches_fixed (cycle Cs) energy (cycle_energy Cs energy good) bound A (bounded A)

theorem normalize_idempotent {V : Type} {adj : V → V → Prop}
    (Cs : List (Operator adj)) (energy : Region V → Nat) (bound : Nat)
    (good : ∀ C ∈ Cs, EnergyGood C energy) (bounded : ∀ A, energy A ≤ bound)
    (A : Region V) : (normalize Cs bound).map ((normalize Cs bound).map A) =
      (normalize Cs bound).map A := by
  exact iterate_fixed (cycle Cs) _
    (iterate_reaches_fixed (cycle Cs) energy (cycle_energy Cs energy good) bound A (bounded A)) bound

end Princess.ProductCompression
#print axioms Princess.ProductCompression.normalized_common_fixed
#print axioms Princess.ProductCompression.normalize_idempotent
