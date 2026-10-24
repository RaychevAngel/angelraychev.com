import DenseTwoType

/-! Literal separated pairs for the two-type core.  The line labels are
L'_i=L_(i-1), as in DenseTwoType.  A code uses two vertices of one type,
whose indices differ by none of 0, ±1, ±2. -/
namespace Delivery.PairCodeGeometry
open DenseTwoType CyclicArithmetic

def Far {k : Nat} (i j : Fin k) : Prop :=
  i ≠ j ∧ shift i 1 ≠ j ∧ shift j 1 ≠ i ∧ shift i 2 ≠ j ∧ shift j 2 ≠ i

def Separated {k : Nat} : Vertex k → Vertex k → Prop
  | .point i, .point j => Far i j
  | .line i, .line j => Far i j
  | _, _ => False

structure Code (k : Nat) where
  a : Vertex k
  b : Vertex k
  separated : Separated a b

def Code.Mem {k : Nat} (K : Code k) (u : Vertex k) : Prop := u = K.a ∨ u = K.b

theorem separated_ne {k : Nat} {a b : Vertex k} (h : Separated a b) : a ≠ b := by
  cases a <;> cases b <;> simp only [Separated] at h
  all_goals first | exact False.elim h | exact fun e => h.1 (by cases e; rfl)

theorem separated_symm {k : Nat} {a b : Vertex k} (h : Separated a b) : Separated b a := by
  cases a <;> cases b <;> simp only [Separated,Far] at * <;> grind

theorem far_pair {k : Nat} {i j c : Fin k} (far : Far i j) {d : Nat}
    (small : d = 1 ∨ d = 2) (hi : i = c ∨ i = shift c d)
    (hj : j = c ∨ j = shift c d) : False := by
  rcases small with rfl | rfl
  all_goals rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  all_goals simp only [Far] at far
  all_goals simp_all

theorem not_row {k : Nat} {a b c : Vertex k} (code : Separated a b)
    (ha : missing c a) (hb : missing c b) : False := by
  cases a <;> cases b <;> cases c <;>
    simp [Separated,missing,first,second] at code ha hb
  all_goals try contradiction
  · rename_i i j c
    exact far_pair (c := shift c 3) code (Or.inr rfl)
      (by simpa only [shift_add] using ha) (by simpa only [shift_add] using hb)
  · exact far_pair code (Or.inl rfl) ha hb

theorem not_column {k : Nat} {a b t : Vertex k} (code : Separated a b)
    (ha : missing a t) (hb : missing b t) : False := by
  cases a <;> cases b <;> cases t <;>
    simp [Separated,missing,first,second] at code ha hb
  all_goals try contradiction
  · rename_i i j t
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact code.1 (ha.symm.trans hb)
    · exact code.2.2.1 (hb.symm.trans ha)
    · exact code.2.1 (ha.symm.trans hb)
    · exact code.1 (shift_injective (ha.symm.trans hb))
  · rename_i i j t
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact code.1 (shift_injective (ha.symm.trans hb))
    · apply code.2.2.2.2
      apply shift_injective (d := 3)
      simpa only [shift_add] using hb.symm.trans ha
    · apply code.2.2.2.1
      apply shift_injective (d := 3)
      simpa only [shift_add] using ha.symm.trans hb
    · exact code.1 (shift_injective (ha.symm.trans hb))

theorem mixed_impossible {k : Nat} {s t a b : Vertex k}
    (code : Separated a b) (pair : missing s t)
    (ha : missing s a) (hb : missing b t) : False := by
  cases s <;> cases t <;> cases a <;> cases b <;>
    simp [Separated,missing,first,second] at *

theorem not_block {k : Nat} {s t a b : Vertex k}
    (code : Separated a b) (pair : missing s t)
    (ha : missing s a ∨ missing a t) (hb : missing s b ∨ missing b t) : False := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact not_row code ha hb
  · exact mixed_impossible code pair ha hb
  · exact mixed_impossible (separated_symm code) pair hb ha
  · exact not_column code ha hb

theorem row_not_column {k : Nat} (hk : 5 ≤ k) (c t : Vertex k)
    (ha : missing (first c) t) (hb : missing (second c) t) : False := by
  cases c <;> cases t <;> simp [missing,first,second,shift_add] at ha hb
  all_goals rename_i i t
  all_goals rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals first
    | exact shift_ne_of_lt_gap i (by omega) (by omega) (ha.symm.trans hb)
    | exact shift_ne_of_lt_gap i (by omega) (by omega) (hb.symm.trans ha)

theorem code_subset {k : Nat} (K L : Code k)
    (ha : L.Mem K.a) (hb : L.Mem K.b) : ∀ u, K.Mem u ↔ L.Mem u := by
  have different := separated_ne K.separated
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (different (ha.trans hb.symm))
  · intro u; simp only [Code.Mem,ha,hb]
  · intro u; simp only [Code.Mem,ha,hb,or_comm]
  · exact False.elim (different (ha.trans hb.symm))

theorem row_escape {k : Nat} (hk : 5 ≤ k) (K : Code k) (c : Vertex k) :
    ∃ u, missing c u ∧ ¬ K.Mem u := by
  classical
  by_cases a : K.Mem (first c)
  · by_cases b : K.Mem (second c)
    · have different := neighbours_distinct hk c
      rcases a with a | a <;> rcases b with b | b
      · exact False.elim (different (a.trans b.symm))
      · exact False.elim (not_row K.separated (Or.inl a.symm) (Or.inr b.symm))
      · exact False.elim (not_row K.separated (Or.inr b.symm) (Or.inl a.symm))
      · exact False.elim (different (a.trans b.symm))
    · exact ⟨second c,Or.inr rfl,b⟩
  · exact ⟨first c,Or.inl rfl,a⟩

def kind {k : Nat} : Vertex k → Bool
  | .point _ => false
  | .line _ => true

theorem missing_kind {k : Nat} {a b : Vertex k} (h : missing a b) : kind a ≠ kind b := by
  cases a <;> cases b <;> simp [kind,missing,first,second] at *

theorem row_kind {k : Nat} {c u : Vertex k} (h : missing c u) : kind u = kind (first c) := by
  rcases h with rfl | rfl
  · rfl
  · cases c <;> rfl

theorem code_kind {k : Nat} (K : Code k) {u v : Vertex k}
    (hu : K.Mem u) (hv : K.Mem v) : kind u = kind v := by
  have same : kind K.a = kind K.b := by
    have h := K.separated
    cases a : K.a <;> cases b : K.b <;> simp [a,b,Separated,kind] at *
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp_all

theorem column_escape {k : Nat} (K : Code k) (t : Vertex k) :
    ∃ u, K.Mem u ∧ ¬ missing u t := by
  classical
  by_cases ha : missing K.a t
  · exact ⟨K.b,Or.inr rfl,fun hb => not_column K.separated ha hb⟩
  · exact ⟨K.a,Or.inl rfl,ha⟩

theorem block_escape {k : Nat} (K : Code k) {s t : Vertex k} (pair : missing s t) :
    ∃ u, K.Mem u ∧ ¬ missing s u ∧ ¬ missing u t := by
  classical
  by_cases ha : ¬ missing s K.a ∧ ¬ missing K.a t
  · exact ⟨K.a,Or.inl rfl,ha⟩
  · have hb : ¬ missing s K.b ∧ ¬ missing K.b t := by
      apply Classical.byContradiction
      intro no
      exact not_block K.separated pair (by grind) (by grind)
    exact ⟨K.b,Or.inr rfl,hb⟩

theorem difference {k : Nat} (K L : Code k)
    (different : ¬ ∀ u, K.Mem u ↔ L.Mem u) : ∃ u, K.Mem u ∧ ¬ L.Mem u := by
  classical
  by_cases ha : L.Mem K.a
  · by_cases hb : L.Mem K.b
    · exact False.elim (different (code_subset K L ha hb))
    · exact ⟨K.b,Or.inr rfl,hb⟩
  · exact ⟨K.a,Or.inl rfl,ha⟩

theorem row_target_escape {k : Nat} (hk : 5 ≤ k) (K : Code k) {t : Vertex k}
    (target : K.Mem t) (c : Vertex k) :
    ∃ u, missing c u ∧ ¬ K.Mem u ∧ ¬ missing u t := by
  classical
  by_cases same : kind (first c) = kind t
  · obtain ⟨u,hu,notCode⟩ := row_escape hk K c
    exact ⟨u,hu,notCode,fun h => missing_kind h ((row_kind hu).trans same)⟩
  · have get : ∃ u, missing c u ∧ ¬ missing u t := by
      by_cases ha : missing (first c) t
      · exact ⟨second c,Or.inr rfl,fun hb => row_not_column hk c t ha hb⟩
      · exact ⟨first c,Or.inl rfl,ha⟩
    obtain ⟨u,hu,last⟩ := get
    exact ⟨u,hu,fun mem => same ((row_kind hu).symm.trans (code_kind K mem target)),last⟩

theorem code_target_escape {k : Nat} (K L : Code k) {t : Vertex k}
    (target : K.Mem t) (different : ¬ ∀ u, L.Mem u ↔ K.Mem u) :
    ∃ u, L.Mem u ∧ ¬ K.Mem u ∧ ¬ missing u t := by
  classical
  by_cases same : kind L.a = kind t
  · obtain ⟨u,hu,notCode⟩ := difference L K different
    exact ⟨u,hu,notCode,fun h => missing_kind h ((code_kind L hu (Or.inl rfl)).trans same)⟩
  · obtain ⟨u,hu,last⟩ := column_escape L t
    exact ⟨u,hu,fun mem => same ((code_kind L (Or.inl rfl) hu).trans
      (code_kind K mem target)),last⟩

#print axioms not_block
#print axioms row_escape
#print axioms code_target_escape
end Delivery.PairCodeGeometry
