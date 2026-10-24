import PairCodeRouting

/-! An explicit k(k-5)-entry list of distinct separated pair codes.
Entry x has i=x mod k and j=i+(3+floor(x/k)) mod k.  Use the point
part when i<j and the line part otherwise. Each unordered separated pair
therefore occurs once in each part, with no division by two in the count. -/
namespace Delivery.PairCodeCapacity
open DenseTwoType CyclicArithmetic PairCodeGeometry

def firstIndex {k : Nat} (hk : 6 ≤ k) (x : Fin (k*(k-5))) : Fin k :=
  ⟨x.val % k,Nat.mod_lt _ (by omega)⟩

def distance {k : Nat} (x : Fin (k*(k-5))) : Nat := x.val / k + 3

theorem distance_bounds {k : Nat} (hk : 6 ≤ k) (x : Fin (k*(k-5))) :
    3 ≤ distance x ∧ distance x + 2 < k := by
  have upper : x.val / k < k-5 := by
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mpr
    simpa only [Nat.mul_comm] using x.isLt
  unfold distance
  constructor
  · exact Nat.le_add_left 3 _
  · have bound := Nat.add_lt_add_right upper 5
    have cancel : k-5+5=k := Nat.sub_add_cancel (by omega)
    rw [cancel] at bound
    simpa only [Nat.add_assoc] using bound

def secondIndex {k : Nat} (hk : 6 ≤ k) (x : Fin (k*(k-5))) : Fin k :=
  shift (firstIndex hk x) (distance x)

theorem separated_indices {k : Nat} (hk : 6 ≤ k) (x : Fin (k*(k-5))) :
    Far (firstIndex hk x) (secondIndex hk x) := by
  have bounds := distance_bounds hk x
  unfold secondIndex Far
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact Ne.symm (shift_ne_self _ (by omega) (by omega))
  · exact shift_ne_of_lt_gap _ (by omega) (by omega)
  · simpa only [shift_add] using shift_ne_self (firstIndex hk x)
      (d := distance x+1) (by omega) (by omega)
  · exact shift_ne_of_lt_gap _ (by omega) (by omega)
  · simpa only [shift_add] using shift_ne_self (firstIndex hk x)
      (d := distance x+2) (by omega) (by omega)

def makeCode {k : Nat} (i j : Fin k) (far : Far i j) : Code k :=
  if i.val < j.val then ⟨.point i,.point j,far⟩ else ⟨.line i,.line j,far⟩

theorem makeCode_injective {k : Nat} {i j u v : Fin k}
    (hij : Far i j) (huv : Far u v)
    (same : ∀ z, (makeCode i j hij).Mem z ↔ (makeCode u v huv).Mem z) :
    i = u ∧ j = v := by
  have ha := (same (makeCode i j hij).a).mp (Or.inl rfl)
  have hb := (same (makeCode i j hij).b).mp (Or.inr rfl)
  have neq := hij.1
  by_cases h : i.val < j.val <;> by_cases h' : u.val < v.val
  all_goals simp [makeCode,h,h',Code.Mem] at ha hb
  all_goals rcases ha with ha | ha <;> rcases hb with hb | hb
  all_goals first
    | exact ⟨ha,hb⟩
    | exact False.elim (neq (ha.trans hb.symm))
    | have va := congrArg Fin.val ha
      have vb := congrArg Fin.val hb
      have different : i.val ≠ j.val := fun e => neq (Fin.ext e)
      omega

def code {k : Nat} (hk : 6 ≤ k) (x : Fin (k*(k-5))) : Code k :=
  makeCode (firstIndex hk x) (secondIndex hk x) (separated_indices hk x)

theorem code_injective {k : Nat} (hk : 6 ≤ k) {x y : Fin (k*(k-5))}
    (same : ∀ u, (code hk x).Mem u ↔ (code hk y).Mem u) : x = y := by
  obtain ⟨first,second⟩ := makeCode_injective (separated_indices hk x)
    (separated_indices hk y) same
  have residue : x.val % k = y.val % k := congrArg Fin.val first
  have offsets : distance x % k = distance y % k := by
    apply (shift_eq_iff (firstIndex hk x) _ _).mp
    simpa only [secondIndex,← first] using second
  have bx := distance_bounds hk x
  have by' := distance_bounds hk y
  rw [Nat.mod_eq_of_lt (by omega : distance x < k),
    Nat.mod_eq_of_lt (by omega : distance y < k)] at offsets
  have quotient : x.val / k = y.val / k := by unfold distance at offsets; omega
  have dx := Nat.mod_add_div x.val k
  have dy := Nat.mod_add_div y.val k
  rw [residue,quotient] at dx
  exact Fin.ext (dx.symm.trans dy)

/-- The first q prescribed codes, whenever q is within the proved capacity. -/
def codes {k q : Nat} (hk : 6 ≤ k) (capacity : q ≤ k*(k-5)) (x : Fin q) : Code k :=
  code hk ⟨x.val,Nat.lt_of_lt_of_le x.isLt capacity⟩

theorem distinct {k q : Nat} (hk : 6 ≤ k) (capacity : q ≤ k*(k-5)) :
    PairCodeRouting.Distinct (codes hk capacity) := by
  intro x y same
  have eq := code_injective hk same
  exact Fin.ext (congrArg (fun z : Fin (k*(k-5)) => z.val) eq)

#print axioms code_injective
#print axioms distinct
end Delivery.PairCodeCapacity
