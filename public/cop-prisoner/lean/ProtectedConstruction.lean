import ProtectedGrowth

/-! Exact-budget protected circles. The envelope is obtained by the specified
increasing-residue greedy extension, followed by a lexicographic arrow prefix. -/
namespace Delivery.ProtectedConstruction
open CyclicArithmetic DenseCombinatorics ProtectedCircle ProtectedGrowth
open FiniteGame Extremal CircleEnvelope RobustTwoMove

def initial {n a : Nat} (room : 2*a+1<n) : List (Fin n) :=
  [⟨0,by omega⟩,⟨1,by omega⟩,⟨a,by omega⟩,⟨2*a+1,room⟩]

theorem listed_initial {n a : Nat} (room : 2*a+1<n) (d : Nat) :
    Listed (initial room) d ↔ Initial a d := by
  simp [Listed,initial,Initial,Core,eq_comm]

theorem initial_nodup {n a : Nat} (large : 3≤a) (room : 2*a+1<n) :
    (initial room).Nodup := by
  simp [initial,Fin.ext_iff]
  omega

def offsets {n a : Nat} (room : 2*a+1<n) : List (Fin n) :=
  grow a (List.finRange n) (initial room)

theorem offsets_nodup {n a : Nat} (large : 3≤a) (room : 2*a+1<n) :
    (offsets room).Nodup := grow_nodup _ _ (initial_nodup large room)

theorem offsets_size {n a : Nat} (room : 2*a+1<n) : (n+6)/7≤(offsets room).length :=
  grown_size _

theorem offsets_contains {n a : Nat} (room : 2*a+1<n) {d : Nat} (member : Initial a d) :
    Listed (offsets room) d := by
  obtain ⟨x,hx,same⟩ := (listed_initial room d).mpr member
  exact ⟨x,grow_contains _ _ hx,same⟩

theorem offsets_protected {n a : Nat} (large : 3≤a) (room : 2*(2*a+1)<n) :
    Protected n a (Listed (offsets (by omega : 2*a+1<n))) := by
  apply grow_protected large (by omega)
  intro u v hu hv ne x y hx hy same
  exact initial_protected large room u v hu hv ne x y
    ((listed_initial _ x).mp hx) ((listed_initial _ y).mp hy) same

theorem listed_count {n : Nat} (xs : List (Fin n)) (nodup : xs.Nodup) :
    card (fun d : Fin n => Listed xs d.val)=xs.length := by
  have perm := (List.perm_ext_iff_of_nodup
    (elems_nodup (fun d : Fin n => Listed xs d.val)) nodup).mpr (fun d => by simp)
  exact perm.length_eq

theorem base_eq {n a : Nat} (large : 3≤a) (room : 2*a+1<n) :
    (Base (n := n) a)=Envelope (Initial a) := by
  funext s t
  apply propext
  constructor
  · rintro ⟨d,core,rfl⟩
    have positive : 0<d := by rcases core with rfl | rfl | rfl <;> omega
    have small : d<n := by rcases core with rfl | rfl | rfl <;> omega
    exact ⟨Ne.symm (shift_ne_self s positive small),d,Or.inr core,rfl⟩
  · rintro ⟨different,d,member,equal⟩
    rcases member with rfl | core
    · simp only [shift_zero] at equal
      exact False.elim (different equal.symm)
    · exact ⟨d,core,equal⟩

theorem base_arcCount {n a : Nat} (large : 3≤a) (room : 2*a+1<n) :
    arcCount (Base (n := n) a)=3*n := by
  rw [base_eq large room,CircleConstruction.envelope_arcCount _ ?_ (Or.inl rfl)]
  · have equal : card (fun d : Fin n => Initial a d.val)=4 := by
      rw [card_congr (Q := fun d : Fin n => Listed (initial room) d.val)
        (fun d => (listed_initial room d.val).symm),listed_count _ (initial_nodup large room)]
      rfl
    rw [equal]
    omega
  · intro d member
    rcases member with rfl | rfl | rfl | rfl <;> omega

/-- Every optional-arrow prefix in the protected-circle interval attains the
missing-pair upper bound. All offset and game premises are discharged. -/
theorem maximum {n a m : Nat} (large : 3≤a) (room : 2*(2*a+1)<n)
    (coprime : Nat.Coprime n (2*a+1)) (low : 3*n≤m)
    (high : m≤n*((n+6)/7-1)) : IsMaximum n m (n*(n-1)-m) := by
  let A := Listed (offsets (by omega : 2*a+1<n))
  have zero : A 0 := offsets_contains _ (Or.inl rfl)
  have bounded : ∀ d, A d→d<n := by
    rintro d ⟨x,_,rfl⟩
    exact x.isLt
  have subset : Subgraph (Base (n := n) a) (Envelope A) := by
    intro s t edge
    have original := congrFun (congrFun (base_eq large (by omega : 2*a+1<n)) s) t
    rw [original] at edge
    obtain ⟨different,d,member,equal⟩ := edge
    exact ⟨different,d,offsets_contains _ member,equal⟩
  apply GuaranteedPrefix.maximum (Base a) (Envelope A) subset (fun _ e => e.1 rfl)
  · intro G lower upper s t
    exact universal_guaranteed (ProtectedCircle.envelope_universal large (by omega) coprime zero
      (offsets_protected large room) lower upper t s)
  · rw [base_arcCount large (by omega)]
    exact low
  · rw [CircleConstruction.envelope_arcCount A bounded zero]
    have size := offsets_size (by omega : 2*a+1<n)
    have count := listed_count _ (offsets_nodup large (by omega : 2*a+1<n))
    change card (fun d : Fin n => A d.val)=_ at count
    rw [count]
    exact Nat.le_trans high (Nat.mul_le_mul_left n (by omega))

#print axioms maximum
end Delivery.ProtectedConstruction
