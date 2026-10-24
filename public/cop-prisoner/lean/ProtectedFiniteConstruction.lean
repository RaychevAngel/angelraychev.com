import ProtectedConstruction

/-! Exact capacities of the prescribed protected-offset construction. The
generic theorem uses the actual length of the greedy offset list; the finite
instances need only arithmetic/list evaluation, not game certificates. -/
namespace Delivery.ProtectedFiniteConstruction
open CyclicArithmetic DenseCombinatorics ProtectedCircle ProtectedGrowth
open FiniteGame Extremal CircleEnvelope RobustTwoMove ProtectedConstruction

theorem maximum {n a m : Nat} (large : 3≤a) (room : 2*(2*a+1)<n)
    (coprime : Nat.Coprime n (2*a+1)) (low : 3*n≤m)
    (high : m≤n*((offsets (by omega : 2*a+1<n)).length-1)) :
    IsMaximum n m (n*(n-1)-m) := by
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
    have count := listed_count _ (offsets_nodup large (by omega : 2*a+1<n))
    change card (fun d : Fin n => A d.val)=_ at count
    rwa [count]

def parameter (n : Nat) : Nat :=
  match n with
  | 25 | 26 | 35 => 4
  | 27 | 28 | 29 | 30 | 31 => 5
  | 32 | 33 | 34 => 6
  | _ => 0

def degree (n : Nat) : Nat :=
  match n with
  | 25 | 26 | 27 | 28 | 29 => 7
  | 30 | 31 | 32 | 33 => 8
  | 34 => 9
  | 35 => 10
  | _ => 0

theorem parameter_valid {n : Nat} (lo : 25≤n) (hi : n≤35) :
    3≤parameter n ∧ 2*(2*parameter n+1)<n ∧ Nat.Coprime n (2*parameter n+1) := by
  have checked : ∀ j : Fin 11, 3≤parameter (j.val+25) ∧
      2*(2*parameter (j.val+25)+1)<j.val+25 ∧
      Nat.Coprime (j.val+25) (2*parameter (j.val+25)+1) := by decide +kernel
  have h := checked ⟨n-25,by omega⟩
  have eq : n-25+25=n := by omega
  simpa only [eq] using h

def actualDegree (n a : Nat) : Nat :=
  if room : 2*a+1<n then (offsets room).length-1 else 0

theorem degree_checked (j : Fin 11) :
    actualDegree (j.val+25) (parameter (j.val+25))=degree (j.val+25) := by
  revert j
  decide +kernel

theorem degree_exact {n : Nat} (lo : 25≤n) (hi : n≤35) :
    (offsets (n:=n) (a:=parameter n) (by have h := parameter_valid lo hi; omega)).length-1=degree n := by
  have h := degree_checked ⟨n-25,by omega⟩
  have eq : n-25+25=n := by omega
  have short : 2*parameter n+1<n := by have h := parameter_valid lo hi; omega
  have h2 : actualDegree n (parameter n)=degree n := by simpa only [eq] using h
  simpa only [actualDegree,dif_pos short] using h2

theorem finite_maximum {n m : Nat} (lo : 25≤n) (hi : n≤35)
    (low : 3*n≤m) (high : m≤n*degree n) : IsMaximum n m (n*(n-1)-m) := by
  obtain ⟨large,room,coprime⟩ := parameter_valid lo hi
  apply maximum large room coprime low
  rwa [degree_exact lo hi]

#print axioms maximum
#print axioms finite_maximum
end Delivery.ProtectedFiniteConstruction
