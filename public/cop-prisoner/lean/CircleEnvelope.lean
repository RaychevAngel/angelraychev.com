import CirclePropagation

/-! Literal five-offset envelopes: local arithmetic is discharged against
closed pursuer neighborhoods, including waiting. -/
namespace Delivery.CircleEnvelope
open CyclicArithmetic CirclePropagation RobustTwoMove

def Allowed (n h d : Nat) : Prop :=
  d < n ∧ (d%4=0 ∨ d%4=1 ∨ d=h) ∧ d ≠ 2*h-1

def Envelope {n : Nat} (A : Nat → Prop) (s t : Fin n) : Prop :=
  s ≠ t ∧ ∃ d, A d ∧ t = shift s d

theorem legal_offset {n : Nat} {A : Nat → Prop} (zero : A 0)
    {s t : Fin n} (move : Legal (Envelope A) s t) :
    ∃ d, A d ∧ shift s d = t := by
  rcases move with same | ⟨_,d,inside,same⟩
  · exact ⟨0,zero,(shift_zero s).trans same⟩
  · exact ⟨d,inside,same.symm⟩

theorem compare_offsets {n : Nat} (s c : Fin n) {a b d e : Nat}
    (first : shift c a = shift s d) (second : shift c b = shift s e) :
    (d+b)%n = (e+a)%n := by
  apply (shift_eq_iff s _ _).mp
  calc
    shift s (d+b) = shift (shift s d) b := (shift_add s d b).symm
    _ = shift (shift c a) b := by rw [first]
    _ = shift c (a+b) := shift_add c a b
    _ = shift c (b+a) := by rw [Nat.add_comm a b]
    _ = shift (shift c b) a := (shift_add c b a).symm
    _ = shift (shift s e) a := by rw [second]
    _ = shift s (e+a) := shift_add s e a

theorem compare_mod_four {n : Nat} (four : n%4=0) (s c : Fin n) {a b d e : Nat}
    (first : shift c a = shift s d) (second : shift c b = shift s e) :
    (d+b)%4 = (e+a)%4 := by
  have eq := congrArg (fun x => x%4) (compare_offsets s c first second)
  have dvd : 4 ∣ n := Nat.dvd_of_mod_eq_zero four
  simpa only [Nat.mod_mod_of_dvd _ dvd] using eq

theorem zero_allowed {n h : Nat} (hh : 7 ≤ h) (room : 2*h+2 ≤ n) : Allowed n h 0 := by
  constructor
  · omega
  constructor
  · exact Or.inl rfl
  · omega

/-- A full modulo-four envelope cannot cover the h,1 pair from a different source. -/
theorem pair_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (four : n%4=0) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (n := n) (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (n := n) (Allowed n h)) c (shift s 1)) := by
  rintro ⟨first,second⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have congruence := compare_mod_four four s c ea eb
  have aclass : a%4=0 ∨ a%4=1 := by rcases ha.2.1 with h | h | h; exact Or.inl h; exact Or.inr h; contradiction
  have bexception : b = h := by rcases hb.2.1 with h | h | h <;> omega
  subst b
  have equal := compare_offsets s c ea eb
  have leftSmall : h+h < n := by omega
  rw [Nat.mod_eq_of_lt leftSmall] at equal
  have rightSmall : 1+a < n := by
    by_cases small : 1+a<n
    · exact small
    · have edge : 1+a=n := by have := ha.1; omega
      rw [edge,Nat.mod_self] at equal
      omega
  rw [Nat.mod_eq_of_lt rightSmall] at equal
  exact ha.2.2 (by omega)

theorem triple_a_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (four : n%4=0) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (n := n) (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (n := n) (Allowed n h)) c (shift s (h-3)) ∧
      Legal (Envelope (n := n) (Allowed n h)) c (shift s (h-2))) := by
  rintro ⟨first,second,third⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  obtain ⟨d,hd,ed⟩ := legal_offset (zero_allowed hh room) third
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have congruence1 := compare_mod_four four s c ea eb
  have congruence2 := compare_mod_four four s c ea ed
  have classesA := ha.2.1
  have classesB := hb.2.1
  have classesD := hd.2.1
  omega

theorem triple_b_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (four : n%4=0) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (n := n) (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (n := n) (Allowed n h)) c (shift s (h-2)) ∧
      Legal (Envelope (n := n) (Allowed n h)) c (shift s (h+2))) := by
  rintro ⟨first,second,third⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  obtain ⟨d,hd,ed⟩ := legal_offset (zero_allowed hh room) third
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have congruence1 := compare_mod_four four s c ea eb
  have congruence2 := compare_mod_four four s c ea ed
  have classesA := ha.2.1
  have classesB := hb.2.1
  have classesD := hd.2.1
  have beq : b = h := by omega
  have deq : d = h := by omega
  subst b; subst d
  have collision : shift s (h-2) = shift s (h+2) := eb.symm.trans ed
  exact shift_ne_of_lt_gap s (by omega) (by omega) collision

theorem escapes {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (four : n%4=0) : Escape (Envelope (n := n) (Allowed n h)) h :=
  ⟨pair_escape hh residue room four,triple_a_escape hh residue room four,
    triple_b_escape hh residue room four⟩

theorem compulsory_allowed {n h d : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (member : Compulsory h d) : Allowed n h d ∧ 0 < d := by
  rcases member with rfl | rfl | rfl | rfl | rfl <;> unfold Allowed <;> omega

theorem base_subset {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) : Subgraph (Base (n := n) h) (Envelope (n := n) (Allowed n h)) := by
  rintro s t ⟨d,member,rfl⟩
  have valid := compulsory_allowed hh residue room member
  exact ⟨Ne.symm (shift_ne_self s valid.2 valid.1.1),d,valid.1,rfl⟩

/-- The complete arbitrary-subset game theorem for the full envelope. -/
theorem universal {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (four : n%4=0) (coprime : Nat.Coprime n h)
    {G : Graph (Fin n)} (lower : Subgraph (Base h) G)
    (upper : Subgraph G (Envelope (n := n) (Allowed n h))) (t s : Fin n) :
    Universal G t (3*n-1) s :=
  CirclePropagation.universal hh (by omega) coprime lower upper
    (escapes hh residue room four) t s

#print axioms escapes
#print axioms universal
end Delivery.CircleEnvelope
