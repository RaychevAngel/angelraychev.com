import CircleEnvelope

/-! The wraparound gap makes every putative local covering use a common
integer lift. Hence the modulo-four escape argument applies at arbitrary n. -/
namespace Delivery.CircleGuarded
open CyclicArithmetic CirclePropagation CircleEnvelope RobustTwoMove

def Allowed (n h d : Nat) : Prop := CircleEnvelope.Allowed n h d ∧ d ≤ n-h

theorem equal_of_close_mod {n low x y : Nat} (base : low < n)
    (xlow : low ≤ x) (ylow : low ≤ y) (xhigh : x < low+n) (yhigh : y < low+n)
    (same : x%n=y%n) : x=y := by
  have xsmall : x<2*n := by omega
  have ysmall : y<2*n := by omega
  by_cases wx : x<n <;> by_cases wy : y<n
  · rw [Nat.mod_eq_of_lt wx,Nat.mod_eq_of_lt wy] at same
    exact same
  · have ym : y%n=y-n := by
      rw [Nat.mod_eq_sub_mod (by omega : n≤y),Nat.mod_eq_of_lt (by omega : y-n<n)]
    rw [Nat.mod_eq_of_lt wx,ym] at same
    omega
  · have xm : x%n=x-n := by
      rw [Nat.mod_eq_sub_mod (by omega : n≤x),Nat.mod_eq_of_lt (by omega : x-n<n)]
    rw [xm,Nat.mod_eq_of_lt wy] at same
    omega
  · have xm : x%n=x-n := by
      rw [Nat.mod_eq_sub_mod (by omega : n≤x),Nat.mod_eq_of_lt (by omega : x-n<n)]
    have ym : y%n=y-n := by
      rw [Nat.mod_eq_sub_mod (by omega : n≤y),Nat.mod_eq_of_lt (by omega : y-n<n)]
    rw [xm,ym] at same
    omega

/-- Targets in an interval shorter than h cannot wrap relative to a covering
whose allowed offsets end at n−h. Their congruence is an integer equality. -/
theorem compare_lift {n h a b d e low : Nat} (s c : Fin n)
    (room : h ≤ n) (lowSmall : low < n)
    (aSmall : a ≤ n-h) (bSmall : b ≤ n-h)
    (dlow : low ≤ d) (elow : low ≤ e) (dhigh : d < low+h) (ehigh : e < low+h)
    (first : shift c a = shift s d) (second : shift c b = shift s e) : d+b=e+a := by
  exact equal_of_close_mod lowSmall
    (by omega) (by omega) (by omega) (by omega) (compare_offsets s c first second)

theorem zero_allowed {n h : Nat} (hh : 7 ≤ h) (room : 2*h+2 ≤ n) : Allowed n h 0 :=
  ⟨CircleEnvelope.zero_allowed hh room,Nat.zero_le _⟩

theorem pair_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (Allowed n h)) c (shift s 1)) := by
  rintro ⟨first,second⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have equality := compare_lift (low := 1) s c (by omega) (by omega) ha.2 hb.2
    (by omega) (by omega) (by omega) (by omega) ea eb
  have aclass := ha.1.2.1
  have bclass := hb.1.2.1
  have beq : b=h := by omega
  exact ha.1.2.2 (by omega)

theorem triple_a_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (Allowed n h)) c (shift s (h-3)) ∧
      Legal (Envelope (Allowed n h)) c (shift s (h-2))) := by
  rintro ⟨first,second,third⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  obtain ⟨d,hd,ed⟩ := legal_offset (zero_allowed hh room) third
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have equality1 := compare_lift (low := h-3) s c (by omega) (by omega) ha.2 hb.2
    (by omega) (by omega) (by omega) (by omega) ea eb
  have equality2 := compare_lift (low := h-3) s c (by omega) (by omega) ha.2 hd.2
    (by omega) (by omega) (by omega) (by omega) ea ed
  have classesA := ha.1.2.1
  have classesB := hb.1.2.1
  have classesD := hd.1.2.1
  omega

theorem triple_b_escape {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (s c : Fin n) (different : c ≠ s) :
    ¬ (Legal (Envelope (Allowed n h)) c (shift s h) ∧
      Legal (Envelope (Allowed n h)) c (shift s (h-2)) ∧
      Legal (Envelope (Allowed n h)) c (shift s (h+2))) := by
  rintro ⟨first,second,third⟩
  obtain ⟨a,ha,ea⟩ := legal_offset (zero_allowed hh room) first
  obtain ⟨b,hb,eb⟩ := legal_offset (zero_allowed hh room) second
  obtain ⟨d,hd,ed⟩ := legal_offset (zero_allowed hh room) third
  by_cases exceptional : a = h
  · rw [exceptional] at ea
    exact different (shift_injective ea)
  have equality1 := compare_lift (low := h-2) s c (by omega) (by omega) ha.2 hb.2
    (by omega) (by omega) (by omega) (by omega) ea eb
  have equality2 := compare_lift (low := h-2) s c (by omega) (by omega) ha.2 hd.2
    (by omega) (by omega) (by omega) (by omega) ea ed
  have classesA := ha.1.2.1
  have classesB := hb.1.2.1
  have classesD := hd.1.2.1
  have beq : b=h := by omega
  have deq : d=h := by omega
  omega

theorem escapes {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) : Escape (Envelope (n := n) (Allowed n h)) h :=
  ⟨pair_escape hh residue room,triple_a_escape hh residue room,triple_b_escape hh residue room⟩

theorem compulsory_allowed {n h d : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (member : Compulsory h d) : Allowed n h d ∧ 0 < d := by
  have original := CircleEnvelope.compulsory_allowed hh residue room member
  refine ⟨⟨original.1,?_⟩,original.2⟩
  rcases member with rfl | rfl | rfl | rfl | rfl <;> omega

theorem base_subset {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) : Subgraph (Base (n := n) h) (Envelope (Allowed n h)) := by
  rintro s t ⟨d,member,rfl⟩
  have valid := compulsory_allowed hh residue room member
  exact ⟨Ne.symm (shift_ne_self s valid.2 valid.1.1.1),d,valid.1,rfl⟩

/-- Actual universal delivery for every arbitrary optional subset and every
admissible order, with no divisibility restriction on n. -/
theorem universal {n h : Nat} (hh : 7 ≤ h) (residue : h%4=3)
    (room : 2*h+2 ≤ n) (coprime : Nat.Coprime n h)
    {G : Graph (Fin n)} (lower : Subgraph (Base h) G)
    (upper : Subgraph G (Envelope (Allowed n h))) (t s : Fin n) :
    Universal G t (3*n-1) s :=
  CirclePropagation.universal hh (by omega) coprime lower upper (escapes hh residue room) t s

#print axioms compare_lift
#print axioms escapes
#print axioms universal
end Delivery.CircleGuarded
