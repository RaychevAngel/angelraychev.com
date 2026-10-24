import CircleConstruction

/-! The three-offset circle and its protected-pair propagation. The envelope
may be nonsymmetric; only the three prescribed pairs of moves are protected. -/
namespace Delivery.ProtectedCircle
open CyclicArithmetic RobustTwoMove CirclePropagation CircleEnvelope

def Core (a d : Nat) : Prop := d=1 ∨ d=a ∨ d=2*a+1

def Base {n : Nat} (a : Nat) (s t : Fin n) : Prop :=
  ∃ d, Core a d ∧ t=shift s d

def Protected (n a : Nat) (A : Nat → Prop) : Prop :=
  ∀ u v, Core a u → Core a v → u≠v → ∀ x y, A x → A y →
    (u+y)%n=(v+x)%n → x=u ∧ y=v

def Initial (a d : Nat) : Prop := d=0 ∨ Core a d

def Pattern {n : Nat} (G : Graph (Fin n)) (t : Fin n) (K : Nat) (w : Fin n) (a : Nat) : Prop :=
  Universal G t K w ∧ Universal G t K (shift w 1) ∧
    Universal G t K (shift w a) ∧ Universal G t K (shift w (a+1))

theorem base_move {n : Nat} (s : Fin n) {a d : Nat} (member : Core a d) :
    Base a s (shift s d) := ⟨d,member,rfl⟩

theorem protected_escape {n a : Nat} {A : Nat → Prop} (zero : A 0)
    (protection : Protected n a A) {u v : Nat} (cu : Core a u) (cv : Core a v)
    (different : u≠v) (s c : Fin n) (initial : c≠s) :
    ¬ (Legal (Envelope A) c (shift s u) ∧ Legal (Envelope A) c (shift s v)) := by
  rintro ⟨hu,hv⟩
  obtain ⟨x,hx,ex⟩ := legal_offset zero hu
  obtain ⟨y,hy,ey⟩ := legal_offset zero hv
  have same := compare_offsets s c ex ey
  obtain ⟨rfl,rfl⟩ := protection u v cu cv different x y hx hy same
  exact initial (shift_injective ex)

theorem initial_protected {n a : Nat} (large : 3≤a) (room : 2*(2*a+1)<n) :
    Protected n a (Initial a) := by
  intro u v hu hv different x y hx hy same
  have ub : u≤2*a+1 := by rcases hu with rfl | rfl | rfl <;> omega
  have vb : v≤2*a+1 := by rcases hv with rfl | rfl | rfl <;> omega
  have xb : x≤2*a+1 := by rcases hx with rfl | rfl | rfl | rfl <;> omega
  have yb : y≤2*a+1 := by rcases hy with rfl | rfl | rfl | rfl <;> omega
  rw [Nat.mod_eq_of_lt (by omega : u+y<n),Nat.mod_eq_of_lt (by omega : v+x<n)] at same
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;> omega

variable {n a : Nat} {G E : Graph (Fin n)}

/-- Each pair of distinct core successors is protected against the full cop envelope. -/
def Escape (E : Graph (Fin n)) (a : Nat) : Prop :=
  ∀ u v, Core a u → Core a v → u≠v → ∀ s c, c≠s →
    ¬ (Legal E c (shift s u) ∧ Legal E c (shift s v))

theorem pattern_step (large : 3≤a) (room : 2*a+1≤n)
    (lower : Subgraph (Base a) G) (upper : Subgraph G E) (escapes : Escape E a)
    {t w : Fin n} {K : Nat} (wins : Pattern G t K w a) :
    Pattern G t (K+3) (retreat w (2*a+1)) a := by
  have c1 : Core a 1 := Or.inl rfl
  have ca : Core a a := Or.inr (Or.inl rfl)
  have ch : Core a (2*a+1) := Or.inr (Or.inr rfl)
  let v := retreat w (2*a+1)
  have last : Universal G t (K+1) (shift v (a+1)) := by
    apply two_successors lower upper (base_move _ ca) (base_move _ ch)
      (escapes a (2*a+1) ca ch (by omega) (shift v (a+1)))
    · simpa only [v,retreat_offsets w room (show a+1+a=(2*a+1)+0 by omega),shift_zero] using wins.1
    · simpa only [v,retreat_offsets w room (show a+1+(2*a+1)=(2*a+1)+(a+1) by omega)] using wins.2.2.2
  have middleA : Universal G t (K+2) (shift v a) := by
    apply two_successors lower upper (base_move _ c1) (base_move _ ch)
      (escapes 1 (2*a+1) c1 ch (by omega) (shift v a))
    · simpa only [shift_add] using last
    · apply universal_mono (k := K) ?_ (by omega)
      simpa only [v,retreat_offsets w room (show a+(2*a+1)=(2*a+1)+a by omega)] using wins.2.2.1
  have middle1 : Universal G t (K+2) (shift v 1) := by
    apply two_successors lower upper (base_move _ ca) (base_move _ ch)
      (escapes a (2*a+1) ca ch (by omega) (shift v 1))
    · simpa only [shift_add,Nat.add_comm 1 a] using last
    · apply universal_mono (k := K) ?_ (by omega)
      simpa only [v,retreat_offsets w room (show 1+(2*a+1)=(2*a+1)+1 by omega)] using wins.2.1
  have first : Universal G t (K+3) v := by
    apply two_successors lower upper (base_move _ c1) (base_move _ ch)
      (escapes 1 (2*a+1) c1 ch (by omega) v)
    · exact middle1
    · apply universal_mono (k := K) ?_ (by omega)
      simpa only [v,retreat_cancel w room] using wins.1
  exact ⟨first,universal_mono middle1 (by omega),universal_mono middleA (by omega),
    universal_mono last (by omega)⟩

theorem initial_pattern (large : 3≤a) (room : a+1≤n)
    (lower : Subgraph (Base a) G) (upper : Subgraph G E) (escapes : Escape E a)
    (t : Fin n) : Pattern G t 2 (retreat t (a+1)) a := by
  have c1 : Core a 1 := Or.inl rfl
  have ca : Core a a := Or.inr (Or.inl rfl)
  let w := retreat t (a+1)
  have direct1 : Universal G t 1 (shift w 1) := by
    have arrow := lower _ _ (base_move (shift w 1) ca)
    simpa only [w,retreat_offsets t room (show 1+a=(a+1)+0 by omega),shift_zero] using universal_direct arrow
  have directA : Universal G t 1 (shift w a) := by
    have arrow := lower _ _ (base_move (shift w a) c1)
    simpa only [w,retreat_offsets t room (show a+1=(a+1)+0 by omega),shift_zero] using universal_direct arrow
  have first : Universal G t 2 w := two_successors lower upper (base_move w c1) (base_move w ca)
    (escapes 1 a c1 ca (by omega) w) direct1 directA
  have last : Universal G t 0 (shift w (a+1)) := by
    simpa only [w,retreat_cancel t room] using universal_target (E := G) t 0
  exact ⟨first,universal_mono direct1 (by omega),universal_mono directA (by omega),
    universal_mono last (by omega)⟩

theorem iterated_pattern (large : 3≤a) (room : 2*a+1≤n)
    (lower : Subgraph (Base a) G) (upper : Subgraph G E) (escapes : Escape E a)
    (t : Fin n) (j : Nat) :
    Pattern G t (2+3*j) (shift (retreat t (a+1)) (j*(n-(2*a+1)))) a := by
  induction j with
  | zero => simpa using initial_pattern large (by omega) lower upper escapes t
  | succ j ih =>
    have step := pattern_step large room lower upper escapes ih
    have rankEq : 2+3*(j+1)=(2+3*j)+3 := by omega
    have advance : (j+1)*(n-(2*a+1))=j*(n-(2*a+1))+(n-(2*a+1)) := Nat.succ_mul _ _
    rw [rankEq,advance]
    simpa only [retreat,shift_add,Nat.add_assoc] using step

theorem universal (large : 3≤a) (room : 2*a+1≤n) (coprime : Nat.Coprime n (2*a+1))
    (lower : Subgraph (Base a) G) (upper : Subgraph G E) (escapes : Escape E a)
    (t s : Fin n) : Universal G t (3*n-1) s := by
  obtain ⟨j,atSource⟩ := CyclicOrbit.retreat_orbit coprime room (retreat t (a+1)) s
  have win := (iterated_pattern large room lower upper escapes t j.val).1
  rw [atSource] at win
  exact universal_mono win (by have := j.isLt; omega)

/-- Concrete protected-offset envelope: all actual game ranks are derived. -/
theorem envelope_universal {A : Nat → Prop} (large : 3≤a) (room : 2*a+1≤n)
    (coprime : Nat.Coprime n (2*a+1)) (zero : A 0) (protection : Protected n a A)
    (lower : Subgraph (Base a) G) (upper : Subgraph G (Envelope A)) (t s : Fin n) :
    Universal G t (3*n-1) s :=
  universal large room coprime lower upper (fun _ _ => protected_escape zero protection) t s

#print axioms initial_protected
#print axioms envelope_universal
end Delivery.ProtectedCircle
