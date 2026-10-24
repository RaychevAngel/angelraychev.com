import SparseSupported

/-! Scalar arithmetic for the sparse parity upper bound, followed by an
induction in the number of original arrows. -/
namespace Delivery.SparseParity
open FiniteGame Extremal DenseCombinatorics SparseSupport SparseSupported
open SparseDeletion

theorem product_deficit (q r u v k : Nat) (hq : q+u=k) (hr : r+v=k) :
    q*r+(u+v)*k=k*k+u*v := by
  have a := congrArg (fun z => q*z) hr
  have b := congrArg (fun z => u*z) hr
  have c := congrArg (fun z => z*k) hq
  have d := congrArg (fun z => z*v) hq
  simp only [Nat.mul_add,Nat.add_mul] at a b c d ⊢
  rw [Nat.mul_comm k v] at d
  omega

/-- Only the final three possible values of each active-set cardinal need
symbolic case analysis; below them the product bound alone suffices. -/
theorem even_scalar (k N q r b e I : Nat) (hk : 5 ≤ k)
    (qk : q ≤ k) (rk : r ≤ k)
    (qN : q ≤ N) (rN : r ≤ N)
    (qcap : N+q ≤ 2*k) (rcap : N+r ≤ 2*k)
    (overlap : q+r ≤ N+b) (arrows : 2*k+q+r ≤ e+2*N)
    (rectangle : I+b+e ≤ q*r) : I+3*k ≤ k*k := by
  by_cases smallq : q+3 ≤ k
  · have product := Nat.mul_le_mul_right k smallq
    have qr := Nat.mul_le_mul_left q rk
    simp only [Nat.add_mul] at product
    omega
  by_cases smallr : r+3 ≤ k
  · have product := Nat.mul_le_mul_left k smallr
    have qr := Nat.mul_le_mul_right r qk
    simp only [Nat.mul_add] at product
    omega
  let u := k-q
  let v := k-r
  have hq : q+u=k := Nat.add_sub_of_le qk
  have hr : r+v=k := Nat.add_sub_of_le rk
  have hu : u=0 ∨ u=1 ∨ u=2 := by dsimp [u]; omega
  have hv : v=0 ∨ v=1 ∨ v=2 := by dsimp [v]; omega
  have product := product_deficit q r u v k hq hr
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    simp only [hu,hv,Nat.zero_add,Nat.add_zero,Nat.zero_mul,Nat.mul_zero,
      Nat.one_mul,Nat.mul_one] at product hq hr <;> omega

theorem odd_scalar (k N q r b e I : Nat) (hk : 5 ≤ k)
    (qk : q ≤ k) (rk : r ≤ k)
    (qN : q ≤ N) (rN : r ≤ N)
    (qcap : N+q ≤ 2*k+1) (rcap : N+r ≤ 2*k+1)
    (overlap : q+r ≤ N+b) (arrows : 2*k+1+q+r ≤ e+2*N)
    (rectangle : I+b+e ≤ q*r) : I+3*k ≤ k*k+2 := by
  by_cases smallq : q+3 ≤ k
  · have product := Nat.mul_le_mul_right k smallq
    have qr := Nat.mul_le_mul_left q rk
    simp only [Nat.add_mul] at product
    omega
  by_cases smallr : r+3 ≤ k
  · have product := Nat.mul_le_mul_left k smallr
    have qr := Nat.mul_le_mul_right r qk
    simp only [Nat.mul_add] at product
    omega
  let u := k-q
  let v := k-r
  have hq : q+u=k := Nat.add_sub_of_le qk
  have hr : r+v=k := Nat.add_sub_of_le rk
  have hu : u=0 ∨ u=1 ∨ u=2 := by dsimp [u]; omega
  have hv : v=0 ∨ v=1 ∨ v=2 := by dsimp [v]; omega
  have product := product_deficit q r u v k hq hr
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
    simp only [hu,hv,Nat.zero_add,Nat.add_zero,Nat.zero_mul,Nat.mul_zero,
      Nat.one_mul,Nat.mul_one] at product hq hr <;> omega

/-- The small branch is deliberately an auxiliary upper envelope, not the
sharp small-budget classification. Its values through nine are
0,0,0,0,1,1,3,3,6,6; these suffice to start the sharp parity induction. -/
def budgetBound (m : Nat) : Nat :=
  if m < 10 then (m/2)*(m/2-1)/2 else (m/2)*(m/2-3)+2*(m%2)

theorem budget_identity (m : Nat) (large : 10 ≤ m) :
    budgetBound m + 3*(m/2) = (m/2)*(m/2)+2*(m%2) := by
  have kLarge : 3 ≤ m/2 := by omega
  have product := Nat.mul_le_mul_left (m/2) kLarge
  rw [budgetBound,if_neg (by omega),Nat.mul_sub]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem small_scalar_table : ∀ m N q r : Fin 10,
    q.val ≤ N.val → r.val ≤ N.val →
    2*q.val ≤ m.val → 2*r.val ≤ m.val →
    N.val+q.val ≤ m.val → N.val+r.val ≤ m.val →
    min (N.val*N.val-N.val-m.val)
      (q.val*r.val-(q.val+r.val-N.val)-(m.val+q.val+r.val-2*N.val)) ≤
      budgetBound m.val := by decide +kernel

/-- Uniform positive-support bound, including all small induction seeds. -/
theorem supported_budget_bound {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (P : Fin n → Prop)
    (outSupport : ∀ s, 1 ≤ outdegree E s ↔ P s)
    (inSupport : ∀ t, 1 ≤ indegree E t ↔ P t) : score E ≤ budgetBound (arcCount E) := by
  have bounds := active_card_bounds E
  have counts := supported_counts E P outSupport inSupport
  have qN := card_mono (P := ActiveOut E) (Q := P)
    (fun x h => (outSupport x).mp (Nat.le_trans (by decide) h))
  have rN := card_mono (P := ActiveIn E) (Q := P)
    (fun x h => (inSupport x).mp (Nat.le_trans (by decide) h))
  have rectangle := eligible_rectangle E loopless
  have overlap := card_overlap_in P (ActiveOut E) (ActiveIn E)
    (fun x h => (outSupport x).mp (Nat.le_trans (by decide) h))
    (fun x h => (inSupport x).mp (Nat.le_trans (by decide) h))
  by_cases small : arcCount E < 10
  · have square := supported_pair_bound E loopless P outSupport inSupport
    have bound := supported_bound E loopless P outSupport inSupport
    have table := small_scalar_table ⟨arcCount E,small⟩ ⟨card P,by omega⟩
      ⟨card (ActiveOut E),by omega⟩ ⟨card (ActiveIn E),by omega⟩
      qN rN bounds.1 bounds.2 counts.1 counts.2.1
    simp only at table
    omega
  · let k := arcCount E/2
    have hk : 5 ≤ k := by dsimp [k]; omega
    have qk : card (ActiveOut E) ≤ k := by dsimp [k]; omega
    have rk : card (ActiveIn E) ≤ k := by dsimp [k]; omega
    have identity := budget_identity (arcCount E) (by omega)
    change budgetBound (arcCount E)+3*k = k*k+2*(arcCount E%2) at identity
    have parity : arcCount E=2*k ∨ arcCount E=2*k+1 := by dsimp [k]; omega
    rcases parity with even | odd
    · have upper := even_scalar k (card P) (card (ActiveOut E)) (card (ActiveIn E))
        (card (fun x => ActiveOut E x ∧ ActiveIn E x))
        (cut E (ActiveOut E) (ActiveIn E)) (score E) hk qk rk qN rN
        (by omega) (by omega) overlap (by omega) rectangle
      have remainder : arcCount E%2=0 := by omega
      rw [remainder] at identity
      omega

    · have upper := odd_scalar k (card P) (card (ActiveOut E)) (card (ActiveIn E))
        (card (fun x => ActiveOut E x ∧ ActiveIn E x))
        (cut E (ActiveOut E) (ActiveIn E)) (score E) hk qk rk qN rN
        (by omega) (by omega) overlap (by omega) rectangle
      have remainder : arcCount E%2=1 := by omega
      rw [remainder] at identity
      omega

private theorem small_step : ∀ m : Fin 10, budgetBound m.val ≤ budgetBound (m.val+1) :=
  by decide +kernel

theorem budget_step (m : Nat) : budgetBound m ≤ budgetBound (m+1) := by
  by_cases small : m<10
  · exact small_step ⟨m,small⟩
  have old := budget_identity m (by omega)
  have new := budget_identity (m+1) (by omega)
  by_cases even : m%2=0
  · have quotient : (m+1)/2=m/2 := by omega
    have remainder : (m+1)%2=1 := by omega
    rw [quotient,remainder] at new
    rw [even] at old
    omega
  · have remainder : m%2=1 := by omega
    have quotient : (m+1)/2=m/2+1 := by omega
    have next : (m+1)%2=0 := by omega
    rw [quotient,next] at new
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul] at new
    rw [remainder] at old
    omega

theorem budget_mono {a b : Nat} (order : a ≤ b) : budgetBound a ≤ budgetBound b := by
  induction b generalizing a with
  | zero =>
      have same : a=0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases same : a=b+1
      · subst a; exact Nat.le_refl _
      · exact Nat.le_trans (ih (by omega)) (budget_step b)

private theorem small_two_step : ∀ m : Fin 12, 2 ≤ m.val →
    budgetBound (m.val-2)+(m.val-2)/2 ≤ budgetBound m.val := by decide +kernel

theorem budget_two_step (m : Nat) (large : 2 ≤ m) :
    budgetBound (m-2)+(m-2)/2 ≤ budgetBound m := by
  by_cases small : m<12
  · exact small_two_step ⟨m,small⟩ large
  have old := budget_identity (m-2) (by omega)
  have new := budget_identity m (by omega)
  have quotient : m/2=(m-2)/2+1 := by omega
  have remainder : m%2=(m-2)%2 := by omega
  rw [quotient,remainder] at new
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul] at new
  omega

theorem budget_deletion {t m : Nat} (gap : t+2 ≤ m) :
    budgetBound t+t/2 ≤ budgetBound m := by
  have monotone := budget_mono (a := t) (b := m-2) (by omega)
  have final := budget_two_step m (by omega)
  omega

/-- An unconditional upper bound on the actual game for every loopless finite
digraph. The induction deletes a nonisolated source or sink; otherwise the
support-cardinality argument applies directly, with isolates still present. -/
theorem upper {n : Nat} (E : Graph (Fin n)) (loopless : Loopless E) :
    score E ≤ budgetBound (arcCount E) := by
  have all : ∀ m n (E : Graph (Fin n)), Loopless E → arcCount E=m →
      score E ≤ budgetBound m := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
        intro n E loopless budget
        by_cases hasSource : ∃ v, (∀ x, ¬ E x v) ∧ ∃ x, E v x
        · obtain ⟨v,source,hasEdge⟩ := hasSource
          have degree : 0 < outdegree E v := card_positive.mpr hasEdge
          have deletion := source_deletion E loopless v source
          have old := ih (arcCount (isolate E v)) (by omega) n (isolate E v)
            (isolate_loopless loopless v) rfl
          by_cases small : outdegree E v ≤ 1
          · have monotone := budget_mono (a := arcCount (isolate E v)) (b := m) (by omega)
            have preserved := deletion.2.2.2 small
            omega
          · have bounded := budget_deletion (t := arcCount (isolate E v)) (m := m) (by omega)
            omega
        by_cases hasSink : ∃ v, (∀ x, ¬ E v x) ∧ ∃ x, E x v
        · obtain ⟨v,sink,hasEdge⟩ := hasSink
          have degree : 0 < indegree E v := card_positive.mpr hasEdge
          have deletion := sink_deletion E loopless v sink
          have old := ih (arcCount (isolate E v)) (by omega) n (isolate E v)
            (isolate_loopless loopless v) rfl
          by_cases small : indegree E v ≤ 1
          · have monotone := budget_mono (a := arcCount (isolate E v)) (b := m) (by omega)
            have preserved := deletion.2.2.2 small
            omega
          · have bounded := budget_deletion (t := arcCount (isolate E v)) (m := m) (by omega)
            omega
        have support := support_equivalences E
          (fun x source y edge => hasSource ⟨x,source,y,edge⟩)
          (fun x sink y edge => hasSink ⟨x,sink,y,edge⟩)
        have bounded := supported_budget_bound E loopless (fun x => 1 ≤ outdegree E x)
          (fun _ => Iff.rfl) support
        simpa only [budget] using bounded
  exact all (arcCount E) n E loopless rfl

theorem even_upper {n k : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (hk : 5 ≤ k) (budget : arcCount E=2*k) : score E ≤ k*(k-3) := by
  have bound := upper E loopless
  rw [budget,budgetBound,if_neg (by omega)] at bound
  have quotient : 2*k/2=k := by omega
  have remainder : 2*k%2=0 := by omega
  simpa only [quotient,remainder,Nat.mul_zero,Nat.add_zero] using bound

theorem odd_upper {n k : Nat} (E : Graph (Fin n)) (loopless : Loopless E)
    (hk : 5 ≤ k) (budget : arcCount E=2*k+1) : score E ≤ k*(k-3)+2 := by
  have bound := upper E loopless
  rw [budget,budgetBound,if_neg (by omega)] at bound
  have quotient : (2*k+1)/2=k := by omega
  have remainder : (2*k+1)%2=1 := by omega
  simpa only [quotient,remainder,Nat.mul_one] using bound

#print axioms even_scalar
#print axioms odd_scalar
#print axioms supported_budget_bound
#print axioms upper
#print axioms even_upper
#print axioms odd_upper
end Delivery.SparseParity
