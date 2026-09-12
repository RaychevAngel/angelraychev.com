import DeliveryGame

/-!
Final dense-band staircase: numerical implications of explicit cardinality
inequalities, plus complementary-block gluing in actual game semantics.
The graph-to-cardinality obstructions and existence of attaining blocks remain
ordinary proofs. Neither is introduced here as an axiom or hidden premise.
-/
namespace Delivery.DenseCounting

def ceilHalf (r : Nat) : Nat := (r + 1) / 2

/-- The numerical core. Each displayed cardinality inequality is an explicit
hypothesis; its derivation from an arbitrary graph is not formalized here. -/
theorem loss_from_counts {ell a b rho D : Nat}
    (loss : ell + 2*b ≤ D + rho)
    (outside_image : rho + a ≤ ell)
    (distinct_images : rho ≤ a + b)
    (cycle_exclusion : b = 0 → rho + 2 ≤ a) :
    ceilHalf ell + 1 ≤ D := by
  unfold ceilHalf
  by_cases hb : b = 0
  · have hc := cycle_exclusion hb
    omega
  · omega

theorem staircase_from_counts {r ell a b rho D : Nat}
    (degree_count : r ≤ ell)
    (loss : ell + 2*b ≤ D + rho)
    (outside_image : rho + a ≤ ell)
    (distinct_images : rho ≤ a + b)
    (cycle_exclusion : b = 0 → rho + 2 ≤ a) :
    ceilHalf r + 1 ≤ D := by
  have h := loss_from_counts loss outside_image distinct_images cycle_exclusion
  unfold ceilHalf at *
  omega

theorem zero_case_bound {n h r : Nat}
    (hn : 2 ≤ n) (_hr : 1 ≤ r) (hrn : r ≤ n) (band : h + r = 2*n) :
    ceilHalf r + 1 ≤ h := by
  unfold ceilHalf
  omega

/-- Numerical upper bound, with the graph-counting bridge exposed as the
premise counts_if_positive, rather than asserted as a proved theorem. -/
theorem final_band_bound {n h r I D : Nat}
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (band : h + r = 2*n) (partition : I + D = h)
    (counts_if_positive : 0 < I → ∃ ell a b rho : Nat,
      r ≤ ell ∧ ell + 2*b ≤ D + rho ∧ rho + a ≤ ell ∧
      rho ≤ a + b ∧ (b = 0 → rho + 2 ≤ a)) :
    I + ceilHalf r + 1 ≤ h := by
  by_cases hz : I = 0
  · subst I
    simpa only [Nat.zero_add] using zero_case_bound hn hr hrn band
  · obtain ⟨ell,a,b,rho,hdeg,hloss,houtside,himages,hcycle⟩ :=
      counts_if_positive (by omega)
    have hd := staircase_from_counts hdeg hloss houtside himages hcycle
    omega

theorem final_band_bound_subtracted {n h r I D : Nat}
    (hn : 2 ≤ n) (hr : 1 ≤ r) (hrn : r ≤ n)
    (band : h + r = 2*n) (partition : I + D = h)
    (counts_if_positive : 0 < I → ∃ ell a b rho : Nat,
      r ≤ ell ∧ ell + 2*b ≤ D + rho ∧ rho + a ≤ ell ∧
      rho ≤ a + b ∧ (b = 0 → rho + 2 ≤ a)) :
    I ≤ h - ceilHalf r - 1 := by
  have hb := final_band_bound hn hr hrn band partition counts_if_positive
  omega

/-- Block-count identity. Graph existence at k≥52 remains a separate result. -/
theorem attaining_block_count {n r k : Nat}
    (hr : 2 ≤ r) (blocks : n = r + k) :
    (r - 2)/2 + 2*k = 2*n - r - ceilHalf r - 1 := by
  unfold ceilHalf
  omega

theorem attaining_bounds_force_equality {n r k I : Nat}
    (hr : 2 ≤ r) (blocks : n = r + k)
    (lower : (r - 2)/2 + 2*k ≤ I)
    (upper : I ≤ 2*n - r - ceilHalf r - 1) :
    I = 2*n - r - ceilHalf r - 1 := by
  have hc := attaining_block_count hr blocks
  omega

universe u v
variable {V : Type u} {B : Type v}

/-- F records precisely the missing arcs in this loopless complement. -/
def complement (F : Graph V) : Graph V := fun x y => x ≠ y ∧ ¬ F x y

/-- Actual two-move strategy, safe against every intervening pursuer move. -/
theorem safe_intermediate_winning {E : Graph V} {s t c u : V}
    (initial : s ≠ c) (first : E s u) (last : E u t)
    (unreachable : ¬ Legal E c u) : Winning E t 2 s c := by
  have safe : ∀ c', Legal E c c' → u ≠ c' := by
    intro c' hc' heq
    apply unreachable
    simpa only [heq] using hc'
  apply Winning.step initial (Or.inr first)
      (safe c (legal_wait E c)) safe
  intro c' hc'
  exact Winning.finish (safe c' hc') (Or.inr last)

theorem missing_arc_unreachable {F : Graph V} {c u : V}
    (loopless : ∀ x, ¬ F x x) (missing : F c u) :
    ¬ Legal (complement F) c u := by
  intro reachable
  cases reachable with
  | inl heq => subst u; exact loopless c missing
  | inr he => exact he.2 missing

theorem cross_block_arc {F : Graph V} {block : V → B} {x y : V}
    (supported : ∀ v w, F v w → block v = block w)
    (different : block x ≠ block y) : complement F x y := by
  constructor
  · intro h; exact different (congrArg block h)
  · intro h; exact different (supported x y h)

/-- Complementary-block gluing. Same-block pursuers are handled by local
safe two-move witnesses; other pursuers supply a missing outgoing arc in their
own block. No preservation of arbitrary multi-move strategies is asserted. -/
theorem complementary_blocks_two_move {F : Graph V} {block : V → B}
    (loopless : ∀ x, ¬ F x x)
    (supported : ∀ v w, F v w → block v = block w)
    (positive : ∀ c, ∃ u, F c u)
    {s t : V} (same_block : block s = block t)
    (local_witness : ∀ c, block c = block s → c ≠ s →
      ∃ u, complement F s u ∧ complement F u t ∧ F c u) :
    Universal (complement F) t 2 s := by
  intro c hcs
  by_cases hcblock : block c = block s
  · obtain ⟨u,hfirst,hlast,hmissing⟩ := local_witness c hcblock hcs
    exact safe_intermediate_winning (Ne.symm hcs) hfirst hlast
      (missing_arc_unreachable loopless hmissing)
  · obtain ⟨u,hmissing⟩ := positive c
    have hcu := supported c u hmissing
    have hsu : block s ≠ block u := by
      intro h
      exact hcblock (hcu.trans h.symm)
    have hut : block u ≠ block t := by
      intro h
      exact hcblock (hcu.trans (h.trans same_block.symm))
    exact safe_intermediate_winning (Ne.symm hcs)
      (cross_block_arc supported hsu) (cross_block_arc supported hut)
      (missing_arc_unreachable loopless hmissing)

/-- Actual delivery against every legal history-dependent pursuer. -/
theorem complementary_blocks_actual_delivery [DecidableEq V]
    {F : Graph V} {block : V → B}
    (loopless : ∀ x, ¬ F x x)
    (supported : ∀ v w, F v w → block v = block w)
    (positive : ∀ c, ∃ u, F c u)
    {s t c : V} (same_block : block s = block t)
    (local_witness : ∀ p, block p = block s → p ≠ s →
      ∃ u, complement F s u ∧ complement F u t ∧ F p u)
    (initial : c ≠ s) (cop : PursuerPolicy V)
    (legal : LegalPursuer (complement F) cop) (history : History V) :
    play (complement F) t cop 2 history s c = .delivered := by
  exact winning_play_delivers
    (complementary_blocks_two_move loopless supported positive same_block
      local_witness c initial) cop legal history

#print axioms loss_from_counts
#print axioms final_band_bound
#print axioms attaining_block_count
#print axioms complementary_blocks_two_move
#print axioms complementary_blocks_actual_delivery

end Delivery.DenseCounting
