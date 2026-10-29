import StrategyCompression

/-!
Complement-dual compression and the joining inspection of two histories.

The graph is finite and undirected. A supplied compression must already be
monotone, cardinality preserving, and neighborhood-subcommuting. This module
constructs its complement dual and proves that applying the two operators at
the same cut cannot increase the intersection of the endpoint envelopes.
It also proves the reversed compatibility of two time-dependent operators.

These are abstract proof tools. No rectangle compression operator, boundary
arrival theorem, capture-time formula, or uniform gap bound is assumed or
established here. The actual-walk corollary uses the existing strategy theorem.
-/

namespace Princess.PairedCompression

open Princess.CaptureRecurrence Princess.LadderCardinality
open Princess.StrategyCompression

def complement {V : Type} (A : Region V) : Region V := fun x => ¬ A x

def dualMap {V : Type} (C : Region V → Region V) (A : Region V) : Region V :=
  complement (C (complement A))

theorem complement_involutive {V : Type} (A : Region V) :
    complement (complement A) = A := by
  classical
  funext x
  apply propext
  constructor
  · intro h
    exact Classical.byContradiction h
  · intro h hn
    exact hn h

theorem complement_card {n : Nat} (A : Board n) :
    card (complement A) = n - card A := by
  have h := cardOn_split (List.finRange n) (fun _ => True) A
  have full : card (fun _ : Fin n => True) = n :=
    (card_full_iff _).mpr (fun _ => True.intro)
  have first : cardOn (List.finRange n) (fun x => True ∧ A x) = card A := by
    apply cardOn_congr
    intro _ _
    simp
  have second : cardOn (List.finRange n) (fun x => True ∧ ¬ A x) =
      card (complement A) := by
    apply cardOn_congr
    intro _ _
    simp [complement]
  change card (fun _ : Fin n => True) = _ at h
  rw [full, first, second] at h
  omega

theorem dual_mono {V : Type} (C : Region V → Region V)
    (mono : ∀ A B, Subset A B → Subset (C A) (C B))
    (A B : Region V) (h : Subset A B) :
    Subset (dualMap C A) (dualMap C B) := by
  intro x hx hb
  apply hx
  exact mono (complement B) (complement A) (fun y hy ha => hy (h y ha)) x hb

theorem dual_size {n : Nat} (C : Board n → Board n)
    (size : ∀ A, card (C A) = card A) (A : Board n) :
    card (dualMap C A) = card A := by
  change card (complement (C (complement A))) = card A
  rw [complement_card, size, complement_card]
  have bound := card_le A
  omega

/-- The indices reverse: `N C₀ ⊆ C₁ N` gives `N C₁† ⊆ C₀† N`.
Compatibility is assumed for every set, including the complement-neighborhood
input used in this proof; endpoint compatibility alone would not suffice. -/
theorem reversed_compatibility {V : Type} (adj : V → V → Prop)
    (symmetric : ∀ u v, adj u v → adj v u)
    (C₀ C₁ : Region V → Region V)
    (mono₁ : ∀ A B, Subset A B → Subset (C₁ A) (C₁ B))
    (compatible : ∀ A, Subset (move adj (C₀ A)) (C₁ (move adj A)))
    (A : Region V) :
    Subset (move adj (dualMap C₁ A)) (dualMap C₀ (move adj A)) := by
  intro v hv bad
  obtain ⟨u, hu, edge⟩ := hv
  apply hu
  have outside : Subset (move adj (complement (move adj A))) (complement A) := by
    intro x hx ha
    obtain ⟨y, hy, hyx⟩ := hx
    exact hy ⟨x, ha, symmetric y x hyx⟩
  exact mono₁ _ _ outside u
    (compatible (complement (move adj A)) u ⟨v, bad, symmetric u v edge⟩)

/-- A valid compression supplies a valid complement-dual compression. -/
def dual {n : Nat} {adj : Fin n → Fin n → Prop}
    (symmetric : ∀ u v, adj u v → adj v u) (C : Compression adj) :
    Compression adj where
  map := dualMap C.map
  mono := dual_mono C.map C.mono
  size := dual_size C.map C.size
  neighbors := reversed_compatibility adj symmetric C.map C.map C.mono C.neighbors

theorem dual_idempotent {V : Type} (C : Region V → Region V)
    (idem : ∀ A, C (C A) = C A) (A : Region V) :
    dualMap C (dualMap C A) = dualMap C A := by
  unfold dualMap
  rw [complement_involutive, idem]

/-- Opposite compression cannot increase the number of cells that a joining
inspection must cover. Both endpoints use the same supplied operator. -/
theorem overlap_contracts {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (F R : Board n) :
    card (fun x => C.map F x ∧ dualMap C.map R x) ≤
      card (fun x => F x ∧ R x) := by
  let S : Board n := fun x => F x ∧ R x
  have reduced := reduced_probe_bound C F (C.map F) S (fun _ h => h)
  have inc : Subset (fun x => F x ∧ ¬ S x) (complement R) := by
    intro x hx hr
    exact hx.2 ⟨hx.1, hr⟩
  have bound := card_mono
    (fun x => C.map F x ∧ dualMap C.map R x)
    (fun x => C.map F x ∧ ¬ C.map (fun y => F y ∧ ¬ S y) x)
    (fun x hx => ⟨hx.1, fun h => hx.2 (C.mono _ _ inc x h)⟩)
  exact Nat.le_trans bound reduced

/-- Actual transformed endpoints may be proper subsets of their envelopes. -/
theorem endpoint_overlap_contracts {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (F R F' R' : Board n)
    (forward : Subset F' (C.map F))
    (reverse : Subset R' (dualMap C.map R)) :
    card (fun x => F' x ∧ R' x) ≤ card (fun x => F x ∧ R x) := by
  exact Nat.le_trans
    (card_mono _ _ (fun x hx => ⟨forward x hx.1, reverse x hx.2⟩))
    (overlap_contracts C F R)

/-- The transformed belief is defined from the actual original history.
At each round it removes precisely the cells outside the compressed original
survivor set, then makes the mandatory move. No endpoint search is used. -/
def compressedBelief {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (initial : Board n) (probes : Nat → Board n) :
    Nat → Board n
  | 0 => C.map initial
  | t + 1 =>
      let B := compressedBelief C initial probes t
      next adj B (fun x => B x ∧
        ¬ C.map (fun y => possible adj initial probes t y ∧ ¬ probes t y) x)

def compressedProbes {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (initial : Board n) (probes : Nat → Board n)
    (t : Nat) : Board n :=
  fun x => compressedBelief C initial probes t x ∧
    ¬ C.map (fun y => possible adj initial probes t y ∧ ¬ probes t y) x

/-- The constructed trace is an actual belief history, with inspections before
each compulsory move in the same convention as `Reachable`. -/
theorem compressedBelief_is_possible {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (initial : Board n) (probes : Nat → Board n)
    (t : Nat) :
    compressedBelief C initial probes t =
      possible adj (C.map initial) (compressedProbes C initial probes) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change next adj (compressedBelief C initial probes t)
        (compressedProbes C initial probes t) =
        next adj (possible adj (C.map initial) (compressedProbes C initial probes) t)
          (compressedProbes C initial probes t)
      rw [ih]

theorem compressedBelief_envelope {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (initial : Board n) (probes : Nat → Board n)
    (t : Nat) :
    Subset (compressedBelief C initial probes t)
      (C.map (possible adj initial probes t)) := by
  cases t with
  | zero => exact fun _ h => h
  | succ t =>
      exact reduced_step C (possible adj initial probes t)
        (compressedBelief C initial probes t) (probes t)

/-- Every daily quota is individually respected, including zero quotas. -/
theorem compressedProbes_card_le {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) (initial : Board n) (probes : Nat → Board n)
    (t : Nat) : card (compressedProbes C initial probes t) ≤ card (probes t) :=
  reduced_probe_bound C (possible adj initial probes t)
    (compressedBelief C initial probes t) (probes t)
    (compressedBelief_envelope C initial probes t)

/-- Two actual prefixes may have different lengths. Compress them oppositely;
their actual endpoint intersection cannot increase. The same operator and its
complement dual are required at the joining cut. -/
theorem paired_actual_prefix_overlap {n : Nat} {adj : Fin n → Fin n → Prop}
    (symmetric : ∀ u v, adj u v → adj v u) (C : Compression adj)
    (forwardInitial reverseInitial : Board n)
    (forwardProbes reverseProbes : Nat → Board n) (s t : Nat) :
    card (fun x =>
      possible adj (C.map forwardInitial)
        (compressedProbes C forwardInitial forwardProbes) s x ∧
      possible adj ((dual symmetric C).map reverseInitial)
        (compressedProbes (dual symmetric C) reverseInitial reverseProbes) t x) ≤
    card (fun x => possible adj forwardInitial forwardProbes s x ∧
      possible adj reverseInitial reverseProbes t x) := by
  rw [← compressedBelief_is_possible, ← compressedBelief_is_possible]
  exact endpoint_overlap_contracts C _ _ _ _
    (compressedBelief_envelope C forwardInitial forwardProbes s)
    (compressedBelief_envelope (dual symmetric C) reverseInitial reverseProbes t)

/-- Consequently an allowed joining inspection remains allowed. Together with
`compressedProbes_card_le`, all prefix quotas and the joining quota are kept. -/
theorem paired_actual_prefix_join_budget {n : Nat} {adj : Fin n → Fin n → Prop}
    (symmetric : ∀ u v, adj u v → adj v u) (C : Compression adj)
    (forwardInitial reverseInitial : Board n)
    (forwardProbes reverseProbes : Nat → Board n) (s t k : Nat)
    (budget : card (fun x => possible adj forwardInitial forwardProbes s x ∧
      possible adj reverseInitial reverseProbes t x) ≤ k) :
    card (fun x =>
      possible adj (C.map forwardInitial)
        (compressedProbes C forwardInitial forwardProbes) s x ∧
      possible adj ((dual symmetric C).map reverseInitial)
        (compressedProbes (dual symmetric C) reverseInitial reverseProbes) t x) ≤ k :=
  Nat.le_trans (paired_actual_prefix_overlap symmetric C forwardInitial
    reverseInitial forwardProbes reverseProbes s t) budget

theorem compression_preserves_full {n : Nat} {adj : Fin n → Fin n → Prop}
    (C : Compression adj) : C.map (fun _ => True) = (fun _ => True) :=
  subset_equal _ _ (fun _ _ => True.intro) (C.size _)

/-- In particular, both transformed prefixes retain full initial uncertainty.
This removes any implicit initial-set assumption in the rectangle use case. -/
theorem paired_full_origin_overlap {n : Nat} {adj : Fin n → Fin n → Prop}
    (symmetric : ∀ u v, adj u v → adj v u) (C : Compression adj)
    (forwardProbes reverseProbes : Nat → Board n) (s t : Nat) :
    card (fun x =>
      possible adj (fun _ => True)
        (compressedProbes C (fun _ => True) forwardProbes) s x ∧
      possible adj (fun _ => True)
        (compressedProbes (dual symmetric C) (fun _ => True) reverseProbes) t x) ≤
    card (fun x => possible adj (fun _ => True) forwardProbes s x ∧
      possible adj (fun _ => True) reverseProbes t x) := by
  have h := paired_actual_prefix_overlap symmetric C (fun _ => True)
    (fun _ => True) forwardProbes reverseProbes s t
  rw [compression_preserves_full C, compression_preserves_full (dual symmetric C)] at h
  exact h

/-- The dual preserves existence of a winning continuation with the entire
original budget word, not merely its sum. -/
theorem dual_preserves_budget_word {n : Nat} {adj : Fin n → Fin n → Prop}
    (symmetric : ∀ u v, adj u v → adj v u) (C : Compression adj)
    (budgets : List Nat) (A B : Board n)
    (inc : Subset B (dualMap C.map A))
    (h : wins adj budgets A) : wins adj budgets B :=
  wins_compressed (dual symmetric C) budgets A B inc h

/-- Physical actual-walk interpretation of the dual fixed normal form. -/
theorem dual_fixed_iff_actual_capture {n : Nat} (adj : Fin n → Fin n → Prop)
    (symmetric : ∀ u v, adj u v → adj v u)
    (noDeadEnds : ∀ v, ∃ w, adj v w) (C : Compression adj)
    (idem : ∀ A, C.map (C.map A) = C.map A) (m t : Nat)
    (A : Board n) (hA : Fixed (dual symmetric C) A) :
    fixedWins adj (dual symmetric C) (List.replicate (t + 1) m) A ↔
      ∃ probes : Nat → Board n,
        (∀ i, i < t + 1 → card (probes i) ≤ m) ∧ GuaranteesAt adj A probes t :=
  fixed_iff_actual_capture adj noDeadEnds (dual symmetric C)
    (dual_idempotent C.map idem) m t A hA

end Princess.PairedCompression

#print axioms Princess.PairedCompression.reversed_compatibility
#print axioms Princess.PairedCompression.dual
#print axioms Princess.PairedCompression.overlap_contracts
#print axioms Princess.PairedCompression.endpoint_overlap_contracts
#print axioms Princess.PairedCompression.compressedBelief_is_possible
#print axioms Princess.PairedCompression.compressedProbes_card_le
#print axioms Princess.PairedCompression.paired_actual_prefix_overlap
#print axioms Princess.PairedCompression.paired_actual_prefix_join_budget
#print axioms Princess.PairedCompression.paired_full_origin_overlap
#print axioms Princess.PairedCompression.dual_preserves_budget_word
#print axioms Princess.PairedCompression.dual_fixed_iff_actual_capture
