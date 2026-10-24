import FiniteExclusionBoundTreeRows

/-! Boolean reflection for the bitset tree checker. Quantified closure loops
compute Boolean values directly, then one theorem supplies their proof meaning. -/
namespace Delivery.FiniteExclusion.Boolean
open FiniteGame Bounds PrefixBounds FastBounds Bitset BoundTreeRows

def all9 (f : Fin 9 → Bool) : Bool := (List.finRange 9).all f
@[simp] theorem all9_true (f : Fin 9 → Bool) : all9 f = true ↔ ∀ x, f x = true := by
  simp [all9,List.all_eq_true]

def guard (p q : Bool) : Bool := !p || q
@[simp] theorem guard_true (p q : Bool) : guard p q = true ↔ (p = true → q = true) := by
  cases p <;> simp [guard]

def regionCheck (upper lower good : Rows) (t : Fin 9) (mask : Nat) : Bool :=
  all9 (fun c => decide (lower c < 512)) &&
  all9 (fun r => (upper r).testBit r.val) &&
  decide (row mask t = 0) &&
  all9 (fun c => all9 (fun z => guard ((good c).testBit z.val)
    (decide (z ≠ t) && (decide (z = c) || decide (lower c &&& (2^z.val ||| row mask z) ≠ 0))))) &&
  all9 (fun r => all9 (fun c => guard
    (mask.testBit (r.val*9+c.val) && decide (r ≠ c))
    (decide (upper r &&& good c = upper r))))

theorem region_sound (upper lower good : Rows) (t : Fin 9) (mask : Nat)
    (checked : regionCheck upper lower good t mask = true) :
    FastRegionOK upper lower good t mask := by
  simpa only [regionCheck,Bool.and_eq_true,Bool.or_eq_true,all9_true,guard_true,
    decide_eq_true_eq,FastRegionOK,graph,maskRegion,and_imp,and_assoc] using checked

def leafCheck (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (leaf : Leaf) : Bool :=
  decide (∀ w ∈ leaf.sources, SourceOK a p w) &&
  decide (∀ w ∈ leaf.recipients, RecipientOK a p w) &&
  decide (∀ r z, Legal (upperEdge a p) r z → graph (rows leaf.upper) r z) &&
  decide (∀ c z, graph (rows leaf.lower) c z → lowerLegal a p c z) &&
  leaf.losses.all (fun loss => regionCheck (rows leaf.upper) (rows leaf.lower)
    (rows loss.good) loss.target loss.region) &&
  decide (CoverOK a p (rows leaf.allowed) leaf.sources leaf.recipients leaf.masks) &&
  decide (allowedCount (rows leaf.allowed) ≤ bound)

theorem leaf_sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (leaf : Leaf)
    (checked : leafCheck a p bound leaf = true) : UpperPrefix a p bound := by
  simp only [leafCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checked
  apply BoundTreeRows.leaf_sound a p bound leaf
  rcases checked with ⟨⟨⟨⟨⟨⟨hs,hr⟩,hu⟩,hl⟩,hm⟩,hc⟩,hn⟩
  exact ⟨hs,hr,hu,hl,fun loss member => region_sound _ _ _ _ _ (hm loss member),hc,hn⟩

def check (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) : Tree → Bool
  | .invalid => decide (¬PrefixOK a p)
  | .leaf leaf => leafCheck a p bound leaf
  | .camp cert => decide (LocalOK a p bound cert)
  | .branch children => decide (p.length < 9) &&
      all9 (fun v => check a (p++[v]) bound (children v))

theorem sound (a : Assignment 9) (p : List (Fin 9)) (bound : Nat) (tree : Tree)
    (checked : check a p bound tree = true) : UpperPrefix a p bound := by
  induction tree generalizing p with
  | invalid => exact invalid_upper a p bound (of_decide_eq_true checked)
  | leaf certificate => exact leaf_sound a p bound certificate checked
  | camp certificate => exact BoundTreeRows.local_sound a p bound certificate (of_decide_eq_true checked)
  | branch children ih =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq,all9_true] at checked
    exact branch_upper a p bound checked.1 (fun v => ih v (p++[v]) (checked.2 v))

#print axioms region_sound
#print axioms sound
end Delivery.FiniteExclusion.Boolean
