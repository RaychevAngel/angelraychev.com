import RowPrefixTree

/-! A small reflected front end for order ten. The semantic row-prefix kernel
is arbitrary-order; these literal finite quantifiers reduce replay overhead. -/
namespace Delivery.RowPrefix.Boolean
open FiniteGame

def all10 (f : Fin 10 → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6 && f 7 && f 8 && f 9

theorem all10_true (f : Fin 10 → Bool) : all10 f = true ↔ ∀ x, f x = true := by
  simp only [all10,Bool.and_eq_true]
  constructor
  · intro h ⟨x,hx⟩
    have cases : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨
      x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 ∨ x = 9 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩,h 4⟩,h 5⟩,h 6⟩,h 7⟩,h 8⟩,h 9⟩

def prefixCheck (D R : Fin 10 → Nat) (p : List Nat) : Bool :=
  all10 (fun s => decide (∀ h : s.val < p.length,
    ¬ bit p[s.val] s ∧ rowCount 10 p[s.val] = D s)) &&
  all10 (fun t => decide (
    ((List.finRange 10).filter fun s => decide (known p s t)).length ≤ R t ∧
    R t ≤ ((List.finRange 10).filter fun s => decide (possible p s t)).length))

theorem prefixCheck_true (D R : Fin 10 → Nat) (p : List Nat) :
    prefixCheck D R p = true ↔ PrefixOK D R p := by
  simp only [prefixCheck,Bool.and_eq_true,all10_true,decide_eq_true_eq,PrefixOK]

def mapCheck (D R : Fin 10 → Nat) (p q : List Nat) (f : Fin 10 → Fin 10) : Bool :=
  all10 (fun x => decide (f (f x) = x)) &&
  all10 (fun x => decide (D (f x) = D x ∧ R (f x) = R x)) &&
  decide (p.length = q.length) &&
  all10 (fun s => decide (s.val < p.length → f s = s)) &&
  all10 (fun s => if hp : s.val < p.length then
    if hq : s.val < q.length then all10 (fun t => decide (bit p[s.val] t ↔ bit q[s.val] (f t)))
    else true else true)

theorem mapCheck_true (D R : Fin 10 → Nat) (p q : List Nat) (f : Fin 10 → Fin 10) :
    mapCheck D R p q f = true ↔ MapOK D R p q f := by
  simp only [mapCheck,Bool.and_eq_true,all10_true,decide_eq_true_eq,MapOK]
  constructor
  · rintro ⟨⟨⟨⟨inv,degree⟩,length⟩,fixed⟩,bits⟩
    refine ⟨inv,degree,length,fixed,?_⟩
    intro s hp hq t
    have bitCheck := bits s
    rw [dif_pos hp,dif_pos hq] at bitCheck
    exact of_decide_eq_true ((all10_true _).mp bitCheck t)
  · rintro ⟨inv,degree,length,fixed,bits⟩
    refine ⟨⟨⟨⟨inv,degree⟩,length⟩,fixed⟩,?_⟩
    intro s
    split
    next hp =>
      split
      next hq => exact (all10_true _).mpr (fun t => decide_eq_true (bits s hp hq t))
      next => rfl
    next => rfl

def routesCheck (D R : Fin 10 → Nat) (p : List Nat)
    (rows representatives : List Nat) (route : Route 10) : Bool :=
  rows.all fun mask => !prefixCheck D R (p++[mask]) ||
    (decide ((route mask).1 ∈ representatives) &&
      mapCheck D R (p++[mask]) (p++[(route mask).1]) (route mask).2)

theorem routesCheck_true (D R : Fin 10 → Nat) (p : List Nat)
    (rows representatives : List Nat) (route : Route 10) :
    routesCheck D R p rows representatives route = true ↔ RoutesOK D R p rows representatives route := by
  simp only [routesCheck,List.all_eq_true,Bool.or_eq_true,Bool.and_eq_true,
    Bool.not_eq_true',Bool.eq_false_iff,ne_eq,prefixCheck_true,mapCheck_true,
    decide_eq_true_eq,RoutesOK]

def envelopeCheck (R : Fin 10 → Nat) (p : List Nat) (upper lower : Rows 10) : Bool :=
  all10 (fun r => all10 (fun z => decide (Legal (upperEdge R p) r z → bit (upper r) z))) &&
  all10 (fun c => all10 (fun z => decide (bit (lower c) z → c = z ∨ known p c z)))

theorem envelopeCheck_true (R : Fin 10 → Nat) (p : List Nat) (upper lower : Rows 10) :
    envelopeCheck R p upper lower = true ↔ EnvelopeOK R p upper lower := by
  simp only [envelopeCheck,Bool.and_eq_true,all10_true,decide_eq_true_eq,EnvelopeOK]

def regionCheck (upper lower good region : Rows 10) (t : Fin 10) : Bool :=
  all10 (fun c => decide (lower c < 1024)) && decide (region t = 0) &&
  all10 (fun c => all10 (fun z => decide (bit (good c) z → z ≠ t ∧
    (z = c ∨ lower c &&& (2^z.val ||| region z) ≠ 0)))) &&
  all10 (fun r => all10 (fun c => decide (bit (region r) c → r ≠ c → upper r &&& good c = upper r)))

theorem regionCheck_true (upper lower good region : Rows 10) (t : Fin 10) :
    regionCheck upper lower good region t = true ↔ RegionOK upper lower good region t := by
  simp only [regionCheck,Bool.and_eq_true,all10_true,decide_eq_true_eq,RegionOK]
  simp only [and_assoc,show (2^10 : Nat) = 1024 from rfl]

def coverCheck (D R : Fin 10 → Nat) (p : List Nat) (allowed : Rows 10) (losses : List (Loss 10)) : Bool :=
  all10 (fun s => all10 (fun t => decide (bit (allowed s) t ∨ D s < 2 ∨ R t < 2 ∨
    s = t ∨ known p s t ∨ LossExists losses s t)))

theorem coverCheck_true (D R : Fin 10 → Nat) (p : List Nat)
    (allowed : Rows 10) (losses : List (Loss 10)) :
    coverCheck D R p allowed losses = true ↔ CoverOK D R p allowed losses := by
  simp only [coverCheck,all10_true,decide_eq_true_eq,CoverOK]

def boundCheck (D R : Fin 10 → Nat) (p : List Nat) (bound : Nat) (cert : Bound 10) : Bool :=
  envelopeCheck R p cert.upper cert.lower &&
  cert.losses.all (fun loss => regionCheck cert.upper cert.lower loss.good loss.region loss.target) &&
  coverCheck D R p cert.allowed cert.losses && decide (allowedCount cert.allowed ≤ bound)

theorem boundCheck_true (D R : Fin 10 → Nat) (p : List Nat) (bound : Nat) (cert : Bound 10) :
    boundCheck D R p bound cert = true ↔ BoundOK D R p bound cert := by
  simp only [boundCheck,Bool.and_eq_true,envelopeCheck_true,List.all_eq_true,regionCheck_true,
    coverCheck_true,decide_eq_true_eq,BoundOK]
  simp only [and_assoc]

def check (D R : Fin 10 → Nat) (choices : Nat → List Nat)
    (bound : Nat) (p : List Nat) : Tree 10 → Bool
  | .invalid => !prefixCheck D R p
  | .bound cert => boundCheck D R p bound cert
  | .branch representatives route children =>
    if h : p.length < 10 then
      routesCheck D R p (choices (D ⟨p.length,h⟩)) representatives route &&
        representatives.all (fun mask => check D R choices bound (p++[mask]) (children mask))
    else false

theorem sound (D R : Fin 10 → Nat) (choices : Nat → List Nat)
    (complete : ∀ s : Fin 10, RowCover 10 (D s) (choices (D s)))
    (bound : Nat) (p : List Nat) (tree : Tree 10)
    (checked : check D R choices bound p tree = true) : Upper D R p bound := by
  induction tree generalizing p with
  | invalid =>
    apply invalid_upper D R p bound
    intro valid
    have := (prefixCheck_true D R p).mpr valid
    simp only [check,this] at checked
    contradiction
  | bound cert => exact bound_sound D R p bound cert ((boundCheck_true _ _ _ _ _).mp checked)
  | branch representatives route children ih =>
    simp only [check] at checked
    split at checked
    next h =>
      simp only [Bool.and_eq_true,routesCheck_true,List.all_eq_true] at checked
      exact routed_branch D R p bound h (choices (D ⟨p.length,h⟩)) representatives route
        (complete ⟨p.length,h⟩) checked.1
        (fun mask member => ih mask (p++[mask]) (checked.2 mask member))
    next h => contradiction

#print axioms sound
end Delivery.RowPrefix.Boolean
