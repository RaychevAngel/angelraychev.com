import SinglePatchWindow

/-! Exact arithmetic for the six retained odd-endpoint local arenas. These
bounds certify the window geometry at every order at least98; they do not
assert the finite strategy certificates or the concrete graph simulation. -/
namespace Delivery.OddEndpointParameters

def radius (r : Fin 6) : Nat := if r.val<3 then 6 else 7
def jump (r : Fin 6) : Nat := if r.val=1 then 1 else 2
def span (r : Fin 6) : Nat := if r.val=0 then 0 else if r.val=5 then 3 else 2
def supportMax (r : Fin 6) : Nat := if r.val=0 then 0 else if r.val=5 then 2 else 1
def anchorLimit (r : Fin 6) : Nat := if r.val=0 then 6 else 10
def minimum (r : Fin 6) : Nat := if r.val<3 then 15 else if r.val=5 then 18 else 17

theorem case_values (r : Fin 6) : r.val=0 ∨ r.val=1 ∨ r.val=2 ∨ r.val=3 ∨ r.val=4 ∨ r.val=5 := by
  have := r.isLt
  omega

/-- The two independent projection inequalities: no long short-edge wrap,
and no second lift of the supported defect inside the pursuer window. -/
theorem projection_bounds {q : Nat} (r : Fin 6) (large : minimum r≤q) :
    2*radius r+jump r<q ∧ 2*radius r+span r<q := by
  rcases case_values r with h|h|h|h|h|h <;>
    simp [minimum,radius,jump,span,h] at * <;> omega

/-- An unsigned anchor for the window based at `-R` corresponds to signed
patch translation `h-R-b`; every such anchor is in the frozen catalogue. -/
theorem anchor_covered (r : Fin 6) {h : Nat} (range : h≤2*radius r+span r) :
    -(anchorLimit r : Int)≤(h : Int)-(radius r : Int)-(supportMax r : Int) ∧
    (h : Int)-(radius r : Int)-(supportMax r : Int)≤(anchorLimit r : Int) := by
  rcases case_values r with h|h|h|h|h|h <;>
    simp [radius,span,supportMax,anchorLimit,h] at * <;> omega

/-- This handles all six residues at once, including the sharp last excluded
case `q=17,r=5,n=97`. -/
theorem circumference {n q : Nat} (r : Fin 6)
    (order : 98≤n) (size : n+r.val=6*q) : minimum r≤q := by
  rcases case_values r with h|h|h|h|h|h <;>
    simp [minimum,h] at * <;> omega

def circumferenceOf (n : Nat) : Nat := (n+5)/6

theorem residue_lt (n : Nat) : 6*circumferenceOf n-n<6 := by
  unfold circumferenceOf
  omega

def residue (n : Nat) : Fin 6 := ⟨6*circumferenceOf n-n,residue_lt n⟩

theorem size (n : Nat) : n+(residue n).val=6*circumferenceOf n := by
  unfold residue circumferenceOf
  dsimp
  omega

theorem uniform (n : Nat) (large : 98≤n) :
    2*radius (residue n)+jump (residue n)<circumferenceOf n ∧
    2*radius (residue n)+span (residue n)<circumferenceOf n :=
  projection_bounds _ (circumference _ large (size n))

theorem last_excluded : circumferenceOf 97<minimum (residue 97) := by
  decide +kernel

#print axioms uniform
#print axioms anchor_covered
end Delivery.OddEndpointParameters
