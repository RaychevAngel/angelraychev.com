import OddEndpointLifting
import LocalArena

/-! Fixed padded local arenas for the six odd-endpoint archives. Padding
vertices are unusable and collide universally; delivery and safe transfer
remain separate goals. No finite strategy certificate is assumed here. -/
namespace Delivery.OddEndpointLocal
open OddEndpointGraph LocalArena
abbrev R := Fin 66
abbrev C := Fin 91
def outside : C := 90
def messengerRadius (r : Case) : Nat := OddEndpointParameters.radius r-2
def rvertex (x : R) : OddEndpointStrip.Vertex :=
  ((x.val/6 : Int)-5,⟨x.val%6,Nat.mod_lt _ (by decide)⟩)
def cvertex (c : C) : OddEndpointStrip.Vertex :=
  ((c.val/6 : Int)-7,⟨c.val%6,Nat.mod_lt _ (by decide)⟩)
def translate (v : OddEndpointStrip.Vertex) (h : Int) : OddEndpointStrip.Vertex := (v.1+h,v.2)

def inWindow (radius : Nat) (v : OddEndpointStrip.Vertex) : Prop :=
  -(radius : Int)≤v.1 ∧ v.1≤(radius : Int)
instance (radius : Nat) (v : OddEndpointStrip.Vertex) : Decidable (inWindow radius v) :=
  inferInstanceAs (Decidable (_≤_∧_≤_))

def present (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) : Prop :=
  match anchor with
  | none => True
  | some h => translate v (-h)∉OddEndpointStrip.holes r
instance (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) : Decidable (present r anchor v) := by
  cases anchor <;> unfold present <;> infer_instance

def permitted (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) (b : Bool) : Prop :=
  match anchor with
  | none => True
  | some h => OddEndpointStrip.permitted r (translate v (-h)) b
instance (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) (b : Bool) :
    Decidable (permitted r anchor v b) := by
  cases anchor <;> unfold permitted <;> infer_instance

def next (r : Case) (anchor : Option Int) (b : Bool) (v : OddEndpointStrip.Vertex) :
    OddEndpointStrip.Vertex :=
  match anchor with
  | none => OddEndpointStrip.raw r b v
  | some h => translate (OddEndpointStrip.smooth r b (translate v (-h))) h

def presentR (r : Case) (anchor : Option Int) (x : R) : Prop :=
  inWindow (messengerRadius r) (rvertex x) ∧ present r anchor (rvertex x)
instance (r : Case) (anchor : Option Int) (x : R) : Decidable (presentR r anchor x) :=
  inferInstanceAs (Decidable (_∧_))
def presentC (r : Case) (anchor : Option Int) (c : C) : Prop :=
  c=outside ∨ inWindow (OddEndpointParameters.radius r) (cvertex c) ∧ present r anchor (cvertex c)
instance (r : Case) (anchor : Option Int) (c : C) : Decidable (presentC r anchor c) :=
  inferInstanceAs (Decidable (_∨_∧_))

def pack (r : Case) (v : OddEndpointStrip.Vertex) : C :=
  if inside : inWindow (OddEndpointParameters.radius r) v then
    ⟨6*(v.1+7).toNat+v.2.val,by
      have radius : OddEndpointParameters.radius r≤7 := by
        unfold OddEndpointParameters.radius
        split <;> omega
      have := v.2.isLt
      unfold inWindow at inside
      omega⟩
  else outside

def messenger (r : Case) (anchor : Option Int) (x y : R) : Prop :=
  presentR r anchor x ∧ presentR r anchor y ∧
    (x=y ∨ ∃ b : Bool, permitted r anchor (rvertex x) b ∧
      rvertex y=next r anchor b (rvertex x))
instance (r : Case) (anchor : Option Int) : DecidableRel (messenger r anchor) :=
  fun _ _ => inferInstanceAs (Decidable (_∧_∧(_∨∃ _ : Bool,_∧_)))

def boundary (r : Case) (c : C) : Prop :=
  (cvertex c).1≤-(OddEndpointParameters.radius r : Int)+(OddEndpointParameters.jump r : Int)-1 ∨
    (OddEndpointParameters.radius r : Int)-(OddEndpointParameters.jump r : Int)+1≤(cvertex c).1
instance (r : Case) (c : C) : Decidable (boundary r c) :=
  inferInstanceAs (Decidable (_≤_∨_≤_))

def pursuer (r : Case) (anchor : Option Int) (c d : C) : Prop :=
  presentC r anchor c ∧ presentC r anchor d ∧
    if c=outside then d=outside ∨ boundary r d
    else d=c ∨ ∃ b : Bool, permitted r anchor (cvertex c) b ∧
      d=pack r (next r anchor b (cvertex c))
instance (r : Case) (anchor : Option Int) : DecidableRel (pursuer r anchor) :=
  fun _ _ => inferInstanceAs (Decidable (_∧_∧ite _ _ _))

def arena (r : Case) (anchor : Option Int) : Arena R C where
  messenger := messenger r anchor
  pursuer := pursuer r anchor
  collision := fun x c => ¬presentR r anchor x ∨ pack r (rvertex x)=c

def eligible (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) : Prop :=
  match anchor with
  | none => True
  | some h => translate v (-h)≠OddEndpointStrip.source r
instance (r : Case) (anchor : Option Int) (v : OddEndpointStrip.Vertex) : Decidable (eligible r anchor v) := by
  cases anchor <;> unfold eligible <;> infer_instance

def safeGoal (r : Case) (anchor : Option Int) (x : R) : Prop :=
  presentR r anchor x ∧ eligible r anchor (rvertex x) ∧
    ((rvertex x).1=0 ∨ (r.val=5 ∧ (rvertex x).1 = -1))
def deliveryGoal (r : Case) (anchor : Option Int) (j : Fin 6) (x : R) : Prop :=
  presentR r anchor x ∧ rvertex x=(0,j)

theorem radius_bounds (r : Case) : 6≤OddEndpointParameters.radius r ∧
    OddEndpointParameters.radius r≤7 ∧ messengerRadius r+2=OddEndpointParameters.radius r := by
  unfold messengerRadius OddEndpointParameters.radius
  split <;> omega

theorem next_present (r : Case) (anchor : Option Int) (b : Bool)
    (v : OddEndpointStrip.Vertex) (available : present r anchor v) :
    present r anchor (next r anchor b v) := by
  cases anchor with
  | none => trivial
  | some h =>
    change translate (translate (OddEndpointStrip.smooth r b (translate v (-h))) h) (-h)∉_
    have same : translate (translate (OddEndpointStrip.smooth r b (translate v (-h))) h) (-h)=
        OddEndpointStrip.smooth r b (translate v (-h)) := by
      apply Prod.ext
      · dsimp [translate]; omega
      · rfl
    rw [same]
    exact ((OddEndpointStrip.good r (translate v (-h)) available).1 b).1

theorem next_jump (r : Case) (anchor : Option Int) (b : Bool)
    (v : OddEndpointStrip.Vertex) (available : present r anchor v)
    (allowed : permitted r anchor v b) :
    -(OddEndpointParameters.jump r : Int)≤(next r anchor b v).1-v.1 ∧
    (next r anchor b v).1-v.1≤(OddEndpointParameters.jump r : Int) := by
  cases anchor with
  | none =>
    have raw := OddEndpointStrip.raw_displacement r b v.2
    have positive := OddEndpointStrip.jump_positive r
    dsimp [next,OddEndpointStrip.raw]
    omega
  | some h =>
    have bounds := ((OddEndpointStrip.good r (translate v (-h)) available).1 b).2.2.2.2 allowed
    dsimp [next,translate] at *
    omega

#print axioms next_present
#print axioms next_jump
end Delivery.OddEndpointLocal
