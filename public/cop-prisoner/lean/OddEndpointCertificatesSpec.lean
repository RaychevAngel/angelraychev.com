import OddEndpointLocal

/-! Exact interface of the two retained odd-endpoint certificate archives.
This module states the finite obligations; it contains no literal witnesses. -/
namespace Delivery.OddEndpointCertificatesSpec
open OddEndpointGraph OddEndpointLocal LocalArena

def transferBound (r : Case) : Nat :=
  if r.val=0 then 14 else if r.val=1 then 9 else if r.val=2 then 17 else
  if r.val=3 then 34 else if r.val=4 then 28 else 9
def deliveryBound (r : Case) : Nat :=
  if r.val=0 then 26 else if r.val=1 then 22 else if r.val=2 then 26 else
  if r.val=3 then 23 else if r.val=4 then 27 else 26
def entryColumn (r : Case) : Int := if r.val=2 ∨ r.val=5 then 1 else -1

def transferEntry (r : Case) (a : Option Int) (x : R) : Prop :=
  presentR r a x ∧ eligible r a (rvertex x) ∧ (rvertex x).1=entryColumn r
def deliveryEntry (r : Case) (a : Option Int) (x : R) : Prop :=
  presentR r a x ∧ eligible r a (rvertex x) ∧
    ((rvertex x).1=2*entryColumn r ∨ (r.val=5 ∧ (rvertex x).1=3))
def targetAllowed (r : Case) (a : Option Int) (j : Fin 6) : Prop :=
  present r a (0,j) ∧ match a with
    | none => True
    | some h => translate (0,j) (-h)≠OddEndpointStrip.target r

instance (r : Case) (a : Option Int) (x : R) : Decidable (safeGoal r a x) :=
  inferInstanceAs (Decidable (_∧_∧(_∨(_∧_))))
instance (r : Case) (a : Option Int) (j : Fin 6) (x : R) : Decidable (deliveryGoal r a j x) :=
  inferInstanceAs (Decidable (_∧_))
instance (r : Case) (a : Option Int) (x : R) : Decidable (transferEntry r a x) :=
  inferInstanceAs (Decidable (_∧_∧_))
instance (r : Case) (a : Option Int) (x : R) : Decidable (deliveryEntry r a x) :=
  inferInstanceAs (Decidable (_∧_∧(_∨(_∧_))))
instance (r : Case) (a : Option Int) (j : Fin 6) : Decidable (targetAllowed r a j) := by
  cases a <;> unfold targetAllowed <;> infer_instance
instance (r : Case) (a : Option Int) (x : R) (c : C) : Decidable ((arena r a).collision x c) :=
  inferInstanceAs (Decidable (_∨_))
instance (r : Case) (a : Option Int) : DecidableRel (arena r a).messenger :=
  inferInstanceAs (DecidableRel (messenger r a))
instance (r : Case) (a : Option Int) : DecidableRel (arena r a).pursuer :=
  inferInstanceAs (DecidableRel (pursuer r a))

structure Transfer (r : Case) (a : Option Int) where
  data : Data R C
  checked : SafeChecked (arena r a) (safeGoal r a) data
  starts : ∀ x c, transferEntry r a x → presentC r a c → ¬(arena r a).collision x c →
    data.region x c ∧ data.rank x c≤transferBound r

structure Delivery (r : Case) (a : Option Int) (j : Fin 6) where
  data : Data R C
  checked : DeliveryChecked (arena r a) (deliveryGoal r a j) data
  starts : ∀ x c, deliveryEntry r a x → presentC r a c → ¬(arena r a).collision x c →
    data.region x c ∧ data.rank x c≤deliveryBound r

structure Certificates (r : Case) (a : Option Int) where
  transfer : Transfer r a
  delivery : ∀ j, targetAllowed r a j → Delivery r a j

def Catalogued (r : Case) : Option Int → Prop
  | none => True
  | some h => -(OddEndpointParameters.anchorLimit r : Int)≤h ∧
      h≤(OddEndpointParameters.anchorLimit r : Int)

theorem uniform_bounds (r : Case) : transferBound r≤34 ∧ deliveryBound r≤27 := by
  have finite : ∀ r, transferBound r≤34 ∧ deliveryBound r≤27 := by decide +kernel
  exact finite r

#print axioms uniform_bounds
end Delivery.OddEndpointCertificatesSpec
