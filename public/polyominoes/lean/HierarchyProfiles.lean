import GunFamilyClassification
import UnitStemClassification
import PositiveCrossClassification
import RepComposition

namespace PolyominoFormal
open CrossUnits

inductive Capability where
  | rectangle | halfStrip | bentStrip | quadrant | strip | halfPlane | plane | rep
  deriving DecidableEq, Repr

inductive HierarchyClass where
  | rectangle | bentStrip | strip | plane | none
  deriving DecidableEq, Repr

def HasCapability (a b c d : Int) : Capability→Prop
  | .rectangle => RectangleTileable a b c d
  | .halfStrip => HalfStripTileable a b c d
  | .bentStrip => BentStripTileable a b c d
  | .quadrant => Tiles a b c d Quadrant
  | .strip => StripTileable a b c d
  | .halfPlane => Tiles a b c d HalfPlane
  | .plane => Tiles a b c d Plane
  | .rep => RepTileable a b c d

def Supports : HierarchyClass→Capability→Prop
  | .rectangle,_ => True
  | .bentStrip,.bentStrip | .bentStrip,.quadrant | .bentStrip,.strip |
    .bentStrip,.halfPlane | .bentStrip,.plane => True
  | .strip,.strip | .strip,.halfPlane | .strip,.plane => True
  | .plane,.plane => True
  | _,_ => False

def Classified (a b c d : Int) (rank : HierarchyClass) : Prop :=
  ∀ cap, HasCapability a b c d cap ↔ Supports rank cap

def SameCopies (a b c d e f g h : Int) : Prop :=
  ∀ t, Copy a b c d t ↔ Copy e f g h t

def Tiling.changeParameters {a b c d e f g h : Int} {R : Region}
    (same : SameCopies a b c d e f g h) (T : Tiling a b c d R) : Tiling e f g h R where
  world := T.world
  copies t ht := (same t).1 (T.copies t ht)
  inside := T.inside
  cover := T.cover
  disjoint := T.disjoint

theorem same_copies_symm {a b c d e f g h : Int}
    (same : SameCopies a b c d e f g h) : SameCopies e f g h a b c d :=
  fun t => (same t).symm

theorem same_copies_tiles {a b c d e f g h : Int} {R : Region}
    (same : SameCopies a b c d e f g h) : Tiles a b c d R ↔ Tiles e f g h R := by
  constructor
  · rintro ⟨T⟩; exact ⟨T.changeParameters same⟩
  · rintro ⟨T⟩; exact ⟨T.changeParameters (same_copies_symm same)⟩

theorem same_copies_rep_one_way {a b c d e f g h : Int}
    (same : SameCopies a b c d e f g h) (rep : RepTileable a b c d) : RepTileable e f g h := by
  obtain ⟨k,hk,⟨T⟩⟩ := rep
  have target : Copy a b c d ⟨0,0,e,f,g,h⟩ :=
    (same _).2 (Or.inl ⟨rfl,rfl,rfl,rfl⟩)
  obtain ⟨U⟩ := scaled_copy_tileable T ⟨0,0,e,f,g,h⟩ target
  exact ⟨k,hk,⟨U.changeParameters same⟩⟩

theorem same_copies_rep {a b c d e f g h : Int}
    (same : SameCopies a b c d e f g h) : RepTileable a b c d ↔ RepTileable e f g h :=
  ⟨same_copies_rep_one_way same,same_copies_rep_one_way (same_copies_symm same)⟩

theorem same_copies_capability {a b c d e f g h : Int}
    (same : SameCopies a b c d e f g h) (cap : Capability) :
    HasCapability a b c d cap ↔ HasCapability e f g h cap := by
  cases cap with
  | rectangle =>
    simp only [HasCapability,RectangleTileable]
    exact exists_congr (fun w => exists_congr (fun h => and_congr_right
      (fun _ => and_congr_right (fun _ => same_copies_tiles same))))
  | halfStrip =>
    simp only [HasCapability,HalfStripTileable]
    exact exists_congr (fun h => and_congr_right (fun _ => same_copies_tiles same))
  | bentStrip =>
    simp only [HasCapability,BentStripTileable]
    exact exists_congr (fun w => exists_congr (fun h => and_congr_right
      (fun _ => and_congr_right (fun _ => same_copies_tiles same))))
  | strip =>
    simp only [HasCapability,StripTileable]
    exact exists_congr (fun h => and_congr_right (fun _ => same_copies_tiles same))
  | quadrant | halfPlane | plane => exact same_copies_tiles same
  | rep => exact same_copies_rep same

theorem same_copies_classified {a b c d e f g h : Int} {rank : HierarchyClass}
    (same : SameCopies a b c d e f g h) (classified : Classified a b c d rank) :
    Classified e f g h rank :=
  fun cap => (same_copies_capability same cap).symm.trans (classified cap)

theorem same_copies_rotate (a b c d : Int) : SameCopies a b c d b c d a :=
  copy_rotate_parameters a b c d

theorem same_copies_swap_T (a b c : Int) : SameCopies a b c 0 c b a 0 := by
  intro t
  simp only [Copy, or_assoc, or_comm, or_left_comm]

theorem same_copies_swap_L (a b : Int) : SameCopies a b 0 0 b a 0 0 := by
  intro t
  simp only [Copy, or_assoc, or_comm, or_left_comm]

def classifyL (a b : Nat) : HierarchyClass :=
  if min a b≤1 then .rectangle
  else if min a b=2 ∨ (max a b=4 ∧ min a b=3) then .strip else .plane

def classifyT (a b c : Nat) : HierarchyClass :=
  if b=1 then
    if c=1 then (if a≤3 then .rectangle else .bentStrip) else .strip
  else if b≤2 ∨ c=1 ∨ (c=2 ∧ b=a+3) then .plane else .none

def classifyZeroSouth (a b c : Nat) : HierarchyClass :=
  if b=0 then .rectangle
  else if a=0 then classifyL b c
  else if c=0 then classifyL a b
  else classifyT (max a c) b (min a c)

def classifyTuple (a b c d : Nat) : HierarchyClass :=
  if d=0 then classifyZeroSouth a b c
  else if a=0 then classifyZeroSouth b c d
  else if b=0 then classifyZeroSouth c d a
  else if c=0 then classifyZeroSouth d a b
  else if (a=1 ∧ c=1) ∨ (b=1 ∧ d=1) then .plane else .none

#print axioms same_copies_rep
end PolyominoFormal
