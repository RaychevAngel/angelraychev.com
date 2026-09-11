import CrossUnitsGeometry

namespace PolyominoFormal

open CrossUnits

abbrev Region := Int → Int → Prop

/-- A tiling is an arbitrary, possibly infinite, collection of congruent
    copies with containment, coverage, and ordinary cellwise disjointness. -/
structure Tiling (a b c d : Int) (R : Region) where
  world : Cross → Prop
  copies : ∀ t, world t → Copy a b c d t
  inside : ∀ t, world t → ∀ x y, Contains t x y → R x y
  cover : ∀ x y, R x y → ∃ t, world t ∧ Contains t x y
  disjoint : ∀ t u x y, world t → world u →
    Contains t x y → Contains u x y → t = u

def Tiles (a b c d : Int) (R : Region) : Prop := Nonempty (Tiling a b c d R)

def Rectangle (w h : Int) : Region := fun x y => 0 ≤ x ∧ x < w ∧ 0 ≤ y ∧ y < h
def HalfStrip (h : Int) : Region := fun x y => 0 ≤ x ∧ 0 ≤ y ∧ y < h
def BentStrip (w h : Int) : Region := fun x y =>
  0 ≤ x ∧ 0 ≤ y ∧ (x < w ∨ y < h)
def Quadrant : Region := fun x y => 0 ≤ x ∧ 0 ≤ y
def Strip (h : Int) : Region := fun _ y => 0 ≤ y ∧ y < h
def HalfPlane : Region := fun _ y => 0 ≤ y
def Plane : Region := fun _ _ => True

def RectangleTileable (a b c d : Int) : Prop :=
  ∃ w h, 0 < w ∧ 0 < h ∧ Tiles a b c d (Rectangle w h)
def HalfStripTileable (a b c d : Int) : Prop :=
  ∃ h, 0 < h ∧ Tiles a b c d (HalfStrip h)
def BentStripTileable (a b c d : Int) : Prop :=
  ∃ w h, 0 < w ∧ 0 < h ∧ Tiles a b c d (BentStrip w h)
def StripTileable (a b c d : Int) : Prop :=
  ∃ h, 0 < h ∧ Tiles a b c d (Strip h)

/-- Build a tiling from a family of explicit placements. No finiteness or
    periodicity hypothesis is built into the definition. -/
def Tiling.ofIndexed {a b c d : Int} {R : Region} {I : Type}
    (tile : I → Cross)
    (copies : ∀ i, Copy a b c d (tile i))
    (inside : ∀ i x y, Contains (tile i) x y → R x y)
    (cover : ∀ x y, R x y → ∃ i, Contains (tile i) x y)
    (disjoint : ∀ i j x y, Contains (tile i) x y →
      Contains (tile j) x y → tile i = tile j) : Tiling a b c d R where
  world t := ∃ i, tile i = t
  copies := by rintro t ⟨i, rfl⟩; exact copies i
  inside := by rintro t ⟨i, rfl⟩; exact inside i
  cover := by
    intro x y h
    obtain ⟨i, hi⟩ := cover x y h
    exact ⟨tile i, ⟨i, rfl⟩, hi⟩
  disjoint := by
    rintro t u x y ⟨i, rfl⟩ ⟨j, rfl⟩ ht hu
    exact disjoint i j x y ht hu

def shift (p q : Int) (t : Cross) : Cross :=
  ⟨t.x + p, t.y + q, t.east, t.north, t.west, t.south⟩

@[simp] theorem shift_zero (t : Cross) : shift 0 0 t = t := by cases t; simp [shift]

theorem shift_add (p q r s : Int) (t : Cross) :
    shift p q (shift r s t) = shift (r+p) (s+q) t := by
  cases t; simp [shift, Int.add_assoc]

theorem shift_injective (p q : Int) {t u : Cross}
    (h : shift p q t = shift p q u) : t = u := by
  have h' := congrArg (shift (-p) (-q)) h
  have hp : p + -p = 0 := by omega
  have hq : q + -q = 0 := by omega
  simpa [shift_add, hp, hq] using h'

@[simp] theorem contains_shift (p q x y : Int) (t : Cross) :
    Contains (shift p q t) x y ↔ Contains t (x-p) (y-q) := by
  unfold Contains shift; dsimp; omega

@[simp] theorem copy_shift (a b c d p q : Int) (t : Cross) :
    Copy a b c d (shift p q t) ↔ Copy a b c d t := by
  rfl

def Tiling.translate {a b c d : Int} {R : Region}
    (T : Tiling a b c d R) (p q : Int) :
    Tiling a b c d (fun x y => R (x-p) (y-q)) where
  world t := ∃ u, T.world u ∧ shift p q u = t
  copies := by
    rintro t ⟨u, hu, rfl⟩
    exact (copy_shift _ _ _ _ _ _ _).2 (T.copies u hu)
  inside := by
    rintro t ⟨u, hu, rfl⟩ x y h
    exact T.inside u hu _ _ ((contains_shift _ _ _ _ _).1 h)
  cover := by
    intro x y h
    obtain ⟨t, ht, hit⟩ := T.cover _ _ h
    exact ⟨shift p q t, ⟨t, ht, rfl⟩, (contains_shift _ _ _ _ _).2 hit⟩
  disjoint := by
    rintro t u x y ⟨t', ht', rfl⟩ ⟨u', hu', rfl⟩ ht hu
    have heq := T.disjoint t' u' (x-p) (y-q) ht' hu'
      ((contains_shift _ _ _ _ _).1 ht) ((contains_shift _ _ _ _ _).1 hu)
    exact congrArg (shift p q) heq

def Tiling.congr {a b c d : Int} {R S : Region}
    (T : Tiling a b c d R) (h : ∀ x y, R x y ↔ S x y) : Tiling a b c d S where
  world := T.world
  copies := T.copies
  inside t ht x y hc := (h x y).1 (T.inside t ht x y hc)
  cover x y hs := T.cover x y ((h x y).2 hs)
  disjoint := T.disjoint

def Tiling.union {a b c d : Int} {R S : Region}
    (T : Tiling a b c d R) (U : Tiling a b c d S)
    (apart : ∀ x y, R x y → S x y → False) :
    Tiling a b c d (fun x y => R x y ∨ S x y) where
  world t := T.world t ∨ U.world t
  copies t ht := ht.elim (T.copies t) (U.copies t)
  inside := by
    intro t ht x y hc
    exact ht.elim (fun h => Or.inl (T.inside t h x y hc))
      (fun h => Or.inr (U.inside t h x y hc))
  cover := by
    intro x y h
    rcases h with h | h
    · obtain ⟨t, ht, hc⟩ := T.cover x y h
      exact ⟨t, Or.inl ht, hc⟩
    · obtain ⟨t, ht, hc⟩ := U.cover x y h
      exact ⟨t, Or.inr ht, hc⟩
  disjoint := by
    intro t u x y ht hu hc hd
    rcases ht with ht | ht <;> rcases hu with hu | hu
    · exact T.disjoint t u x y ht hu hc hd
    · exact False.elim (apart x y (T.inside t ht x y hc) (U.inside u hu x y hd))
    · exact False.elim (apart x y (T.inside u hu x y hd) (U.inside t ht x y hc))
    · exact U.disjoint t u x y ht hu hc hd

/-- Stack two half-strips to double the height. Applying this twice gives
    height at least four from any positive integer height. -/
def Tiling.doubleHalfStrip {a b c d h : Int} (hh : 0 < h)
    (T : Tiling a b c d (HalfStrip h)) : Tiling a b c d (HalfStrip (h+h)) :=
  (T.union (T.translate 0 h) (by
    intro x y h₁ h₂
    simp only [HalfStrip] at h₁ h₂
    omega)).congr (by
      intro x y
      simp only [HalfStrip]
      omega)

end PolyominoFormal
