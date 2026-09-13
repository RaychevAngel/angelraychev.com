import Std

/-!
Clipped erosion on actual nonnegative cylinder cells. The module proves
neighborhood inclusion and the exact occupied-root loss. It does not
assume a graph-distance threshold or prescribed-size ideal enlargement.
-/

namespace Princess.ClippedPyramidErosion

def height (s k : Nat) : Int := (s : Int)-2+2*(k : Int)

def erode (s k : Nat) : Nat := if s=0 then k-1 else k

theorem height_clipped (s k : Nat) (hs : s≤1) :
    height (1-s) (erode s k) = max (height s k-1) ((1-s : Nat)-2 : Int) := by
  by_cases h : s=0
  · subst s
    by_cases hk : k=0
    · subst k
      simp [height, erode]
      omega
    · simp only [erode, if_true, height]
      omega
  · have : s=1 := by omega
    subst s
    simp [height, erode]
    omega

/-- The clipping term represents an empty fiber, so it cannot contribute
an actual cell of nonnegative height. -/
theorem actual_below_original (s k y : Nat) (hs : s≤1)
    (hy : (y : Int)≤height (1-s) (erode s k)) :
    (y : Int)+1≤height s k := by
  rw [height_clipped s k hs] at hy
  have : ((1-s : Nat)-2 : Int)<0 := by omega
  omega

theorem eroded_edge (s t k l : Nat) (hs : s≤1) (ht : t≤1)
    (hcol : s+t=1)
    (h1 : height s k≤height t l+1) (h2 : height t l≤height s k+1) :
    (height (1-s) (erode s k) = height (1-t) (erode t l)+1) ∨
    (height (1-t) (erode t l) = height (1-s) (erode s k)+1) := by
  have hc1 := height_clipped s k hs
  have hc2 := height_clipped t l ht
  have hle1 : height (1-s) (erode s k)≤height (1-t) (erode t l)+1 := by
    omega
  have hle2 : height (1-t) (erode t l)≤height (1-s) (erode s k)+1 := by
    omega
  unfold height at *
  omega

def Cell {V : Type} (s k : V → Nat) (n : Nat) (v : V × Nat) : Prop :=
  v.2<n ∧ v.2%2=s v.1 ∧ (v.2 : Int)≤height (s v.1) (k v.1)

def fiberRooms (s k : Nat) : List Nat := (List.range k).map (fun i => s+2*i)

/-- The virtual height really represents exactly the spacing-two fiber. -/
theorem mem_fiberRooms (s k y : Nat) (hs : s≤1) :
    y∈fiberRooms s k ↔ y%2=s ∧ (y : Int)≤height s k := by
  simp only [fiberRooms, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i,hi,rfl⟩
    unfold height
    omega
  · rintro ⟨hp,hh⟩
    refine ⟨y/2,?_,?_⟩ <;> unfold height at hh <;> omega

theorem fiberRooms_length (s k : Nat) : (fiberRooms s k).length=k := by
  simp [fiberRooms]

theorem fiberRooms_nodup (s k : Nat) : (fiberRooms s k).Nodup := by
  unfold fiberRooms List.Nodup
  exact List.Pairwise.map (fun i => s+2*i) (fun i j h => by omega) List.nodup_range

/-- With a fitting top cutoff, the list counts actual finite-cylinder
cells, rather than unbounded virtual cells. -/
theorem mem_fiberRooms_bounded (s k n y : Nat) (hs : s≤1)
    (hfit : height s k < (n : Int)) :
    y∈fiberRooms s k ↔ y<n ∧ y%2=s ∧ (y : Int)≤height s k := by
  rw [mem_fiberRooms s k y hs]
  constructor
  · rintro ⟨hp,hh⟩
    exact ⟨by omega,hp,hh⟩
  · intro h
    exact h.2

theorem eroded_fits (s k n : Nat) (hs : s≤1)
    (hfit : height s k < (n : Int)) :
    height (1-s) (erode s k) < (n : Int) := by
  rw [height_clipped s k hs]
  omega

def CylinderEdge {V : Type} (adj : V → V → Prop) (a b : V × Nat) : Prop :=
  (a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨ (adj a.1 b.1 ∧ a.2=b.2)

/-- Every valid cylinder neighbor of an actual eroded cell belongs to the
original pyramid, including empty and clipped fibers and both finite ends. -/
theorem neighbor_in_original {V : Type} (adj : V → V → Prop)
    (s k : V → Nat) (n : Nat)
    (hbits : ∀ v, s v≤1)
    (hcolors : ∀ u v, adj u v → s u+s v=1)
    (hheight : ∀ u v, adj u v → height (s u) (k u)≤height (s v) (k v)+1)
    (a b : V × Nat)
    (ha : Cell (fun v => 1-s v) (fun v => erode (s v) (k v)) n a)
    (hb : b.2<n) (hab : CylinderEdge adj a b) : Cell s k n b := by
  obtain ⟨han,hap,hah⟩ := ha
  change a.2%2=1-s a.1 at hap
  change (a.2 : Int)≤height (1-s a.1) (erode (s a.1) (k a.1)) at hah
  have habove := actual_below_original (s a.1) (k a.1) a.2 (hbits a.1) hah
  refine ⟨hb,?_,?_⟩
  · rcases hab with ⟨he,hstep⟩ | ⟨he,hstep⟩
    · have hbit := hbits a.1
      have hsame : s a.1=s b.1 := congrArg s he
      omega
    · have hc := hcolors a.1 b.1 he
      omega
  · rcases hab with ⟨he,hstep⟩ | ⟨he,hstep⟩
    · have hsame : height (s a.1) (k a.1)=height (s b.1) (k b.1) := by rw [he]
      omega
    · have hh := hheight a.1 b.1 he
      omega

def RootLoss (s k : Nat) : Nat := if s=0 ∧ 0<k then 1 else 0

theorem fiber_loss (s k : Nat) : k = erode s k+RootLoss s k := by
  by_cases hs : s=0 <;> by_cases hk : 0<k <;>
    simp [erode,RootLoss,hs,hk] <;> omega

def countFibers {V : Type} (k : V → Nat) : List V → Nat
  | [] => 0
  | v::vs => k v+countFibers k vs

def rooms {V : Type} (s k : V → Nat) (vs : List V) : List (V × Nat) :=
  vs.flatMap (fun v => (fiberRooms (s v) (k v)).map (fun y => (v,y)))

theorem mem_rooms {V : Type} (s k : V → Nat) (vs : List V) (v : V) (y : Nat) :
    (v,y)∈rooms s k vs ↔ v∈vs ∧ y∈fiberRooms (s v) (k v) := by
  simp only [rooms, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u,hu,z,hz,he⟩
    cases he
    exact ⟨hu,hz⟩
  · rintro ⟨hv,hy⟩
    exact ⟨v,hv,y,hy,rfl⟩

theorem rooms_length {V : Type} (s k : V → Nat) (vs : List V) :
    (rooms s k vs).length=countFibers k vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change ((fiberRooms (s v) (k v)).map (fun y => (v,y)) ++ rooms s k vs).length=_
    simp [List.length_append, fiberRooms_length, ih, countFibers]

theorem rooms_nodup {V : Type} (s k : V → Nat) (vs : List V) (hv : vs.Nodup) :
    (rooms s k vs).Nodup := by
  unfold rooms List.Nodup
  apply List.pairwise_flatMap.mpr
  constructor
  · intro v _
    exact List.Pairwise.map (fun y => (v,y))
      (fun a b (hab : a≠b) he => hab (congrArg Prod.snd he))
      (fiberRooms_nodup (s v) (k v))
  · apply List.Pairwise.imp _ hv
    intro a b hab x hx y hy he
    obtain ⟨xx,_,hxx⟩ := List.mem_map.mp hx
    obtain ⟨yy,_,hyy⟩ := List.mem_map.mp hy
    have hf := congrArg Prod.fst (hxx.trans (he.trans hyy.symm))
    exact hab hf

theorem rooms_are_cells {V : Type} (s k : V → Nat) (vs : List V) (n : Nat)
    (hs : ∀ v, v∈vs → s v≤1)
    (hfit : ∀ v, v∈vs → height (s v) (k v)<(n : Int))
    (v : V) (y : Nat) :
    (v,y)∈rooms s k vs ↔ v∈vs ∧ Cell s k n (v,y) := by
  rw [mem_rooms]
  constructor
  · rintro ⟨hv,hy⟩
    exact ⟨hv,(mem_fiberRooms_bounded (s v) (k v) n y (hs v hv) (hfit v hv)).mp hy⟩
  · rintro ⟨hv,hy⟩
    exact ⟨hv,(mem_fiberRooms_bounded (s v) (k v) n y (hs v hv) (hfit v hv)).mpr hy⟩

def occupiedRoots {V : Type} (s k : V → Nat) : List V → Nat
  | [] => 0
  | v::vs => RootLoss (s v) (k v)+occupiedRoots s k vs

def roots {V : Type} (s : V → Nat) : List V → Nat
  | [] => 0
  | v::vs => (if s v=0 then 1 else 0)+roots s vs

/-- Exact loss before imposing any threshold: only occupied bottom roots
lose a cell. Empty fibers of the other phase are permitted. -/
theorem exact_loss {V : Type} (s k : V → Nat) (vs : List V) :
    countFibers k vs =
      countFibers (fun v => erode (s v) (k v)) vs+occupiedRoots s k vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hv := fiber_loss (s v) (k v)
    simp only [countFibers, occupiedRoots]
    omega

theorem occupiedRoots_eq_roots {V : Type} (s k : V → Nat) (vs : List V)
    (h : ∀ v, v∈vs → s v=0 → 0<k v) : occupiedRoots s k vs=roots s vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hv : s v=0 → 0<k v := h v (by simp)
    have ht := ih (fun u hu => h u (by simp [hu]))
    simp only [occupiedRoots, roots, ht, RootLoss]
    by_cases hs : s v=0 <;> simp [hs,hv]

/-- Once all bottom-root fibers are occupied, erosion loses the size of
that transverse bipartition. Other empty fibers do not obstruct it. -/
theorem root_loss {V : Type} (s k : V → Nat) (vs : List V)
    (h : ∀ v, v∈vs → s v=0 → 0<k v) :
    countFibers k vs = countFibers (fun v => erode (s v) (k v)) vs+roots s vs := by
  rw [exact_loss s k vs, occupiedRoots_eq_roots s k vs h]

/-- Actual room-list cardinalities. Together with `rooms_nodup` and
`rooms_are_cells`, this is the finite-cylinder cardinality statement. -/
theorem room_cardinality_loss {V : Type} (s k : V → Nat) (vs : List V)
    (h : ∀ v, v∈vs → s v=0 → 0<k v) :
    (rooms s k vs).length =
      (rooms (fun v => 1-s v) (fun v => erode (s v) (k v)) vs).length+roots s vs := by
  rw [rooms_length, rooms_length]
  exact root_loss s k vs h

#print axioms height_clipped
#print axioms mem_fiberRooms_bounded
#print axioms fiberRooms_nodup
#print axioms eroded_edge
#print axioms neighbor_in_original
#print axioms root_loss
#print axioms rooms_nodup
#print axioms room_cardinality_loss

end Princess.ClippedPyramidErosion
