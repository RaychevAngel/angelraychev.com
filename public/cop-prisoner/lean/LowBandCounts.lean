import LowBandComposition
import SixTypeCounts
import GuaranteedPrefix

/-! Exact optional-arrow counts on the canonical retained six-type vertices. -/
namespace Delivery.LowBandCounts
open CyclicArithmetic SixTypeGraph LowBandGraph SixTypeCounts
open FiniteGame Extremal DenseCombinatorics ConstructionCounts

def column {k : Nat} (x : Fin (8*k)) : Fin k :=
  ⟨x.val/8,by have := x.isLt; omega⟩
def tag {k : Nat} (x : Fin (8*k)) : Tag := ⟨x.val%8,Nat.mod_lt _ (by decide)⟩
def label {k : Nat} (i : Fin k) (e : Tag) : Fin (8*k) :=
  ⟨8*i.val+e.val,by have := i.isLt; have := e.isLt; omega⟩

@[simp] theorem column_label {k : Nat} (i : Fin k) (e : Tag) : column (label i e)=i := by
  apply Fin.ext; dsimp [column,label]; have := e.isLt; omega
@[simp] theorem tag_label {k : Nat} (i : Fin k) (e : Tag) : tag (label i e)=e := by
  apply Fin.ext; dsimp [tag,label]; have := e.isLt; omega
@[simp] theorem label_column_tag {k : Nat} (x : Fin (8*k)) : label (column x) (tag x)=x := by
  apply Fin.ext; dsimp [label,column,tag]; omega

def good {k : Nat} (r : Nat) (x : Fin (8*k)) : Prop :=
  Present (holes r) (column x,sourceType (tag x)) ∧ ¬excluded (holes r) (column x) (tag x)
instance {k : Nat} (r : Nat) (x : Fin (8*k)) : Decidable (good r x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def lostAt (d : Nat) (e : Tag) : Prop :=
  (d=0 ∧ (e=0 ∨ e=1 ∨ e=2 ∨ e=3)) ∨
  (d=1 ∧ (e=0 ∨ e=1 ∨ e=5)) ∨ (d=2 ∧ (e=1 ∨ e=2))
instance (d : Nat) (e : Tag) : Decidable (lostAt d e) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def lossOffset (q : Fin 9) : Nat := if q.val<4 then 0 else if q.val<7 then 1 else 2
def lossTag (q : Fin 9) : Tag :=
  match q.val with
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3
  | 4 => 0 | 5 => 1 | 6 => 5 | 7 => 1 | _ => 2

theorem loss_small (q : Fin 9) : lossOffset q<3 := by
  unfold lossOffset; split <;> (first | omega | (split <;> omega))
theorem loss_valid (q : Fin 9) : lostAt (lossOffset q) (lossTag q) := by
  revert q; decide +kernel
theorem loss_unique (a b : Fin 9)
    (offset : lossOffset a=lossOffset b) (tags : lossTag a=lossTag b) : a=b := by
  revert a b; decide +kernel
theorem loss_image (d : Fin 3) (e : Tag) :
    lostAt d.val e ↔ ∃ q : Fin 9, lossOffset q=d.val ∧ lossTag q=e := by
  revert d e; decide +kernel
theorem source_four (e : Tag) : sourceType e=4 ↔ e=2 ∨ e=3 := by
  revert e; decide +kernel

theorem bad_iff {k r : Nat} (hk : 20≤k) (hr : r≤5) (x : Fin (8*k)) :
    ¬good r x ↔ ∃ j : Fin r, ∃ d : Fin 3,
      (column x).val=3*j.val+d.val ∧ lostAt d.val (tag x) := by
  constructor
  · intro bad
    by_cases present : Present (holes r) (column x,sourceType (tag x))
    · have blocked : excluded (holes r) (column x) (tag x) := by
        apply Classical.byContradiction; intro no; exact bad ⟨present,no⟩
      obtain ⟨h,⟨j,hj,hcol⟩,zero | one | two⟩ := blocked
      · refine ⟨⟨j.val,hj⟩,0,?_,Or.inl ⟨rfl,?_⟩⟩
        · have eq := congrArg Fin.val zero.1
          change (column x).val=h.val at eq
          change (column x).val=3*j.val
          omega
        · exact zero.2.elim Or.inl (fun h => Or.inr (Or.inl h))
      · refine ⟨⟨j.val,hj⟩,1,?_,Or.inr (Or.inl ⟨rfl,one.2⟩)⟩
        have eq := congrArg Fin.val one.1
        change (column x).val=(h.val+1)%k at eq
        rw [hcol,Nat.mod_eq_of_lt (by have := j.isLt; omega)] at eq
        exact eq
      · refine ⟨⟨j.val,hj⟩,2,?_,Or.inr (Or.inr ⟨rfl,two.2⟩)⟩
        have eq := congrArg Fin.val two.1
        change (column x).val=(h.val+2)%k at eq
        rw [hcol,Nat.mod_eq_of_lt (by have := j.isLt; omega)] at eq
        exact eq
    · have typ : sourceType (tag x)=4 := by
        apply Classical.byContradiction; intro no; exact present (Or.inl no)
      have hit : holes r (column x) := by
        apply Classical.byContradiction; intro no; exact present (Or.inr no)
      obtain ⟨j,hj,col⟩ := hit
      refine ⟨⟨j.val,hj⟩,0,by simpa using col,Or.inl ⟨rfl,?_⟩⟩
      exact Or.inr (Or.inr ((source_four _).mp typ))
  · rintro ⟨j,d,col,lost⟩ ⟨present,allowed⟩
    let h : Fin k := ⟨3*j.val,by have := j.isLt; omega⟩
    have hit : holes r h := ⟨⟨j.val,by have := j.isLt; omega⟩,j.isLt,rfl⟩
    have shifted (v : Nat) (small : v<3) (eq : d.val=v) : column x=shift h v := by
      apply Fin.ext
      change (column x).val=(3*j.val+v)%k
      rw [Nat.mod_eq_of_lt (by have := j.isLt; omega)]
      simpa only [eq] using col
    rcases lost with ⟨dz,tags⟩ | ⟨dOne,tags⟩ | ⟨dt,tags⟩
    · have same : column x=h := by simpa only [shift_zero] using shifted 0 (by decide) dz
      rcases tags with e0 | e1 | e2 | e3
      · exact allowed ⟨h,hit,Or.inl ⟨same,Or.inl e0⟩⟩
      · exact allowed ⟨h,hit,Or.inl ⟨same,Or.inr e1⟩⟩
      · have typ := (source_four _).mpr (Or.inl e2)
        exact present.elim (fun no => no typ) (fun no => no (same.symm ▸ hit))
      · have typ := (source_four _).mpr (Or.inr e3)
        exact present.elim (fun no => no typ) (fun no => no (same.symm ▸ hit))
    · exact allowed ⟨h,hit,Or.inr (Or.inl ⟨shifted 1 (by decide) dOne,tags⟩)⟩
    · exact allowed ⟨h,hit,Or.inr (Or.inr ⟨shifted 2 (by decide) dt,tags⟩)⟩

def lostLabel {k r : Nat} (hk : 20≤k) (hr : r≤5) (a : Fin (9*r)) : Fin (8*k) :=
  let q : Fin 9 := ⟨a.val%9,Nat.mod_lt _ (by decide)⟩
  label ⟨3*(a.val/9)+lossOffset q,by have := a.isLt; have := loss_small q; omega⟩ (lossTag q)

theorem lostLabel_injective {k r : Nat} (hk : 20≤k) (hr : r≤5) (a b : Fin (9*r))
    (same : lostLabel hk hr a=lostLabel hk hr b) : a=b := by
  let qa : Fin 9 := ⟨a.val%9,Nat.mod_lt _ (by decide)⟩
  let qb : Fin 9 := ⟨b.val%9,Nat.mod_lt _ (by decide)⟩
  have col := congrArg (fun x => (column x).val) same
  have tags := congrArg tag same
  simp only [lostLabel,column_label,tag_label] at col tags
  have smalla := loss_small qa
  have smallb := loss_small qb
  change 3*(a.val/9)+lossOffset qa=3*(b.val/9)+lossOffset qb at col
  have offsets : lossOffset qa=lossOffset qb := by omega
  have qsame := congrArg Fin.val (loss_unique qa qb offsets tags)
  apply Fin.ext
  change a.val%9=b.val%9 at qsame
  omega

theorem bad_image {k r : Nat} (hk : 20≤k) (hr : r≤5) (x : Fin (8*k)) :
    ¬good r x ↔ ∃ a : Fin (9*r), lostLabel hk hr a=x := by
  rw [bad_iff hk hr]
  constructor
  · rintro ⟨j,d,col,lost⟩
    obtain ⟨q,offset,tags⟩ := (loss_image d (tag x)).mp lost
    let a : Fin (9*r) := ⟨9*j.val+q.val,by have := j.isLt; have := q.isLt; omega⟩
    refine ⟨a,?_⟩
    have div : a.val/9=j.val := by dsimp [a]; have := q.isLt; omega
    have rem : (⟨a.val%9,Nat.mod_lt _ (by decide)⟩ : Fin 9)=q := by
      apply Fin.ext; dsimp [a]; have := q.isLt; omega
    unfold lostLabel
    simp only [div,rem,offset,tags]
    have cols : (⟨3*j.val+d.val,by have := j.isLt; have := d.isLt; omega⟩ : Fin k)=column x :=
      Fin.ext col.symm
    rw [cols,label_column_tag]
  · rintro ⟨a,rfl⟩
    let q : Fin 9 := ⟨a.val%9,Nat.mod_lt _ (by decide)⟩
    refine ⟨⟨a.val/9,by have := a.isLt; omega⟩,⟨lossOffset q,loss_small q⟩,?_,?_⟩
    · simp only [lostLabel,column_label]; rfl
    · simpa only [lostLabel,tag_label] using loss_valid q

theorem good_count {k r : Nat} (hk : 20≤k) (hr : r≤5) : card (good (k:=k) r)=8*k-9*r := by
  have gone : card (fun x : Fin (8*k) => ¬good r x)=9*r :=
    card_image (lostLabel hk hr) _ (lostLabel_injective hk hr) (bad_image hk hr)
  have split := card_partition (fun _ : Fin (8*k) => True) (good r)
  have keep : card (fun x : Fin (8*k) => True ∧ good r x)=card (good (k:=k) r) :=
    card_congr (fun _ => by simp)
  have drop : card (fun x : Fin (8*k) => True ∧ ¬good r x)=9*r := by
    rw [card_congr (P:=fun x : Fin (8*k) => True ∧ ¬good r x)
      (Q:=fun x => ¬good r x) (fun _ => by simp)]
    exact gone
  rw [keep,drop,card_true] at split
  omega

private theorem tag_shape (e f : Tag)
    (sources : sourceType e=sourceType f) (targets : targetType e=targetType f) :
    e=f ∨ (e=5 ∧ f=6) ∨ (e=6 ∧ f=5) := by
  revert e f; decide +kernel

private theorem offsets_different {k a b : Nat} (i : Fin k)
    (ha : a<k) (hb : b<k) (different : a≠b) : shift i a≠shift i b := by
  intro equal
  have same := (shift_eq_iff i a b).mp equal
  rw [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at same
  exact different same

theorem tag_injective {k : Nat} (hk : 20≤k) (i : Fin k) (e f : Tag)
    (sources : sourceType e=sourceType f) (targets : targetRaw i e=targetRaw i f) : e=f := by
  have typ := congrArg Prod.snd targets
  have col := congrArg Prod.fst targets
  rcases tag_shape e f sources typ with same | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact same
  · change shift i 3=shift i (k-3) at col
    exact False.elim (offsets_different i (by omega) (by omega) (by omega) col)
  · change shift i (k-3)=shift i 3 at col
    exact False.elim (offsets_different i (by omega) (by omega) (by omega) col)

@[simp] private theorem tagval3 : (3:Tag).val=3 := rfl
@[simp] private theorem tagval4 : (4:Tag).val=4 := rfl
@[simp] private theorem tagval5 : (5:Tag).val=5 := rfl
@[simp] private theorem tagval6 : (6:Tag).val=6 := rfl
@[simp] private theorem tagval7 : (7:Tag).val=7 := rfl

theorem target_ne_first {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (i : Fin k) (e : Tag) : targetRaw i e≠firstRaw H (i,sourceType e) := by
  intro equal
  rcases tag_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [targetRaw,targetColumn,targetType,sourceType,firstRaw] at equal
  all_goals first
    | exact shift_ne_self i (d:=k-3) (by omega) (by omega) equal.1
    | exact shift_ne_self i (d:=3) (by omega) (by omega) equal.1
    | exact offsets_different i (a:=k-2) (b:=1) (by omega) (by omega) (by omega) equal

theorem target_ne_second {k : Nat} (hk : 20≤k) (H : Fin k → Prop) [DecidablePred H]
    (i : Fin k) (e : Tag) : targetRaw i e≠secondRaw H (i,sourceType e) := by
  intro equal
  rcases tag_cases e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [targetRaw,targetColumn,targetType,sourceType,secondRaw] at equal
  all_goals first
    | (split at equal <;> simp_all)
    | exact offsets_different i (a:=3) (b:=k-1) (by omega) (by omega) (by omega) equal
    | exact offsets_different i (a:=k-3) (b:=k-1) (by omega) (by omega) (by omega) equal

def labelSource {k : Nat} (r : Nat) (x : Fin (8*k)) : Vertex (holes (k:=k) r) :=
  if h : Present (holes r) (column x,sourceType (tag x)) then
    ⟨(column x,sourceType (tag x)),h⟩
  else ⟨(column x,0),Or.inl (show (0:Fin 6)≠4 by decide)⟩

theorem labelSource_raw {k : Nat} (r : Nat) (x : Fin (8*k)) (allowed : good r x) :
    (labelSource r x).val=(column x,sourceType (tag x)) := by
  simp only [labelSource,dif_pos allowed.1]

def labelPair {k : Nat} (r : Nat) (x : Fin (8*k)) :
    Fin (vertices k r).length × Fin (vertices k r).length :=
  (fromVertex (labelSource r x),fromVertex (target (holes r) (column x) (tag x)))

theorem labelPair_injective {k r : Nat} (hk : 20≤k) (x y : Fin (8*k))
    (hx : good r x) (hy : good r y) (same : labelPair r x=labelPair r y) : x=y := by
  have sources := congrArg (fun p => (toVertex p.1).val) same
  have targets := congrArg (fun p => (toVertex p.2).val) same
  simp only [labelPair,to_from,labelSource_raw r x hx,labelSource_raw r y hy] at sources
  have col : column x=column y := congrArg Prod.fst sources
  have typ : sourceType (tag x)=sourceType (tag y) := congrArg Prod.snd sources
  simp only [labelPair,to_from] at targets
  change targetRaw (column x) (tag x)=targetRaw (column y) (tag y) at targets
  rw [←col] at targets
  have tags := tag_injective hk (column x) (tag x) (tag y) typ targets
  rw [←label_column_tag x,←label_column_tag y,col,tags]

def optionalGraph (k r : Nat) : Graph (Fin (vertices k r).length) :=
  fun s t => optional (holes r) (toVertex s) (toVertex t)
def upperGraph (k r : Nat) : Graph (Fin (vertices k r).length) :=
  fun s t => LowBandGraph.upper (holes r) (toVertex s) (toVertex t)

theorem optional_image {k r : Nat} (s t : Fin (vertices k r).length) :
    optionalGraph k r s t ↔ ∃ x : Fin (8*k), good r x ∧ labelPair r x=(s,t) := by
  constructor
  · rintro ⟨e,typ,allowed,dest⟩
    let x := label (toVertex s).val.1 e
    have present : Present (holes r) ((toVertex s).val.1,sourceType e) := by
      rw [←typ]
      exact (toVertex s).property
    have hx : good r x := by
      change Present (holes r) (column x,sourceType (tag x)) ∧ ¬excluded (holes r) (column x) (tag x)
      simpa only [x,column_label,tag_label] using And.intro present allowed
    refine ⟨x,hx,?_⟩
    apply Prod.ext
    · change fromVertex (labelSource r x)=s
      have source : labelSource r x=toVertex s := by
        apply Subtype.ext
        rw [labelSource_raw r x hx]
        simp only [x,column_label,tag_label,←typ]
      rw [source,from_to]
    · change fromVertex (target (holes r) (column x) (tag x))=t
      simp only [x,column_label,tag_label]
      rw [←dest,from_to]
  · rintro ⟨x,hx,equal⟩
    have src := congrArg Prod.fst equal
    have dst := congrArg Prod.snd equal
    change fromVertex (labelSource r x)=s at src
    change fromVertex (target (holes r) (column x) (tag x))=t at dst
    rw [←src,←dst]
    unfold optionalGraph
    simp only [to_from]
    have raw := labelSource_raw r x hx
    refine ⟨tag x,congrArg Prod.snd raw,?_,?_⟩
    · simpa only [raw] using hx.2
    · simp only [raw]

private theorem arcCount_image {m n : Nat} (P : Fin m → Prop)
    (f : Fin m → Fin n × Fin n) (E : Graph (Fin n))
    (injective : ∀ x y, P x → P y → f x=f y → x=y)
    (image : ∀ s t, E s t ↔ ∃ x, P x ∧ f x=(s,t)) : arcCount E=card P := by
  classical
  have nd : ((elems P).map f).Nodup := by
    apply List.pairwise_map.mpr
    apply (elems_nodup P).imp_of_mem
    intro x y hx hy different equal
    exact different (injective x y (mem_elems.mp hx) (mem_elems.mp hy) equal)
  have perm := (List.perm_ext_iff_of_nodup
    ((DenseZero.allPairs_nodup n).filter (fun p => decide (E p.1 p.2))) nd).mpr (fun p => by
      simp only [List.mem_filter,GraphRelabeling.allPairs_mem,true_and,decide_eq_true_eq,
        List.mem_map,mem_elems]
      exact image p.1 p.2)
  rw [arcCount_eq]
  simpa only [List.length_map,card] using perm.length_eq

theorem optional_arcs {k r : Nat} (hk : 20≤k) (hr : r≤5) :
    arcCount (optionalGraph k r)=8*k-9*r := by
  rw [arcCount_image (good r) (labelPair r) (optionalGraph k r)
    (labelPair_injective hk) optional_image]
  exact good_count hk hr

theorem optional_disjoint {k r : Nat} (hk : 20≤k) (s t : Fin (vertices k r).length)
    (base : graph k r s t) (opt : optionalGraph k r s t) : False := by
  obtain ⟨e,typ,_,dest⟩ := opt
  have source : (toVertex s).val=((toVertex s).val.1,sourceType e) := Prod.ext rfl typ
  rcases base with first | second
  · have raw := congrArg Subtype.val (dest.symm.trans first)
    change targetRaw (toVertex s).val.1 e=firstRaw (holes r) (toVertex s).val at raw
    rw [source] at raw
    exact target_ne_first hk (holes r) (toVertex s).val.1 e raw
  · have raw := congrArg Subtype.val (dest.symm.trans second)
    change targetRaw (toVertex s).val.1 e=secondRaw (holes r) (toVertex s).val at raw
    rw [source] at raw
    exact target_ne_second hk (holes r) (toVertex s).val.1 e raw

theorem upper_arcs {k r : Nat} (hk : 20≤k) (hr : r≤5) :
    arcCount (upperGraph k r)=20*k-11*r := by
  have split := SparseSupport.arcs_union (E:=graph k r) (F:=optionalGraph k r)
    (optional_disjoint hk)
  change arcCount (upperGraph k r)=arcCount (graph k r)+arcCount (optionalGraph k r) at split
  rw [SixTypeCounts.graph_arcs (by omega),optional_arcs hk hr] at split
  have size := vertices_length (k:=k) (by omega) hr
  omega

theorem upper_loopless (k r : Nat) : Loopless (upperGraph k r) := by
  intro s arrow
  exact LowBandGraph.upper_loopless (holes r) (toVertex s) arrow

theorem graph_subset (k r : Nat) : RobustTwoMove.Subgraph (graph k r) (upperGraph k r) :=
  fun _ _ h => Or.inl h

def liftGraph {k r : Nat} (G : Graph (Fin (vertices k r).length)) :
    Graph (Vertex (holes (k:=k) r)) := fun s t => G (fromVertex s) (fromVertex t)

def liftIso {k r : Nat} (G : Graph (Fin (vertices k r).length)) :
    GraphRelabeling.Iso G (liftGraph G) where
  toFun := toVertex
  invFun := fromVertex
  left_inv := from_to
  right_inv := to_from
  edge_iff s t := by simp only [liftGraph,from_to]

theorem delivers
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {k r : Nat} (hk : 20≤k) (hr : r≤5) :
    GuaranteedPrefix.Delivers (graph k r) (upperGraph k r) := by
  intro G lower upper s t
  have low : RobustTwoMove.Subgraph (edge (holes r)) (liftGraph G) := by
    intro a b arrow
    apply lower (fromVertex a) (fromVertex b)
    change edge (holes r) (toVertex (fromVertex a)) (toVertex (fromVertex b))
    simpa only [to_from] using arrow
  have high : RobustTwoMove.Subgraph (liftGraph G) (LowBandGraph.upper (holes r)) := by
    intro a b arrow
    have result := upper (fromVertex a) (fromVertex b) arrow
    change LowBandGraph.upper (holes r) (toVertex (fromVertex a)) (toVertex (fromVertex b)) at result
    simpa only [to_from] using result
  have result := LowBandComposition.canonical_guaranteed cert hk hr (liftGraph G)
    low high (toVertex s) (toVertex t)
  have back := (liftIso G).symm.guaranteed (toVertex s) (toVertex t) result
  simpa only [GraphRelabeling.Iso.symm,liftIso,from_to] using back

theorem maximum_at_parameters
    (cert : ∀ p, p∈LowBandCropCoverage.catalog → LowBandLocal.Certificates p)
    {k r m : Nat} (hk : 20≤k) (hr : r≤5)
    (low : 2*(6*k-r)≤m) (high : m≤20*k-11*r) :
    IsMaximum (vertices k r).length m
      ((vertices k r).length*((vertices k r).length-1)-m) := by
  apply GuaranteedPrefix.maximum (graph k r) (upperGraph k r) (graph_subset k r)
    (upper_loopless k r) (delivers cert hk hr)
  · have arrows := SixTypeCounts.graph_arcs (r:=r) (by omega : 15≤k)
    have size := vertices_length (k:=k) (by omega) hr
    omega
  · rw [upper_arcs hk hr]
    exact high

#print axioms optional_arcs
#print axioms upper_arcs
#print axioms delivers
#print axioms maximum_at_parameters
end Delivery.LowBandCounts
