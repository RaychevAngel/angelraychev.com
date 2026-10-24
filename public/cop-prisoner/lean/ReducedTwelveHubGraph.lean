import TwelveHubGraph

/-! The reduced twelve-hub envelope. A fixed four-rank interface and the
antichain safe-entry lemma give five actual messenger moves. The full
family's stronger three-move theorem is retained separately. -/
namespace Delivery.ReducedTwelveHubGraph
open FiniteGame Extremal RobustTwoMove DenseCombinatorics
open TwelveHubGraph (Vertex hubRel hubArrow guideCode omitted guideIndex sourceMoveRaw
  isHub isGuide isBulk assigned)

def outlet (h : Fin 12) : Prop := h.val∈[1,2,3,4,6,7,9,10]
def access (h : Fin 12) : Prop := h.val∈[1,4,7,9]
def bulkSafe (h : Fin 12) : Prop := h.val∈[0,2,3]
instance (h : Fin 12) : Decidable (outlet h) := inferInstanceAs (Decidable (_∈_))
instance (h : Fin 12) : Decidable (access h) := inferInstanceAs (Decidable (_∈_))
instance (h : Fin 12) : Decidable (bulkSafe h) := inferInstanceAs (Decidable (_∈_))

def base {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) : Graph (Vertex g b)
  | .inl (.inl h), .inl (.inl t) => hubArrow h t
  | .inl (.inl h), .inl (.inr _) => outlet h
  | .inl (.inl h), .inr _ => outlet h
  | .inl (.inr j), .inl (.inl h) => ¬omitted (guideIndex (by omega) j) h
  | .inr _, .inl (.inl h) => access h
  | .inr x, .inl (.inr j) => J x j
  | _, _ => False

def extra {g b : Nat} : Graph (Vertex g b)
  | .inl (.inl h), .inr _ => ¬outlet h
  | .inl (.inr _), .inr _ => True
  | .inr _, .inl (.inl h) => ¬bulkSafe h ∧ ¬access h
  | .inr x, .inr y => x≠y
  | _, _ => False

def upper {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) : Graph (Vertex g b) :=
  fun s t => base hg J s t ∨ extra s t

theorem subset {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) :
    Subgraph (base hg J) (upper hg J) := fun _ _ h => Or.inl h

theorem loopless {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop) : Loopless (upper hg J) := by
  rintro ((h|j)|x) <;> simp [upper,base,extra,hubArrow,hubRel]

def sourceMove (s : Fin 19) (h : Fin 12) : Prop := sourceMoveRaw s.val h.val
def direct (s : Fin 19) (t : Fin 13) : Prop :=
  if t.val<12 then sourceMoveRaw s.val t.val else s.val∈[1,2,3,4,6,7,9,10]
def copSafe (c : Fin 20) (h : Fin 12) : Prop :=
  if c.val<12 then h.val≠c.val ∧ ¬hubRel c.val h.val
  else if c.val<19 then h.val∈guideCode (c.val-12)
  else bulkSafe h

instance (s : Fin 19) (h : Fin 12) : Decidable (sourceMove s h) := by unfold sourceMove; infer_instance
instance (s : Fin 19) (t : Fin 13) : Decidable (direct s t) := by unfold direct; infer_instance
instance (c : Fin 20) (h : Fin 12) : Decidable (copSafe c h) := by unfold copSafe; infer_instance

def interfaceRank (s : Fin 19) (t : Fin 13) : Nat :=
  if t.val<12 then if s.val=t.val then 0 else if direct s t then 1 else 2
  else if s.val<12 then if s.val∈[1,2,3,4,6,7,9,10] then 1
    else if s.val=0 ∨ s.val=5 then 2 else 3
  else if s.val∈[14,15,16] then 3 else 4

def hubCode (h : Fin 12) : Fin 19 := ⟨h.val,by have := h.isLt; omega⟩

theorem interface_checked (s : Fin 19) (t : Fin 13) (c : Fin 20)
    (distinct : s.val≠c.val) (nonterminal : ¬(s.val=t.val ∧ t.val<12))
    (missing : ¬direct s t) :
    ∃ h : Fin 12, sourceMove s h ∧ copSafe c h ∧
      interfaceRank (hubCode h) t < interfaceRank s t := by
  revert s t c
  decide +kernel

theorem rank_bound (s : Fin 19) (t : Fin 13) : interfaceRank s t≤4 := by
  revert s t
  decide +kernel

theorem rank_direct (s : Fin 19) (t : Fin 13) (arrow : direct s t) : 1≤interfaceRank s t := by
  revert s t
  decide +kernel

theorem safe_disjoint (h : Fin 12) : bulkSafe h → ¬access h := by
  revert h
  decide +kernel

theorem outlet_entry (c : Fin 12) (member : outlet c) :
    ∃ h : Fin 12, access h ∧ ¬Legal hubArrow c h := by
  revert c
  change ∀ c, outlet c → ∃ h, access h ∧ ¬(c=h ∨ hubArrow c h)
  decide +kernel

def sourceCode {g : Nat} (hg : g≤7) : Fin 12 ⊕ Fin g → Fin 19
  | .inl h => hubCode h
  | .inr j => ⟨12+j.val,by have := j.isLt; omega⟩
def targetCode {g b : Nat} : Vertex g b → Fin 13 := TwelveHubGraph.targetCode
def copCode {g b : Nat} (hg : g≤7) : Vertex g b → Fin 20
  | .inl s => ⟨(sourceCode hg s).val,by have := (sourceCode hg s).isLt; omega⟩
  | .inr _ => ⟨19,by decide⟩

def rank {g b : Nat} (hg : g≤7) (t : Vertex g b) : Vertex g b → Nat
  | .inl s => interfaceRank (sourceCode hg s) (targetCode t)
  | .inr _ => 5

theorem source_lift {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (s : Fin 12 ⊕ Fin g) (h : Fin 12) :
    sourceMove (sourceCode hg s) h ↔ base hg J (.inl s) (.inl (.inl h)) := by
  rcases s with s|j
  · simp [sourceMove,sourceMoveRaw,sourceCode,hubCode,base,hubArrow,s.isLt]
  · have := j.isLt
    simp [sourceMove,sourceMoveRaw,sourceCode,base,guideIndex,omitted,show ¬12+j.val<12 by omega]

theorem direct_lift {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (s : Fin 12 ⊕ Fin g) (t : Vertex g b) :
    direct (sourceCode hg s) (targetCode t) ↔ base hg J (.inl s) t := by
  rcases t with (t|j)|x
  · simp only [direct,targetCode,TwelveHubGraph.targetCode,Fin.val_mk,t.isLt,if_pos]
    exact source_lift hg J s t
  · rcases s with s|j
    · simp [direct,sourceCode,hubCode,targetCode,TwelveHubGraph.targetCode,base,outlet]
    · have := j.isLt
      simp [direct,sourceCode,targetCode,TwelveHubGraph.targetCode,base] <;> omega
  · rcases s with s|j
    · simp [direct,sourceCode,hubCode,targetCode,TwelveHubGraph.targetCode,base,outlet]
    · have := j.isLt
      simp [direct,sourceCode,targetCode,TwelveHubGraph.targetCode,base] <;> omega

theorem safe_lift {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (c : Vertex g b) (h : Fin 12) (safe : copSafe (copCode hg c) h) :
    ¬Legal (upper hg J) c (.inl (.inl h)) := by
  rcases c with (c|j)|x
  · simp only [copSafe,copCode,sourceCode,hubCode,Fin.val_mk,c.isLt,if_pos] at safe
    rintro (same|arrow)
    · have eq := congrArg (fun z : Vertex g b => match z with | .inl (.inl v) => v.val | _ => 12) same
      exact safe.1 eq.symm
    · exact safe.2 (arrow.elim id False.elim)
  · have small : 12+j.val<19 := by have := j.isLt; omega
    have big : ¬12+j.val<12 := by omega
    simp only [copSafe,copCode,sourceCode,Fin.val_mk,big,small,if_pos,Nat.add_sub_cancel_left] at safe
    rintro (same|arrow)
    · cases same
    · exact arrow.elim (fun no => no safe) False.elim
  · simp only [copSafe,copCode,Fin.val_mk,show ¬(19:Nat)<12 by decide,
      show ¬(19:Nat)<19 by decide] at safe
    rintro (same|arrow)
    · cases same
    · exact arrow.elim (safe_disjoint h safe) (fun no => no.1 safe)

def isOutlet {g b : Nat} : Vertex g b → Prop
  | .inl (.inl h) => outlet h | _ => False

def entryData {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j) :
    GuideAttachment.EntryData (base hg J) (upper hg J) where
  hub := isHub
  guide := isGuide
  bulk := isBulk
  outlet := isOutlet
  assigned := assigned J
  cover := by rintro ((h|j)|x) <;> simp [isHub,isGuide,isBulk]
  outsideBulk := by rintro ((h|j)|x) <;> simp [isHub,isGuide,isBulk]
  assignedGuide := by rintro ((h|j)|x) ((k|l)|y) <;> simp [isBulk,assigned,isGuide]
  assignedMove := by rintro ((h|j)|x) ((k|l)|y) <;> simp [isBulk,assigned,base]
  twoGuides := by
    rintro ((h|j)|x) bulk c
    · contradiction
    · contradiction
    obtain ⟨j,l,first,last,different⟩ := two x
    by_cases same : (Sum.inl (Sum.inr j) : Vertex g b)=c
    · refine ⟨.inl (.inr l),last,?_⟩
      intro eq
      have equal : l=j := Sum.inr.inj (Sum.inl.inj (eq.trans same.symm))
      exact different equal.symm
    · exact ⟨.inl (.inr j),first,same⟩
  incomparable := by
    rintro ((h|j)|x) ((k|l)|y) hx hy distinct
    all_goals try contradiction
    obtain ⟨j,yes,no⟩ := difference x y (fun eq => distinct (congrArg Sum.inr eq))
    exact ⟨.inl (.inr j),yes,no⟩
  outletEntry := by
    rintro ((h|j)|x) ((c|l)|y) hx hc member
    all_goals try contradiction
    obtain ⟨z,present,safe⟩ := outlet_entry c member
    refine ⟨.inl (.inl z),trivial,present,?_⟩
    rintro (same|arrow)
    · exact safe (Or.inl (Sum.inl.inj (Sum.inl.inj same)))
    · exact safe (Or.inr (arrow.elim id False.elim))
  otherHubSafe := by
    rintro ((h|j)|x) ((k|l)|y) hc no hz legal
    all_goals try contradiction
    rcases legal with same|edge
    · cases same
    · exact edge.elim no False.elim
  otherGuideSafe := by
    rintro ((h|j)|x) ((k|l)|y) hc hz different legal
    all_goals try contradiction
    rcases legal with same|edge
    · exact different same.symm
    · exact edge.elim False.elim False.elim
  bulkGuide := by
    rintro ((h|j)|x) ((k|l)|y) hc hz legal
    all_goals try contradiction
    rcases legal with same|edge
    · cases same
    · exact edge.elim id False.elim

theorem source_ranks {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j) (t : Vertex g b) :
    RobustLayers.SourceRanks (base hg J) (upper hg J) t (rank hg t) := by
  intro s nonterminal
  rcases s with s|x
  · by_cases arrow : base hg J (.inl s) t
    · exact Or.inl ⟨arrow,rank_direct _ _ ((direct_lift hg J s t).mpr arrow)⟩
    apply Or.inr
    intro c initial
    have distinct : (sourceCode hg s).val≠(copCode hg c).val := by
      intro eq
      apply initial
      rcases c with (h|j)|x <;> rcases s with s|i <;>
        simp [sourceCode,copCode,hubCode] at eq ⊢
      all_goals first | exact Fin.ext eq.symm | (have := s.isLt; omega) | (have := i.isLt; omega)
    have notTerminal : ¬((sourceCode hg s).val=(targetCode t).val ∧ (targetCode t).val<12) := by
      rintro ⟨eq,lt⟩
      apply nonterminal
      rcases t with (h|j)|x <;> rcases s with s|i <;>
        simp [sourceCode,targetCode,TwelveHubGraph.targetCode,hubCode] at eq lt ⊢
      all_goals first | exact Fin.ext eq | omega
    obtain ⟨h,first,safe,smaller⟩ := interface_checked (sourceCode hg s) (targetCode t) (copCode hg c)
      distinct notTerminal (fun direct => arrow ((direct_lift hg J s t).mp direct))
    exact ⟨.inl (.inl h),(source_lift hg J s h).mp first,safe_lift hg J c h safe,smaller⟩
  · apply Or.inr
    intro c initial
    obtain ⟨z,inside,move,safe⟩ := GuideAttachment.safe_entry (entryData hg J two difference)
      (x:=.inr x) (by simp [entryData,isHub,isGuide]) initial
    refine ⟨z,move,safe,?_⟩
    rcases z with z|y
    · exact Nat.lt_of_le_of_lt (rank_bound _ _) (by change 4<5; decide)
    · exact False.elim (inside.elim id id)

theorem rank_le {g b : Nat} (hg : g≤7) (s t : Vertex g b) : rank hg t s≤5 := by
  rcases s with s|x
  · exact Nat.le_trans (rank_bound _ _) (by decide)
  · exact Nat.le_refl 5

theorem envelope_universal {g b : Nat} (hg : g≤7) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j)
    (G : Graph (Vertex g b)) (lower : Subgraph (base hg J) G)
    (bound : Subgraph G (upper hg J)) (s t : Vertex g b) : Universal G t 5 s :=
  universal_mono (RobustLayers.ranked_envelope_universal lower bound
    (source_ranks hg J two difference t) s) (rank_le hg s t)

#print axioms source_ranks
#print axioms envelope_universal
end Delivery.ReducedTwelveHubGraph
