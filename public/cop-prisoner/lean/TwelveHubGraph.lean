import GuideAttachment
import GuaranteedPrefix
import ComplementarySum

/-! The full twelve-hub envelope, with arbitrary antichain assignments of
bulk vertices to guides. All nonterminal interface moves stay at hubs. -/
namespace Delivery.TwelveHubGraph
open FiniteGame Extremal RobustTwoMove DenseCombinatorics

abbrev Vertex (g b : Nat) := (Fin 12 ⊕ Fin g) ⊕ Fin b

def hubRel (s t : Nat) : Prop := s≠t ∧ ¬
  ((s<6 ∧ (t=6+s ∨ t=6+(s+5)%6)) ∨
   (6≤s ∧ (t=(s+4)%6 ∨ t=s%6)))
instance (s t : Nat) : Decidable (hubRel s t) := inferInstanceAs (Decidable (_ ∧ ¬_))
def hubArrow (s t : Fin 12) : Prop := hubRel s.val t.val
instance (s t : Fin 12) : Decidable (hubArrow s t) := inferInstanceAs (Decidable (hubRel _ _))

def guideCode (j : Nat) : List Nat := match j with
  | 0 => [6,8,10] | 1 => [7,9,11] | 2 => [0,3] | 3 => [1,4]
  | 4 => [2,5] | 5 => [6,9] | 6 => [7,10] | _ => [8,11]
def omitted (j : Fin 8) (h : Fin 12) : Prop := h.val∈guideCode j.val
instance (j : Fin 8) (h : Fin 12) : Decidable (omitted j h) := inferInstanceAs (Decidable (_∈_))
def access (h : Fin 12) : Prop := h.val∉[0,3,6,8,10]
instance (h : Fin 12) : Decidable (access h) := inferInstanceAs (Decidable (_∉_))
def guideIndex {g : Nat} (hg : g≤8) (j : Fin g) : Fin 8 := ⟨j.val,by have := j.isLt; omega⟩

def base {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) : Graph (Vertex g b)
  | .inl (.inl h), .inl (.inl t) => hubArrow h t
  | .inl (.inl _), .inl (.inr _) => True
  | .inl (.inl _), .inr _ => True
  | .inl (.inr j), .inl (.inl h) => ¬omitted (guideIndex hg j) h
  | .inr _, .inl (.inl h) => access h
  | .inr x, .inl (.inr j) => J x j
  | _, _ => False

def extra {g b : Nat} : Graph (Vertex g b)
  | .inl (.inr _), .inr _ => True
  | .inr x, .inr y => x≠y
  | _, _ => False

def upper {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) : Graph (Vertex g b) :=
  fun s t => base hg J s t ∨ extra s t

theorem subset {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) :
    Subgraph (base hg J) (upper hg J) := fun _ _ h => Or.inl h

theorem loopless {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop) : Loopless (upper hg J) := by
  rintro ((h|j)|x) <;> simp [upper,base,extra,hubArrow,hubRel]

def sourceMoveRaw (s h : Nat) : Prop :=
  if s<12 then hubRel s h else h∉guideCode (s-12)
def sourceMove (s : Fin 20) (h : Fin 12) : Prop := sourceMoveRaw s.val h.val
def lastMove (h : Fin 12) (t : Fin 13) : Prop :=
  if t.val<12 then hubRel h.val t.val else True
def direct (s : Fin 20) (t : Fin 13) : Prop :=
  if t.val<12 then sourceMoveRaw s.val t.val else s.val<12
def copSafe (c : Fin 21) (h : Fin 12) : Prop :=
  if c.val<12 then h.val≠c.val ∧ ¬hubRel c.val h.val
  else if c.val<20 then h.val∈guideCode (c.val-12)
  else ¬access h

instance (s h : Nat) : Decidable (sourceMoveRaw s h) := by unfold sourceMoveRaw; infer_instance
instance (s : Fin 20) (h : Fin 12) : Decidable (sourceMove s h) := by unfold sourceMove; infer_instance
instance (h : Fin 12) (t : Fin 13) : Decidable (lastMove h t) := by unfold lastMove; infer_instance
instance (s : Fin 20) (t : Fin 13) : Decidable (direct s t) := by unfold direct; infer_instance
instance (c : Fin 21) (h : Fin 12) : Decidable (copSafe c h) := by unfold copSafe; infer_instance

/-- One fixed finite interface covers all permitted guide counts and every
bulk cop; no bulk identity or assignment is inspected by its hub witnesses. -/
theorem interface_checked (s : Fin 20) (t : Fin 13) (c : Fin 21)
    (distinct : s.val≠c.val) (nonterminal : ¬(s.val=t.val ∧ t.val<12))
    (missing : ¬direct s t) :
    ∃ h : Fin 12, sourceMove s h ∧ lastMove h t ∧ copSafe c h := by
  revert s t c
  decide +kernel

theorem outlet_entry (c : Fin 12) : ∃ h : Fin 12, access h ∧ ¬Legal hubArrow c h := by
  revert c
  change ∀ c, ∃ h, access h ∧ ¬(c=h ∨ hubArrow c h)
  decide +kernel

def sourceCode {g : Nat} (hg : g≤8) : Fin 12 ⊕ Fin g → Fin 20
  | .inl h => ⟨h.val,by have := h.isLt; omega⟩
  | .inr j => ⟨12+j.val,by have := j.isLt; omega⟩
@[simp] private theorem value12 : (12 : Fin 13).val=12 := rfl
def targetCode {g b : Nat} : Vertex g b → Fin 13
  | .inl (.inl h) => ⟨h.val,by have := h.isLt; omega⟩
  | _ => ⟨12,by decide⟩
def copCode {g b : Nat} (hg : g≤8) : Vertex g b → Fin 21
  | .inl s => ⟨(sourceCode hg s).val,by have := (sourceCode hg s).isLt; omega⟩
  | .inr _ => ⟨20,by decide⟩

theorem source_lift {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (s : Fin 12 ⊕ Fin g) (h : Fin 12) :
    sourceMove (sourceCode hg s) h ↔ base hg J (.inl s) (.inl (.inl h)) := by
  rcases s with s|j
  · simp [sourceMove,sourceMoveRaw,sourceCode,base,hubArrow,s.isLt]
  · have := j.isLt
    simp [sourceMove,sourceMoveRaw,sourceCode,base,guideIndex,omitted,show ¬12+j.val<12 by omega]

theorem last_lift {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (h : Fin 12) (t : Vertex g b) :
    lastMove h (targetCode t) ↔ base hg J (.inl (.inl h)) t := by
  rcases t with (t|j)|x <;> simp [lastMove,targetCode,base,hubArrow]

theorem direct_lift {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (s : Fin 12 ⊕ Fin g) (t : Vertex g b) :
    direct (sourceCode hg s) (targetCode t) ↔ base hg J (.inl s) t := by
  rcases t with (t|j)|x
  · simp only [direct,targetCode,Fin.val_mk,t.isLt,if_pos]
    exact source_lift hg J s t
  · rcases s with s|j <;> simp [direct,sourceCode,targetCode,base]
  · rcases s with s|j <;> simp [direct,sourceCode,targetCode,base]

theorem safe_lift {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (c : Vertex g b) (h : Fin 12) (safe : copSafe (copCode hg c) h) :
    ¬Legal (upper hg J) c (.inl (.inl h)) := by
  rcases c with (c|j)|x
  · simp only [copSafe,copCode,sourceCode,Fin.val_mk,c.isLt,if_pos] at safe
    rintro (same|arrow)
    · have eq := congrArg (fun z : Vertex g b => match z with | .inl (.inl v) => v.val | _ => 12) same
      exact safe.1 eq.symm
    · exact safe.2 (arrow.elim id False.elim)
  · have small : 12+j.val<20 := by have := j.isLt; omega
    have big : ¬12+j.val<12 := by omega
    simp only [copSafe,copCode,sourceCode,Fin.val_mk,big,small,if_pos,Nat.add_sub_cancel_left] at safe
    rintro (same|arrow)
    · cases same
    · exact arrow.elim (fun no => no safe) False.elim
  · simp only [copSafe,copCode,Fin.val_mk,show ¬(20:Nat)<12 by decide,
      show ¬(20:Nat)<20 by decide] at safe
    rintro (same|arrow)
    · cases same
    · exact arrow.elim safe False.elim

theorem inside_universal {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (G : Graph (Vertex g b)) (lower : Subgraph (base hg J) G)
    (bound : Subgraph G (upper hg J)) (s : Fin 12 ⊕ Fin g) (t : Vertex g b) :
    Universal G t 2 (.inl s) := by
  intro c initial
  by_cases same : (.inl s : Vertex g b)=t
  · subst t; exact Winning.delivered
  by_cases arrow : base hg J (.inl s) t
  · exact Winning.finish (Ne.symm initial) (Or.inr (lower _ _ arrow))
  have distinct : (sourceCode hg s).val≠(copCode hg c).val := by
    intro eq
    apply initial
    rcases c with (h|j)|x <;> rcases s with s|i <;>
      simp [sourceCode,copCode] at eq ⊢
    all_goals first | exact Fin.ext eq.symm | (have := s.isLt; omega) | (have := i.isLt; omega)
  have nonterminal : ¬((sourceCode hg s).val=(targetCode t).val ∧ (targetCode t).val<12) := by
    rintro ⟨eq,lt⟩
    apply same
    rcases t with (h|j)|x <;> rcases s with s|i <;>
      simp [sourceCode,targetCode] at eq lt ⊢
    all_goals first | exact Fin.ext eq | omega
  obtain ⟨h,first,last,safe⟩ := interface_checked (sourceCode hg s) (targetCode t) (copCode hg c)
    distinct nonterminal (fun direct => arrow ((direct_lift hg J s t).mp direct))
  apply DenseCounting.safe_intermediate_winning (Ne.symm initial)
    (lower _ _ ((source_lift hg J s h).mp first))
    (lower _ _ ((last_lift hg J h t).mp last))
  intro legal
  exact safe_lift hg J c h safe (legal.elim Or.inl (fun edge => Or.inr (bound _ _ edge)))

def isHub {g b : Nat} : Vertex g b → Prop
  | .inl (.inl _) => True | _ => False
def isGuide {g b : Nat} : Vertex g b → Prop
  | .inl (.inr _) => True | _ => False
def isBulk {g b : Nat} : Vertex g b → Prop
  | .inr _ => True | _ => False
def assigned {g b : Nat} (J : Fin b → Fin g → Prop) : Vertex g b → Vertex g b → Prop
  | .inr x, .inl (.inr j) => J x j | _, _ => False

def entryData {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j) :
    GuideAttachment.EntryData (base hg J) (upper hg J) where
  hub := isHub
  guide := isGuide
  bulk := isBulk
  outlet := isHub
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
    rintro ((h|j)|x) ((c|l)|y) hx hc outlet
    all_goals try contradiction
    obtain ⟨z,present,safe⟩ := outlet_entry c
    refine ⟨.inl (.inl z),trivial,present,?_⟩
    rintro (same|arrow)
    · exact safe (Or.inl (Sum.inl.inj (Sum.inl.inj same)))
    · exact safe (Or.inr (arrow.elim id False.elim))
  otherHubSafe := by intro c z hub no; exact False.elim (no hub)
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

theorem envelope_universal {g b : Nat} (hg : g≤8) (J : Fin b → Fin g → Prop)
    (two : ∀ x, ∃ j l, J x j ∧ J x l ∧ j≠l)
    (difference : ∀ x y, x≠y → ∃ j, J x j ∧ ¬J y j)
    (G : Graph (Vertex g b)) (lower : Subgraph (base hg J) G)
    (bound : Subgraph G (upper hg J)) (s t : Vertex g b) : Universal G t 3 s := by
  apply GuideAttachment.attachment_universal (entryData hg J two difference) lower bound
  rintro ((h|j)|x) inside
  · exact inside_universal hg J G lower bound (.inl h) t
  · exact inside_universal hg J G lower bound (.inr j) t
  · exact False.elim (inside.elim id id)

#print axioms inside_universal
#print axioms envelope_universal
end Delivery.TwelveHubGraph
