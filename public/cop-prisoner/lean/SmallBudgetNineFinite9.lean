import SmallRowPrefixCut
import SmallBudgetProfiles

/-! Complete row-prefix coverage for every sorted joint-degree profile on
9 vertices with 9 arrows and the stated degree restriction. -/
namespace Delivery.SmallBudgetNineFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows (a b c d e f g h i : Nat) : Rows 9 := fun v =>
  match v.val with | 0 => a | 1 => b | 2 => c | 3 => d | 4 => e | 5 => f | 6 => g | 7 => h | _ => i

def choices (d : Nat) : List Nat :=
  match d with
  | 0 => [0]
  | 1 => [1,2,4,8,16,32,64,128,256]
  | 2 => [3,5,9,17,33,65,129,257,6,10,18,34,66,130,258,12,20,36,68,132,260,24,40,72,136,264,48,80,144,272,96,160,288,192,320,384]
  | 3 => [7,11,19,35,67,131,259,13,21,37,69,133,261,25,41,73,137,265,49,81,145,273,97,161,289,193,321,385,14,22,38,70,134,262,26,42,74,138,266,50,82,146,274,98,162,290,194,322,386,28,44,76,140,268,52,84,148,276,100,164,292,196,324,388,56,88,152,280,104,168,296,200,328,392,112,176,304,208,336,400,224,352,416,448]
  | 4 => [15,23,39,71,135,263,27,43,75,139,267,51,83,147,275,99,163,291,195,323,387,29,45,77,141,269,53,85,149,277,101,165,293,197,325,389,57,89,153,281,105,169,297,201,329,393,113,177,305,209,337,401,225,353,417,449,30,46,78,142,270,54,86,150,278,102,166,294,198,326,390,58,90,154,282,106,170,298,202,330,394,114,178,306,210,338,402,226,354,418,450,60,92,156,284,108,172,300,204,332,396,116,180,308,212,340,404,228,356,420,452,120,184,312,216,344,408,232,360,424,456,240,368,432,464,480]
  | 5 => [31,47,79,143,271,55,87,151,279,103,167,295,199,327,391,59,91,155,283,107,171,299,203,331,395,115,179,307,211,339,403,227,355,419,451,61,93,157,285,109,173,301,205,333,397,117,181,309,213,341,405,229,357,421,453,121,185,313,217,345,409,233,361,425,457,241,369,433,465,481,62,94,158,286,110,174,302,206,334,398,118,182,310,214,342,406,230,358,422,454,122,186,314,218,346,410,234,362,426,458,242,370,434,466,482,124,188,316,220,348,412,236,364,428,460,244,372,436,468,484,248,376,440,472,488,496]
  | 6 => [63,95,159,287,111,175,303,207,335,399,119,183,311,215,343,407,231,359,423,455,123,187,315,219,347,411,235,363,427,459,243,371,435,467,483,125,189,317,221,349,413,237,365,429,461,245,373,437,469,485,249,377,441,473,489,497,126,190,318,222,350,414,238,366,430,462,246,374,438,470,486,250,378,442,474,490,498,252,380,444,476,492,500,504]
  | 7 => [127,191,319,223,351,415,239,367,431,463,247,375,439,471,487,251,379,443,475,491,499,253,381,445,477,493,501,505,254,382,446,478,494,502,506,508]
  | 8 => [255,383,447,479,495,503,507,509,510]
  | 9 => [511]
  | _ => []

theorem cover (d : Fin 10) : RowCover 9 d.val (choices d.val) := by
  revert d
  decide +kernel

def catalogue : List (List Nat) := []

theorem catalogue_eq : hardProfiles 9 9 5 false=catalogue := by decide +kernel

theorem hard_upper (xs : List Nat) (member : xs∈hardProfiles 9 9 5 false) :
    Upper (n:=9) (D xs.reverse) (R xs.reverse) [] 5 := by
  rw [catalogue_eq] at member
  simp only [catalogue,List.mem_cons,List.not_mem_nil,or_false] at member
theorem profile_upper (xs : List Nat) (member : xs∈profiles 9 false 9 0 9 9) :
    Upper (n:=9) (D xs.reverse) (R xs.reverse) [] 5 :=
  upper_of_hard hard_upper xs member

theorem upper (E : Graph (Fin 9)) (loops : Loopless E) (budget : arcCount E=9)
    (degree : ∀x,2≤SparseSupport.outdegree E x+SparseSupport.indegree E x)
    (regularity : ∀x,(0<SparseSupport.outdegree E x ∧ 0<SparseSupport.indegree E x) ∨
      (false=true ∧ SparseSupport.outdegree E x+SparseSupport.indegree E x=2)) : score E≤5 := by
  have od (x) : SparseSupport.outdegree E x<9 := by
    have h := SparseDeletion.row_nonadjacent_bound E loops x
    omega
  have idg (x) : SparseSupport.indegree E x<9 := by
    have h := SparseDeletion.column_nonadjacent_bound E loops x
    omega
  have td : ((List.finRange 9).map (SparseSupport.outdegree E)).sum=9 := by
    have h := SparseSupport.arc_rows E
    exact h.symm.trans budget
  have te : ((List.finRange 9).map (SparseSupport.indegree E)).sum=9 := by
    have h := SparseSupport.arc_columns E
    exact h.symm.trans budget
  have member := sorted_member (SparseSupport.outdegree E) (SparseSupport.indegree E)
    false (by decide) od idg degree regularity td te
  obtain ⟨F,⟨iso⟩,prescribed⟩ := relabel_reversed E loops (fun x => by have := idg x; omega)
  have bound := profile_upper _ member F prescribed (by intro s h; simp at h)
  rw [GraphRelabeling.score_eq iso] at bound
  exact bound

#print axioms upper
end Delivery.SmallBudgetNineFinite9
