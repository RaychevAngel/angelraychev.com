import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0413
import IrregularNine14P06C0414

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38760 : Route 9 := (fun mask => (mask,id))

def c38760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38760 : Upper (D 6) (R 6) [34,192,96,18,264] 13 := by
  apply FastRouting.sound _ _ [34,192,96,18,264] 13 (by decide) (choices 1) [1,4] r38760 c38760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24817
  · exact u24818

def b38761 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 100 28 28 291 323 387 259), lower := (rows 35 194 100 28 28 32 64 128 256), losses := [] }

theorem u38761 : Upper (D 6) (R 6) [34,192,96,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38762 : Route 9 := (fun mask => (mask,id))

def c38762 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38762 : Upper (D 6) (R 6) [34,192,96,20,257] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,257] 13 (by decide) (choices 1) [1,2,4,8] r38762 c38762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24819
  · exact u24820
  · exact u24821
  · exact u24822

def r38763 : Route 9 := (fun mask => (mask,id))

def c38763 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38763 : Upper (D 6) (R 6) [34,192,96,20,258] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,258] 13 (by decide) (choices 1) [1,4,8] r38763 c38763
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24823
  · exact u24824
  · exact u24825

def b38764 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 100 28 276 43 75 139 267), lower := (rows 35 194 100 28 276 32 64 128 256), losses := [] }

theorem u38764 : Upper (D 6) (R 6) [34,192,96,20,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38765 : Route 9 := (fun mask => (mask,id))

def c38765 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38765 : Upper (D 6) (R 6) [34,192,96,20,264] 13 := by
  apply FastRouting.sound _ _ [34,192,96,20,264] 13 (by decide) (choices 1) [1,2,4] r38765 c38765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24826
  · exact u24827
  · exact u24828

def b38766 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 28 116 116 244 372), lower := (rows 35 194 261 11 28 32 64 128 256), losses := [] }

theorem u38766 : Upper (D 6) (R 6) [34,192,257,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38767 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 52 124 92 220 348), lower := (rows 35 194 261 11 52 32 64 128 256), losses := [] }

theorem u38767 : Upper (D 6) (R 6) [34,192,257,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38768 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 261 11 56 116 84 212 340), lower := (rows 35 194 261 11 56 32 64 128 256), losses := [] }

theorem u38768 : Upper (D 6) (R 6) [34,192,257,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38769 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 84 60 124 188 316), lower := (rows 35 194 261 11 84 32 64 128 256), losses := [] }

theorem u38769 : Upper (D 6) (R 6) [34,192,257,3,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38770 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 88 52 116 180 308), lower := (rows 35 194 261 11 88 32 64 128 256), losses := [] }

theorem u38770 : Upper (D 6) (R 6) [34,192,257,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38771 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 11 112 60 92 156 284), lower := (rows 35 194 261 11 112 32 64 128 256), losses := [] }

theorem u38771 : Upper (D 6) (R 6) [34,192,257,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38772 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 22 120 120 248 376), lower := (rows 35 194 261 13 22 32 64 128 256), losses := [] }

theorem u38772 : Upper (D 6) (R 6) [34,192,257,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38773 : PairBound 9 := { available := 116, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 26 116 116 244 372), lower := (rows 35 194 261 13 26 32 64 128 256), losses := [] }

theorem u38773 : Upper (D 6) (R 6) [34,192,257,5,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38774 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 28 114 114 242 370), lower := (rows 35 194 261 13 28 32 64 128 256), losses := [] }

theorem u38774 : Upper (D 6) (R 6) [34,192,257,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38775 : PairBound 9 := { available := 90, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 52 122 90 218 346), lower := (rows 35 194 261 13 52 32 64 128 256), losses := [] }

theorem u38775 : Upper (D 6) (R 6) [34,192,257,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38776 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 56 118 86 214 342), lower := (rows 35 194 261 13 56 32 64 128 256), losses := [] }

theorem u38776 : Upper (D 6) (R 6) [34,192,257,5,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38777 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 84 58 122 186 314), lower := (rows 35 194 261 13 84 32 64 128 256), losses := [] }

theorem u38777 : Upper (D 6) (R 6) [34,192,257,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38778 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 88 54 118 182 310), lower := (rows 35 194 261 13 88 32 64 128 256), losses := [] }

theorem u38778 : Upper (D 6) (R 6) [34,192,257,5,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38778 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38779 : PairBound 9 := { available := 30, camps := [{ cop := 2, region := 8, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 13 112 62 94 158 286), lower := (rows 35 194 261 13 112 32 64 128 256), losses := [] }

theorem u38779 : Upper (D 6) (R 6) [34,192,257,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38780 : Route 9 := (fun mask => (mask,id))

def c38780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38780 : Upper (D 6) (R 6) [34,192,257,6,9] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,9] 13 (by decide) (choices 1) [4,16,64] r38780 c38780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24829
  · exact u24830
  · exact u24831

def b38781 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 194 261 14 28 113 113 241 369), lower := (rows 35 194 261 14 28 32 64 128 256), losses := [] }

theorem u38781 : Upper (D 6) (R 6) [34,192,257,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38782 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 261 14 49 124 92 220 348), lower := (rows 35 194 261 14 49 32 64 128 256), losses := [] }

theorem u38782 : Upper (D 6) (R 6) [34,192,257,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38783 : Route 9 := (fun mask => (mask,id))

def c38783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38783 : Upper (D 6) (R 6) [34,192,257,6,36] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,36] 13 (by decide) (choices 1) [1,8,16,64] r38783 c38783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24832
  · exact u24833
  · exact u24834
  · exact u24835

def r38784 : Route 9 := (fun mask => (mask,id))

def c38784 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38784 : Upper (D 6) (R 6) [34,192,257,6,40] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,40] 13 (by decide) (choices 1) [1,4,16,64] r38784 c38784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24836
  · exact u24837
  · exact u24838
  · exact u24839

def r38785 : Route 9 := (fun mask => (mask,id))

def c38785 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38785 : Upper (D 6) (R 6) [34,192,257,6,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,65] 13 (by decide) (choices 1) [4,8,16] r38785 c38785
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24840
  · exact u24841
  · exact u24842

def r38786 : Route 9 := (fun mask => (mask,id))

def c38786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38786 : Upper (D 6) (R 6) [34,192,257,6,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,68] 13 (by decide) (choices 1) [1,8,16] r38786 c38786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24843
  · exact u24844
  · exact u24845

def r38787 : Route 9 := (fun mask => (mask,id))

def c38787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38787 : Upper (D 6) (R 6) [34,192,257,6,72] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,72] 13 (by decide) (choices 1) [1,4,16] r38787 c38787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24846
  · exact u24847
  · exact u24848

def r38788 : Route 9 := (fun mask => (mask,id))

def c38788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38788 : Upper (D 6) (R 6) [34,192,257,6,96] 13 := by
  apply FastRouting.sound _ _ [34,192,257,6,96] 13 (by decide) (choices 1) [1,4,8,16] r38788 c38788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24849
  · exact u24850
  · exact u24851
  · exact u24852

def b38789 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 194 261 25 26 100 100 228 356), lower := (rows 35 194 261 25 26 32 64 128 256), losses := [] }

theorem u38789 : Upper (D 6) (R 6) [34,192,257,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38790 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6)], upper := (rows 35 194 261 25 28 102 102 230 358), lower := (rows 35 194 261 25 28 32 64 128 256), losses := [] }

theorem u38790 : Upper (D 6) (R 6) [34,192,257,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38791 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 261 25 50 108 76 204 332), lower := (rows 35 194 261 25 50 32 64 128 256), losses := [] }

theorem u38791 : Upper (D 6) (R 6) [34,192,257,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38791 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38792 : Route 9 := (fun mask => (mask,id))

def c38792 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38792 : Upper (D 6) (R 6) [34,192,257,17,36] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,36] 13 (by decide) (choices 1) [2,4,8,64] r38792 c38792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24853
  · exact u24854
  · exact u24855
  · exact u24856

def b38793 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 261 25 56 102 70 198 326), lower := (rows 35 194 261 25 56 32 64 128 256), losses := [] }

theorem u38793 : Upper (D 6) (R 6) [34,192,257,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38794 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 261 25 82 44 108 172 300), lower := (rows 35 194 261 25 82 32 64 128 256), losses := [] }

theorem u38794 : Upper (D 6) (R 6) [34,192,257,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38795 : Route 9 := (fun mask => (mask,id))

def c38795 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38795 : Upper (D 6) (R 6) [34,192,257,17,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,68] 13 (by decide) (choices 1) [2,4,8] r38795 c38795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24857
  · exact u24858
  · exact u24859

def b38796 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 2, region := 226, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 35 194 261 25 88 38 102 166 294), lower := (rows 35 194 261 25 88 32 64 128 256), losses := [] }

theorem u38796 : Upper (D 6) (R 6) [34,192,257,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38797 : Route 9 := (fun mask => (mask,id))

def c38797 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38797 : Upper (D 6) (R 6) [34,192,257,17,96] 13 := by
  apply FastRouting.sound _ _ [34,192,257,17,96] 13 (by decide) (choices 1) [2,4,8] r38797 c38797
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24860
  · exact u24861
  · exact u24862

def r38798 : Route 9 := (fun mask => (mask,id))

def c38798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38798 : Upper (D 6) (R 6) [34,192,257,18,12] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,12] 13 (by decide) (choices 1) [1,4,64] r38798 c38798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24863
  · exact u24864
  · exact u24865

def b38799 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 261 26 49 108 76 204 332), lower := (rows 35 194 261 26 49 32 64 128 256), losses := [] }

theorem u38799 : Upper (D 6) (R 6) [34,192,257,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38800 : Route 9 := (fun mask => (mask,id))

def c38800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38800 : Upper (D 6) (R 6) [34,192,257,18,36] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,36] 13 (by decide) (choices 1) [1,4,8,64] r38800 c38800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24866
  · exact u24867
  · exact u24868
  · exact u24869

def b38801 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 194 261 26 56 101 69 197 325), lower := (rows 35 194 261 26 56 32 64 128 256), losses := [] }

theorem u38801 : Upper (D 6) (R 6) [34,192,257,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38802 : Route 9 := (fun mask => (mask,id))

def c38802 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38802 : Upper (D 6) (R 6) [34,192,257,18,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,65] 13 (by decide) (choices 1) [4,8] r38802 c38802
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24870
  · exact u24871

def r38803 : Route 9 := (fun mask => (mask,id))

def c38803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38803 : Upper (D 6) (R 6) [34,192,257,18,68] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,68] 13 (by decide) (choices 1) [1,4,8] r38803 c38803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24872
  · exact u24873
  · exact u24874

def b38804 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 24, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 35 194 261 26 88 37 101 165 293), lower := (rows 35 194 261 26 88 32 64 128 256), losses := [] }

theorem u38804 : Upper (D 6) (R 6) [34,192,257,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38805 : Route 9 := (fun mask => (mask,id))

def c38805 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38805 : Upper (D 6) (R 6) [34,192,257,18,96] 13 := by
  apply FastRouting.sound _ _ [34,192,257,18,96] 13 (by decide) (choices 1) [1,4,8] r38805 c38805
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24875
  · exact u24876
  · exact u24877

def b38806 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 261 28 28 99 99 227 355), lower := (rows 35 194 261 28 28 32 64 128 256), losses := [] }

theorem u38806 : Upper (D 6) (R 6) [34,192,257,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38807 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 194 261 28 49 110 78 206 334), lower := (rows 35 194 261 28 49 32 64 128 256), losses := [] }

theorem u38807 : Upper (D 6) (R 6) [34,192,257,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38808 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 194 261 28 50 109 77 205 333), lower := (rows 35 194 261 28 50 32 64 128 256), losses := [] }

theorem u38808 : Upper (D 6) (R 6) [34,192,257,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38808 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38809 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 261 28 52 107 75 203 331), lower := (rows 35 194 261 28 52 32 64 128 256), losses := [] }

theorem u38809 : Upper (D 6) (R 6) [34,192,257,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38810 : Route 9 := (fun mask => (mask,id))

def c38810 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38810 : Upper (D 6) (R 6) [34,192,257,20,40] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,40] 13 (by decide) (choices 1) [1,2,4,64] r38810 c38810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24878
  · exact u24879
  · exact u24880
  · exact u24881

def r38811 : Route 9 := (fun mask => (mask,id))

def c38811 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38811 : Upper (D 6) (R 6) [34,192,257,20,65] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,65] 13 (by decide) (choices 1) [2,4,8] r38811 c38811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24882
  · exact u24883
  · exact u24884

def b38812 : PairBound 9 := { available := 45, camps := [{ cop := 1, region := 16, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 35 194 261 28 82 45 109 173 301), lower := (rows 35 194 261 28 82 32 64 128 256), losses := [] }

theorem u38812 : Upper (D 6) (R 6) [34,192,257,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38813 : PairBound 9 := { available := 43, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 194 261 28 84 43 107 171 299), lower := (rows 35 194 261 28 84 32 64 128 256), losses := [] }

theorem u38813 : Upper (D 6) (R 6) [34,192,257,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38813 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38814 : Route 9 := (fun mask => (mask,id))

def c38814 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38814 : Upper (D 6) (R 6) [34,192,257,20,72] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,72] 13 (by decide) (choices 1) [1,2,4] r38814 c38814
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24885
  · exact u24886
  · exact u24887

def r38815 : Route 9 := (fun mask => (mask,id))

def c38815 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38815 : Upper (D 6) (R 6) [34,192,257,20,96] 13 := by
  apply FastRouting.sound _ _ [34,192,257,20,96] 13 (by decide) (choices 1) [1,2,4,8] r38815 c38815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24888
  · exact u24889
  · exact u24890
  · exact u24891

def b38816 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 261 41 84 62 94 158 286), lower := (rows 35 194 261 41 84 32 64 128 256), losses := [] }

theorem u38816 : Upper (D 6) (R 6) [34,192,257,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38817 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 194 261 41 88 54 86 150 278), lower := (rows 35 194 261 41 88 32 64 128 256), losses := [] }

theorem u38817 : Upper (D 6) (R 6) [34,192,257,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38818 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 261 42 81 60 92 156 284), lower := (rows 35 194 261 42 81 32 64 128 256), losses := [] }

theorem u38818 : Upper (D 6) (R 6) [34,192,257,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38818 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38819 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 8, targets := 68 },{ cop := 3, region := 1, targets := 4 }], pairs := [(0,2),(3,2),(3,6)], upper := (rows 35 194 261 42 84 61 93 157 285), lower := (rows 35 194 261 42 84 32 64 128 256), losses := [] }

theorem u38819 : Upper (D 6) (R 6) [34,192,257,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38819
end Delivery.IrregularNine14.P06
