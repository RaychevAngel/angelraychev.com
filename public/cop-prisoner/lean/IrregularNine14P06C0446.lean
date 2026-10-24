import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0139
import IrregularNine14P06C0140

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b26760 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 41 134 276 74 50 36 65 193 321), lower := (rows 41 134 276 74 50 36 64 128 256), losses := [] }

theorem u26760 : Upper (D 6) (R 6) [40,132,272,66,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26761 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 74 50 96 69 133 261), lower := (rows 41 134 276 74 50 96 64 128 256), losses := [] }

theorem u26761 : Upper (D 6) (R 6) [40,132,272,66,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26762 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(3,2)], upper := (rows 41 134 276 74 52 33 67 195 323), lower := (rows 41 134 276 74 52 33 64 128 256), losses := [] }

theorem u26762 : Upper (D 6) (R 6) [40,132,272,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26762 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26763 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,1),(4,0),(4,1)], upper := (rows 41 134 276 74 52 34 65 193 321), lower := (rows 41 134 276 74 52 34 64 128 256), losses := [] }

theorem u26763 : Upper (D 6) (R 6) [40,132,272,66,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26764 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 74 52 96 67 131 259), lower := (rows 41 134 276 74 52 96 64 128 256), losses := [] }

theorem u26764 : Upper (D 6) (R 6) [40,132,272,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26764 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26765 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 276 74 81 33 102 166 294), lower := (rows 41 134 276 74 81 33 64 128 256), losses := [] }

theorem u26765 : Upper (D 6) (R 6) [40,132,272,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26766 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 276 74 81 34 101 165 293), lower := (rows 41 134 276 74 81 34 64 128 256), losses := [] }

theorem u26766 : Upper (D 6) (R 6) [40,132,272,66,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26767 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 276 74 81 36 99 163 291), lower := (rows 41 134 276 74 81 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 24 38 64 128 256), good := (rows 57 164 308 121 81 36 64 128 256) }] }

theorem u26767 : Upper (D 6) (R 6) [40,132,272,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26767 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26768 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 276 74 112 33 71 135 263), lower := (rows 41 134 276 74 112 33 64 128 256), losses := [] }

theorem u26768 : Upper (D 6) (R 6) [40,132,272,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26769 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 276 74 112 34 69 133 261), lower := (rows 41 134 276 74 112 34 64 128 256), losses := [] }

theorem u26769 : Upper (D 6) (R 6) [40,132,272,66,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26770 : PairBound 9 := { available := 3, camps := [], pairs := [(0,1),(4,0),(4,1)], upper := (rows 41 134 276 74 112 36 67 131 259), lower := (rows 41 134 276 74 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 38 64 128 256), good := (rows 56 166 308 122 112 36 64 128 256) },{ target := 1, region := (rows 9 0 4 8 24 38 64 128 256), good := (rows 57 164 308 121 112 36 64 128 256) }] }

theorem u26770 : Upper (D 6) (R 6) [40,132,272,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26770 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26771 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 276 76 19 33 98 226 354), lower := (rows 41 134 276 76 19 33 64 128 256), losses := [] }

theorem u26771 : Upper (D 6) (R 6) [40,132,272,68,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26772 : Route 9 := (fun mask => (mask,id))

def c26772 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26772 : Upper (D 6) (R 6) [40,132,272,68,3,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,3,2] 13 (by decide) (choices 1) [1,32] r26772 c26772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8394
  · exact u8395

def b26773 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 76 19 96 99 163 291), lower := (rows 41 134 276 76 19 96 64 128 256), losses := [] }

theorem u26773 : Upper (D 6) (R 6) [40,132,272,68,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26774 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 276 76 50 33 67 195 323), lower := (rows 41 134 276 76 50 33 64 128 256), losses := [] }

theorem u26774 : Upper (D 6) (R 6) [40,132,272,68,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26774 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26775 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 41 134 276 76 50 34 65 193 321), lower := (rows 41 134 276 76 50 34 64 128 256), losses := [] }

theorem u26775 : Upper (D 6) (R 6) [40,132,272,68,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26776 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 41 134 276 76 50 96 67 131 259), lower := (rows 41 134 276 76 50 96 64 128 256), losses := [] }

theorem u26776 : Upper (D 6) (R 6) [40,132,272,68,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26777 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 276 76 82 33 99 163 291), lower := (rows 41 134 276 76 82 33 64 128 256), losses := [] }

theorem u26777 : Upper (D 6) (R 6) [40,132,272,68,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26778 : Route 9 := (fun mask => (mask,id))

def c26778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26778 : Upper (D 6) (R 6) [40,132,272,68,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,66,2] 13 (by decide) (choices 1) [1,32] r26778 c26778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8396
  · exact u8397

def b26779 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 41 134 276 76 112 33 67 131 259), lower := (rows 41 134 276 76 112 33 64 128 256), losses := [] }

theorem u26779 : Upper (D 6) (R 6) [40,132,272,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26780 : Route 9 := (fun mask => (mask,id))

def c26780 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26780 : Upper (D 6) (R 6) [40,132,272,68,96,2] 13 := by
  apply FastRouting.sound _ _ [40,132,272,68,96,2] 13 (by decide) (choices 1) [1,2] r26780 c26780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8398
  · exact u8399

def b26781 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 292 11 81 34 84 212 340), lower := (rows 41 134 292 11 81 34 64 128 256), losses := [] }

theorem u26781 : Upper (D 6) (R 6) [40,132,288,3,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26781 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26782 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 11 81 36 82 210 338), lower := (rows 41 134 292 11 81 36 64 128 256), losses := [] }

theorem u26782 : Upper (D 6) (R 6) [40,132,288,3,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26782 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26783 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 292 11 81 48 70 198 326), lower := (rows 41 134 292 11 81 48 64 128 256), losses := [] }

theorem u26783 : Upper (D 6) (R 6) [40,132,288,3,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26783 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26784 : Route 9 := (fun mask => (mask,id))

def c26784 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26784 : Upper (D 6) (R 6) [40,132,288,3,65,64] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,65,64] 13 (by decide) (choices 1) [2,4,16] r26784 c26784
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8400
  · exact u8401
  · exact u8402

def b26785 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 292 11 82 33 84 212 340), lower := (rows 41 134 292 11 82 33 64 128 256), losses := [] }

theorem u26785 : Upper (D 6) (R 6) [40,132,288,3,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26785 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26786 : PairBound 9 := { available := 81, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 11 82 36 81 209 337), lower := (rows 41 134 292 11 82 36 64 128 256), losses := [] }

theorem u26786 : Upper (D 6) (R 6) [40,132,288,3,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26786 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26787 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 134 292 11 82 48 69 197 325), lower := (rows 41 134 292 11 82 48 64 128 256), losses := [] }

theorem u26787 : Upper (D 6) (R 6) [40,132,288,3,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26787 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26788 : Route 9 := (fun mask => (mask,id))

def c26788 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26788 : Upper (D 6) (R 6) [40,132,288,3,66,64] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,66,64] 13 (by decide) (choices 1) [1,4,16] r26788 c26788
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8403
  · exact u8404
  · exact u8405

def b26789 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 292 11 84 33 82 210 338), lower := (rows 41 134 292 11 84 33 64 128 256), losses := [] }

theorem u26789 : Upper (D 6) (R 6) [40,132,288,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26789 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26790 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 292 11 84 34 81 209 337), lower := (rows 41 134 292 11 84 34 64 128 256), losses := [] }

theorem u26790 : Upper (D 6) (R 6) [40,132,288,3,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26790 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26791 : Route 9 := (fun mask => (mask,id))

def c26791 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26791 : Upper (D 6) (R 6) [40,132,288,3,68,16] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,68,16] 13 (by decide) (choices 1) [1,2] r26791 c26791
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8406
  · exact u8407

def r26792 : Route 9 := (fun mask => (mask,id))

def c26792 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26792 : Upper (D 6) (R 6) [40,132,288,3,68,64] 13 := by
  apply FastRouting.sound _ _ [40,132,288,3,68,64] 13 (by decide) (choices 1) [1,2,16] r26792 c26792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8408
  · exact u8409
  · exact u8410

def b26793 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 25 82 33 70 198 326), lower := (rows 41 134 292 25 82 33 64 128 256), losses := [] }

theorem u26793 : Upper (D 6) (R 6) [40,132,288,17,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26793 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26794 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 134 292 25 82 34 69 197 325), lower := (rows 41 134 292 25 82 34 64 128 256), losses := [] }

theorem u26794 : Upper (D 6) (R 6) [40,132,288,17,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26794 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26795 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 25 82 36 67 195 323), lower := (rows 41 134 292 25 82 36 64 128 256), losses := [] }

theorem u26795 : Upper (D 6) (R 6) [40,132,288,17,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26795 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26796 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 292 25 82 96 71 135 263), lower := (rows 41 134 292 25 82 96 64 128 256), losses := [] }

theorem u26796 : Upper (D 6) (R 6) [40,132,288,17,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26796 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26797 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 25 84 33 66 194 322), lower := (rows 41 134 292 25 84 33 64 128 256), losses := [] }

theorem u26797 : Upper (D 6) (R 6) [40,132,288,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26797 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26798 : Route 9 := (fun mask => (mask,id))

def c26798 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26798 : Upper (D 6) (R 6) [40,132,288,17,68,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,17,68,2] 13 (by decide) (choices 1) [1,2] r26798 c26798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8411
  · exact u8412

def b26799 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 292 25 84 96 67 131 259), lower := (rows 41 134 292 25 84 96 64 128 256), losses := [] }

theorem u26799 : Upper (D 6) (R 6) [40,132,288,17,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26799 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26800 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 26 81 33 70 198 326), lower := (rows 41 134 292 26 81 33 64 128 256), losses := [] }

theorem u26800 : Upper (D 6) (R 6) [40,132,288,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26800 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26801 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 292 26 81 34 69 197 325), lower := (rows 41 134 292 26 81 34 64 128 256), losses := [] }

theorem u26801 : Upper (D 6) (R 6) [40,132,288,18,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26801 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26802 : PairBound 9 := { available := 67, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 26 81 36 67 195 323), lower := (rows 41 134 292 26 81 36 64 128 256), losses := [] }

theorem u26802 : Upper (D 6) (R 6) [40,132,288,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26802 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26803 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 292 26 81 96 71 135 263), lower := (rows 41 134 292 26 81 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 132 292 57 113 96 96 128 256) }] }

theorem u26803 : Upper (D 6) (R 6) [40,132,288,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26803 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26804 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 26 84 33 67 195 323), lower := (rows 41 134 292 26 84 33 64 128 256), losses := [] }

theorem u26804 : Upper (D 6) (R 6) [40,132,288,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26804 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26805 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 41 134 292 26 84 34 65 193 321), lower := (rows 41 134 292 26 84 34 64 128 256), losses := [] }

theorem u26805 : Upper (D 6) (R 6) [40,132,288,18,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26805 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26806 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(2,6)], upper := (rows 41 134 292 26 84 96 67 131 259), lower := (rows 41 134 292 26 84 96 64 128 256), losses := [] }

theorem u26806 : Upper (D 6) (R 6) [40,132,288,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26806 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26807 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 28 81 33 66 194 322), lower := (rows 41 134 292 28 81 33 64 128 256), losses := [] }

theorem u26807 : Upper (D 6) (R 6) [40,132,288,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26807 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26808 : Route 9 := (fun mask => (mask,id))

def c26808 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26808 : Upper (D 6) (R 6) [40,132,288,20,65,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,20,65,2] 13 (by decide) (choices 1) [1,2] r26808 c26808
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8413
  · exact u8414

def b26809 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 292 28 81 96 67 131 259), lower := (rows 41 134 292 28 81 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 132 292 61 113 96 96 128 256) }] }

theorem u26809 : Upper (D 6) (R 6) [40,132,288,20,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26809 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26810 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 134 292 28 82 33 67 195 323), lower := (rows 41 134 292 28 82 33 64 128 256), losses := [] }

theorem u26810 : Upper (D 6) (R 6) [40,132,288,20,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26810 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26811 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 324, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 41 134 292 28 82 34 65 193 321), lower := (rows 41 134 292 28 82 34 64 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 16 50 73 137 265), good := (rows 489 162 288 505 114 34 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 50 0 128 256), good := (rows 41 166 292 61 50 34 0 128 256) }] }

theorem u26811 : Upper (D 6) (R 6) [40,132,288,20,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26811 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26812 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(0,1),(1,6),(2,6)], upper := (rows 41 134 292 28 82 96 67 131 259), lower := (rows 41 134 292 28 82 96 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 112 64 128 256), good := (rows 41 132 292 61 112 96 96 128 256) }] }

theorem u26812 : Upper (D 6) (R 6) [40,132,288,20,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26812 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26813 : Route 9 := (fun mask => (mask,id))

def c26813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26813 : Upper (D 6) (R 6) [40,132,288,65,3,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,3,2] 13 (by decide) (choices 1) [4,16] r26813 c26813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8415
  · exact u8416

def b26814 : PairBound 9 := { available := 82, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 73 19 36 82 210 338), lower := (rows 41 134 292 73 19 36 64 128 256), losses := [] }

theorem u26814 : Upper (D 6) (R 6) [40,132,288,65,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26814 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26815 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 134 292 73 19 48 70 198 326), lower := (rows 41 134 292 73 19 48 64 128 256), losses := [] }

theorem u26815 : Upper (D 6) (R 6) [40,132,288,65,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26815 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26816 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 9, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 41 134 292 73 19 96 86 150 278), lower := (rows 41 134 292 73 19 96 64 128 256), losses := [] }

theorem u26816 : Upper (D 6) (R 6) [40,132,288,65,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26816 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26817 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 134 292 73 82 33 86 150 278), lower := (rows 41 134 292 73 82 33 64 128 256), losses := [] }

theorem u26817 : Upper (D 6) (R 6) [40,132,288,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26817 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26818 : Route 9 := (fun mask => (mask,id))

def c26818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26818 : Upper (D 6) (R 6) [40,132,288,65,66,2] 13 := by
  apply FastRouting.sound _ _ [40,132,288,65,66,2] 13 (by decide) (choices 1) [1,4,16] r26818 c26818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8417
  · exact u8418
  · exact u8419

def b26819 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 41 134 292 73 82 36 83 147 275), lower := (rows 41 134 292 73 82 36 64 128 256), losses := [] }

theorem u26819 : Upper (D 6) (R 6) [40,132,288,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26819 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26819
end Delivery.IrregularNine14.P06
