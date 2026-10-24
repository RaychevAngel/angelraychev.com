import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0091

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18720 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 25 38 133 76 274 33 98 226 354), lower := (rows 25 38 133 76 274 33 64 128 256), losses := [] }

theorem u18720 : Upper (D 6) (R 6) [24,36,129,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18720 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18721 : Route 9 := (fun mask => (mask,id))

def c18721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18721 : Upper (D 6) (R 6) [24,36,129,68,258,2] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,258,2] 13 (by decide) (choices 1) [1,32] r18721 c18721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5460
  · exact u5461

def r18722 : Route 9 := (fun mask => (mask,id))

def c18722 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18722 : Upper (D 6) (R 6) [24,36,129,68,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,258,64] 13 (by decide) (choices 1) [1,2,32] r18722 c18722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5462
  · exact u5463
  · exact u5464

def b18723 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 336, targets := 4 }], pairs := [(3,0),(4,0),(4,2)], upper := (rows 25 38 133 76 304 33 66 194 322), lower := (rows 25 38 133 76 304 33 64 128 256), losses := [] }

theorem u18723 : Upper (D 6) (R 6) [24,36,129,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18723 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18724 : Route 9 := (fun mask => (mask,id))

def c18724 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18724 : Upper (D 6) (R 6) [24,36,129,68,288,2] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,288,2] 13 (by decide) (choices 1) [1,2] r18724 c18724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5465
  · exact u5466

def r18725 : Route 9 := (fun mask => (mask,id))

def c18725 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18725 : Upper (D 6) (R 6) [24,36,129,68,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,129,68,288,64] 13 (by decide) (choices 1) [1,2] r18725 c18725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5467
  · exact u5468

def b18726 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 1, region := 72, targets := 1 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 25 38 133 76 336 33 98 162 290), lower := (rows 25 38 133 76 336 33 64 128 256), losses := [] }

theorem u18726 : Upper (D 6) (R 6) [24,36,129,68,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18726 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18727 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 133 76 336 34 99 163 291), lower := (rows 25 38 133 76 336 34 64 128 256), losses := [] }

theorem u18727 : Upper (D 6) (R 6) [24,36,129,68,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18727 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18728 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 38 133 104 273 34 70 198 326), lower := (rows 25 38 133 104 273 34 64 128 256), losses := [] }

theorem u18728 : Upper (D 6) (R 6) [24,36,129,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18728 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18729 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 104 273 36 66 194 322), lower := (rows 25 38 133 104 273 36 64 128 256), losses := [] }

theorem u18729 : Upper (D 6) (R 6) [24,36,129,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18729 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18730 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 133 104 273 96 70 134 262), lower := (rows 25 38 133 104 273 96 64 128 256), losses := [] }

theorem u18730 : Upper (D 6) (R 6) [24,36,129,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18730 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18731 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 336, targets := 32 }], pairs := [(3,0),(4,0),(4,5)], upper := (rows 25 38 133 104 274 33 70 198 326), lower := (rows 25 38 133 104 274 33 64 128 256), losses := [] }

theorem u18731 : Upper (D 6) (R 6) [24,36,129,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18731 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18732 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 38 133 104 274 34 69 197 325), lower := (rows 25 38 133 104 274 34 64 128 256), losses := [] }

theorem u18732 : Upper (D 6) (R 6) [24,36,129,96,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18732 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18733 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 104 274 36 67 195 323), lower := (rows 25 38 133 104 274 36 64 128 256), losses := [] }

theorem u18733 : Upper (D 6) (R 6) [24,36,129,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18733 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18734 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 133 104 274 96 71 135 263), lower := (rows 25 38 133 104 274 96 64 128 256), losses := [] }

theorem u18734 : Upper (D 6) (R 6) [24,36,129,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18734 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18735 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 25 38 133 104 276 33 66 194 322), lower := (rows 25 38 133 104 276 33 64 128 256), losses := [] }

theorem u18735 : Upper (D 6) (R 6) [24,36,129,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18735 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18736 : Route 9 := (fun mask => (mask,id))

def c18736 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18736 : Upper (D 6) (R 6) [24,36,129,96,260,2] 13 := by
  apply FastRouting.sound _ _ [24,36,129,96,260,2] 13 (by decide) (choices 1) [1,2] r18736 c18736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5469
  · exact u5470

def b18737 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 133 104 276 96 67 131 259), lower := (rows 25 38 133 104 276 96 64 128 256), losses := [] }

theorem u18737 : Upper (D 6) (R 6) [24,36,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18737 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18738 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 133 104 336 33 70 134 262), lower := (rows 25 38 133 104 336 33 64 128 256), losses := [] }

theorem u18738 : Upper (D 6) (R 6) [24,36,129,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18738 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18739 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 166, targets := 64 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(2,6)], upper := (rows 25 38 133 104 336 34 71 135 263), lower := (rows 25 38 133 104 336 34 64 128 256), losses := [] }

theorem u18739 : Upper (D 6) (R 6) [24,36,129,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18739 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18740 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 38 133 104 336 36 67 131 259), lower := (rows 25 38 133 104 336 36 64 128 256), losses := [] }

theorem u18740 : Upper (D 6) (R 6) [24,36,129,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18740 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18741 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 134 11 84 33 352 480 352), lower := (rows 25 38 134 11 84 33 64 128 256), losses := [] }

theorem u18741 : Upper (D 6) (R 6) [24,36,130,3,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18741 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18742 : Route 9 := (fun mask => (mask,id))

def c18742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u18742 : Upper (D 6) (R 6) [24,36,130,3,68,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,68,64] 13 (by decide) (choices 1) [1,32,256] r18742 c18742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5471
  · exact u5472
  · exact u5473

def r18743 : Route 9 := (fun mask => (mask,id))

def c18743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18743 : Upper (D 6) (R 6) [24,36,130,3,68,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,68,256] 13 (by decide) (choices 1) [1,32] r18743 c18743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5474
  · exact u5475

def b18744 : PairBound 9 := { available := 324, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 112 33 324 452 324), lower := (rows 25 38 134 11 112 33 64 128 256), losses := [] }

theorem u18744 : Upper (D 6) (R 6) [24,36,130,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18744 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18745 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 11 112 36 321 449 321), lower := (rows 25 38 134 11 112 36 64 128 256), losses := [] }

theorem u18745 : Upper (D 6) (R 6) [24,36,130,3,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18745 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18746 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 134 11 112 96 325 389 261), lower := (rows 25 38 134 11 112 96 64 128 256), losses := [] }

theorem u18746 : Upper (D 6) (R 6) [24,36,130,3,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18746 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18747 : Route 9 := (fun mask => (mask,id))

def c18747 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18747 : Upper (D 6) (R 6) [24,36,130,3,96,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,96,256] 13 (by decide) (choices 1) [1,4] r18747 c18747
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5476
  · exact u5477

def b18748 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 38 134 11 276 33 96 224 352), lower := (rows 25 38 134 11 276 33 64 128 256), losses := [] }

theorem u18748 : Upper (D 6) (R 6) [24,36,130,3,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18748 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18749 : Route 9 := (fun mask => (mask,id))

def c18749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18749 : Upper (D 6) (R 6) [24,36,130,3,260,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,260,64] 13 (by decide) (choices 1) [1,32] r18749 c18749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5478
  · exact u5479

def b18750 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 304 33 68 196 324), lower := (rows 25 38 134 11 304 33 64 128 256), losses := [] }

theorem u18750 : Upper (D 6) (R 6) [24,36,130,3,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18750 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18751 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 11 304 36 65 193 321), lower := (rows 25 38 134 11 304 36 64 128 256), losses := [] }

theorem u18751 : Upper (D 6) (R 6) [24,36,130,3,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18751 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18752 : Route 9 := (fun mask => (mask,id))

def c18752 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18752 : Upper (D 6) (R 6) [24,36,130,3,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,288,64] 13 (by decide) (choices 1) [1,4] r18752 c18752
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5480
  · exact u5481

def b18753 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 336 33 100 228 356), lower := (rows 25 38 134 11 336 33 64 128 256), losses := [] }

theorem u18753 : Upper (D 6) (R 6) [24,36,130,3,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18753 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18754 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 11 336 36 97 225 353), lower := (rows 25 38 134 11 336 36 64 128 256), losses := [] }

theorem u18754 : Upper (D 6) (R 6) [24,36,130,3,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18754 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18755 : Route 9 := (fun mask => (mask,id))

def c18755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18755 : Upper (D 6) (R 6) [24,36,130,3,320,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,3,320,64] 13 (by decide) (choices 1) [1,4,32] r18755 c18755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5482
  · exact u5483
  · exact u5484

def b18756 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 82 33 352 480 352), lower := (rows 25 38 134 13 82 33 64 128 256), losses := [] }

theorem u18756 : Upper (D 6) (R 6) [24,36,130,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18756 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18757 : Route 9 := (fun mask => (mask,id))

def c18757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u18757 : Upper (D 6) (R 6) [24,36,130,5,66,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,66,64] 13 (by decide) (choices 1) [1,32,256] r18757 c18757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5485
  · exact u5486
  · exact u5487

def r18758 : Route 9 := (fun mask => (mask,id))

def c18758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18758 : Upper (D 6) (R 6) [24,36,130,5,66,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,66,256] 13 (by decide) (choices 1) [1,32] r18758 c18758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5488
  · exact u5489

def b18759 : PairBound 9 := { available := 322, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 112 33 322 450 322), lower := (rows 25 38 134 13 112 33 64 128 256), losses := [] }

theorem u18759 : Upper (D 6) (R 6) [24,36,130,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18759 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18760 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 13 112 34 321 449 321), lower := (rows 25 38 134 13 112 34 64 128 256), losses := [] }

theorem u18760 : Upper (D 6) (R 6) [24,36,130,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18760 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18761 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 25 38 134 13 112 96 323 387 259), lower := (rows 25 38 134 13 112 96 64 128 256), losses := [] }

theorem u18761 : Upper (D 6) (R 6) [24,36,130,5,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18761 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18762 : Route 9 := (fun mask => (mask,id))

def c18762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18762 : Upper (D 6) (R 6) [24,36,130,5,96,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,96,256] 13 (by decide) (choices 1) [1,2] r18762 c18762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5490
  · exact u5491

def b18763 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 274 33 96 224 352), lower := (rows 25 38 134 13 274 33 64 128 256), losses := [] }

theorem u18763 : Upper (D 6) (R 6) [24,36,130,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18763 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18764 : Route 9 := (fun mask => (mask,id))

def c18764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18764 : Upper (D 6) (R 6) [24,36,130,5,258,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,258,64] 13 (by decide) (choices 1) [1,32] r18764 c18764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5492
  · exact u5493

def b18765 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 304 33 66 194 322), lower := (rows 25 38 134 13 304 33 64 128 256), losses := [] }

theorem u18765 : Upper (D 6) (R 6) [24,36,130,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18765 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18766 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 13 304 34 65 193 321), lower := (rows 25 38 134 13 304 34 64 128 256), losses := [] }

theorem u18766 : Upper (D 6) (R 6) [24,36,130,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18766 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18767 : Route 9 := (fun mask => (mask,id))

def c18767 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18767 : Upper (D 6) (R 6) [24,36,130,5,288,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,288,64] 13 (by decide) (choices 1) [1,2] r18767 c18767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5494
  · exact u5495

def b18768 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 13 336 33 98 226 354), lower := (rows 25 38 134 13 336 33 64 128 256), losses := [] }

theorem u18768 : Upper (D 6) (R 6) [24,36,130,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18768 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18769 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 13 336 34 97 225 353), lower := (rows 25 38 134 13 336 34 64 128 256), losses := [] }

theorem u18769 : Upper (D 6) (R 6) [24,36,130,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18769 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18770 : Route 9 := (fun mask => (mask,id))

def c18770 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18770 : Upper (D 6) (R 6) [24,36,130,5,320,64] 13 := by
  apply FastRouting.sound _ _ [24,36,130,5,320,64] 13 (by decide) (choices 1) [1,2,32] r18770 c18770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5496
  · exact u5497
  · exact u5498

def b18771 : PairBound 9 := { available := 324, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 134 41 82 33 324 452 324), lower := (rows 25 38 134 41 82 33 64 128 256), losses := [] }

theorem u18771 : Upper (D 6) (R 6) [24,36,130,33,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18771 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18772 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 82 36 321 449 321), lower := (rows 25 38 134 41 82 36 64 128 256), losses := [] }

theorem u18772 : Upper (D 6) (R 6) [24,36,130,33,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18772 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18773 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 41 82 96 325 389 261), lower := (rows 25 38 134 41 82 96 64 128 256), losses := [] }

theorem u18773 : Upper (D 6) (R 6) [24,36,130,33,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18773 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18774 : Route 9 := (fun mask => (mask,id))

def c18774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18774 : Upper (D 6) (R 6) [24,36,130,33,66,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,66,256] 13 (by decide) (choices 1) [1,4] r18774 c18774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5499
  · exact u5500

def b18775 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 468, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 25 38 134 41 84 33 322 450 322), lower := (rows 25 38 134 41 84 33 64 128 256), losses := [] }

theorem u18775 : Upper (D 6) (R 6) [24,36,130,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18775 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18776 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 38, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 41 84 34 321 449 321), lower := (rows 25 38 134 41 84 34 64 128 256), losses := [] }

theorem u18776 : Upper (D 6) (R 6) [24,36,130,33,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18776 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b18777 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 41, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 134 41 84 96 323 387 259), lower := (rows 25 38 134 41 84 96 64 128 256), losses := [] }

theorem u18777 : Upper (D 6) (R 6) [24,36,130,33,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18777 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r18778 : Route 9 := (fun mask => (mask,id))

def c18778 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18778 : Upper (D 6) (R 6) [24,36,130,33,68,256] 13 := by
  apply FastRouting.sound _ _ [24,36,130,33,68,256] 13 (by decide) (choices 1) [1,2] r18778 c18778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5501
  · exact u5502

def b18779 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 25 38 134 41 274 33 68 196 324), lower := (rows 25 38 134 41 274 33 64 128 256), losses := [] }

theorem u18779 : Upper (D 6) (R 6) [24,36,130,33,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b18779 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u18779
end Delivery.IrregularNine14.P06
