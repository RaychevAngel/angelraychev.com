import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0085

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18720 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 145 96 338 402 274), lower := (rows 35 70 13 168 145 96 64 128 256), losses := [] }

theorem u18720 : Upper (D 7) (R 7) [34,68,9,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18720 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18721 : Route 9 := (fun mask => (mask,id))

def c18721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18721 : Upper (D 7) (R 7) [34,68,9,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,129,256] 13 (by decide) (choices 1) [2,16] r18721 c18721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5123
  · exact u5124

def b18722 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 146 33 336 464 336), lower := (rows 35 70 13 168 146 33 64 128 256), losses := [] }

theorem u18722 : Upper (D 7) (R 7) [34,68,9,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18723 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 146 48 321 449 321), lower := (rows 35 70 13 168 146 48 64 128 256), losses := [] }

theorem u18723 : Upper (D 7) (R 7) [34,68,9,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18723 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18724 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 146 96 337 401 273), lower := (rows 35 70 13 168 146 96 64 128 256), losses := [] }

theorem u18724 : Upper (D 7) (R 7) [34,68,9,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18724 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18725 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,5),(4,5)], upper := (rows 35 70 13 168 146 288 81 209 337), lower := (rows 35 70 13 168 146 288 64 128 256), losses := [] }

theorem u18725 : Upper (D 7) (R 7) [34,68,9,160,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18725 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18726 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 208 33 338 402 274), lower := (rows 35 70 13 168 208 33 64 128 256), losses := [] }

theorem u18726 : Upper (D 7) (R 7) [34,68,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18727 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 208 34 337 401 273), lower := (rows 35 70 13 168 208 34 64 128 256), losses := [] }

theorem u18727 : Upper (D 7) (R 7) [34,68,9,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18728 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 208 48 323 387 259), lower := (rows 35 70 13 168 208 48 64 128 256), losses := [] }

theorem u18728 : Upper (D 7) (R 7) [34,68,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18729 : Route 9 := (fun mask => (mask,id))

def c18729 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18729 : Upper (D 7) (R 7) [34,68,9,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,192,256] 13 (by decide) (choices 1) [1,2,16] r18729 c18729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5125
  · exact u5126
  · exact u5127

def b18730 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 273 34 208 208 464), lower := (rows 35 70 13 168 273 34 64 128 256), losses := [] }

theorem u18730 : Upper (D 7) (R 7) [34,68,9,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18731 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 0, region := 200, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 35 70 13 168 273 48 194 194 450), lower := (rows 35 70 13 168 273 48 64 128 256), losses := [] }

theorem u18731 : Upper (D 7) (R 7) [34,68,9,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18731 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18732 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 273 96 210 146 402), lower := (rows 35 70 13 168 273 96 64 128 256), losses := [] }

theorem u18732 : Upper (D 7) (R 7) [34,68,9,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18733 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 13 168 273 160 82 210 338), lower := (rows 35 70 13 168 273 160 64 128 256), losses := [] }

theorem u18733 : Upper (D 7) (R 7) [34,68,9,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18734 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 274 33 208 208 464), lower := (rows 35 70 13 168 274 33 64 128 256), losses := [] }

theorem u18734 : Upper (D 7) (R 7) [34,68,9,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18735 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 70 13 168 274 48 193 193 449), lower := (rows 35 70 13 168 274 48 64 128 256), losses := [] }

theorem u18735 : Upper (D 7) (R 7) [34,68,9,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18735 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18736 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 274 96 209 145 401), lower := (rows 35 70 13 168 274 96 64 128 256), losses := [] }

theorem u18736 : Upper (D 7) (R 7) [34,68,9,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18737 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 13 168 274 160 81 209 337), lower := (rows 35 70 13 168 274 160 64 128 256), losses := [] }

theorem u18737 : Upper (D 7) (R 7) [34,68,9,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18737 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18738 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 336 33 210 146 402), lower := (rows 35 70 13 168 336 33 64 128 256), losses := [] }

theorem u18738 : Upper (D 7) (R 7) [34,68,9,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18739 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 336 34 209 145 401), lower := (rows 35 70 13 168 336 34 64 128 256), losses := [] }

theorem u18739 : Upper (D 7) (R 7) [34,68,9,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18740 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 140, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 70 13 168 336 48 195 131 387), lower := (rows 35 70 13 168 336 48 64 128 256), losses := [] }

theorem u18740 : Upper (D 7) (R 7) [34,68,9,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18740 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18741 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 70 13 168 336 160 83 147 275), lower := (rows 35 70 13 168 336 160 64 128 256), losses := [] }

theorem u18741 : Upper (D 7) (R 7) [34,68,9,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18742 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 13 168 400 33 82 210 338), lower := (rows 35 70 13 168 400 33 64 128 256), losses := [] }

theorem u18742 : Upper (D 7) (R 7) [34,68,9,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18743 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 168 400 34 81 209 337), lower := (rows 35 70 13 168 400 34 64 128 256), losses := [] }

theorem u18743 : Upper (D 7) (R 7) [34,68,9,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18744 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 13 168 400 48 67 195 323), lower := (rows 35 70 13 168 400 48 64 128 256), losses := [] }

theorem u18744 : Upper (D 7) (R 7) [34,68,9,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18745 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 70 13 168 400 96 83 147 275), lower := (rows 35 70 13 168 400 96 64 128 256), losses := [] }

theorem u18745 : Upper (D 7) (R 7) [34,68,9,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18746 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 200 145 34 368 432 304), lower := (rows 35 70 13 200 145 34 64 128 256), losses := [] }

theorem u18746 : Upper (D 7) (R 7) [34,68,9,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18747 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 70 13 200 145 48 354 418 290), lower := (rows 35 70 13 200 145 48 64 128 256), losses := [] }

theorem u18747 : Upper (D 7) (R 7) [34,68,9,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18748 : Route 9 := (fun mask => (mask,id))

def c18748 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18748 : Upper (D 7) (R 7) [34,68,9,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,129,256] 13 (by decide) (choices 1) [2,16,32] r18748 c18748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5128
  · exact u5129
  · exact u5130

def b18749 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 200 146 33 368 432 304), lower := (rows 35 70 13 200 146 33 64 128 256), losses := [] }

theorem u18749 : Upper (D 7) (R 7) [34,68,9,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18750 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 13 200 146 48 353 417 289), lower := (rows 35 70 13 200 146 48 64 128 256), losses := [] }

theorem u18750 : Upper (D 7) (R 7) [34,68,9,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18750 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18751 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 70 13 200 146 288 113 177 305), lower := (rows 35 70 13 200 146 288 64 128 256), losses := [] }

theorem u18751 : Upper (D 7) (R 7) [34,68,9,192,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18751 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18752 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 200 176 33 338 402 274), lower := (rows 35 70 13 200 176 33 64 128 256), losses := [] }

theorem u18752 : Upper (D 7) (R 7) [34,68,9,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18753 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 200 176 34 337 401 273), lower := (rows 35 70 13 200 176 34 64 128 256), losses := [] }

theorem u18753 : Upper (D 7) (R 7) [34,68,9,192,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18754 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 200 176 48 323 387 259), lower := (rows 35 70 13 200 176 48 64 128 256), losses := [] }

theorem u18754 : Upper (D 7) (R 7) [34,68,9,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18754 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18755 : Route 9 := (fun mask => (mask,id))

def c18755 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18755 : Upper (D 7) (R 7) [34,68,9,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,68,9,192,160,256] 13 (by decide) (choices 1) [1,2,16] r18755 c18755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5131
  · exact u5132
  · exact u5133

def b18756 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 200 273 34 240 176 432), lower := (rows 35 70 13 200 273 34 64 128 256), losses := [] }

theorem u18756 : Upper (D 7) (R 7) [34,68,9,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18757 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 1 }], pairs := [(0,6),(3,0),(4,6)], upper := (rows 35 70 13 200 273 48 226 162 418), lower := (rows 35 70 13 200 273 48 64 128 256), losses := [] }

theorem u18757 : Upper (D 7) (R 7) [34,68,9,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18757 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18758 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 35 70 13 200 273 160 114 178 306), lower := (rows 35 70 13 200 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 32 65 0 257), good := (rows 371 86 351 72 337 32 64 0 256) }] }

theorem u18758 : Upper (D 7) (R 7) [34,68,9,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18759 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 200 274 33 240 176 432), lower := (rows 35 70 13 200 274 33 64 128 256), losses := [] }

theorem u18759 : Upper (D 7) (R 7) [34,68,9,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18760 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 13 200 274 48 225 161 417), lower := (rows 35 70 13 200 274 48 64 128 256), losses := [] }

theorem u18760 : Upper (D 7) (R 7) [34,68,9,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18760 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18761 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 35 70 13 200 274 160 113 177 305), lower := (rows 35 70 13 200 274 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 21 32 65 0 257), good := (rows 371 86 351 72 274 32 64 0 256) }] }

theorem u18761 : Upper (D 7) (R 7) [34,68,9,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18762 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 200 304 33 210 146 402), lower := (rows 35 70 13 200 304 33 64 128 256), losses := [] }

theorem u18762 : Upper (D 7) (R 7) [34,68,9,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18763 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 200 304 34 209 145 401), lower := (rows 35 70 13 200 304 34 64 128 256), losses := [] }

theorem u18763 : Upper (D 7) (R 7) [34,68,9,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18764 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 13 200 304 48 195 131 387), lower := (rows 35 70 13 200 304 48 64 128 256), losses := [] }

theorem u18764 : Upper (D 7) (R 7) [34,68,9,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18764 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18765 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(1,7),(4,6),(4,7)], upper := (rows 35 70 13 200 304 160 83 147 275), lower := (rows 35 70 13 200 304 160 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 17 32 69 0 261), good := (rows 371 326 351 72 304 32 64 0 256) }] }

theorem u18765 : Upper (D 7) (R 7) [34,68,9,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18766 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 70 13 200 400 33 114 178 306), lower := (rows 35 70 13 200 400 33 64 128 256), losses := [] }

theorem u18766 : Upper (D 7) (R 7) [34,68,9,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18767 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 13 200 400 34 113 177 305), lower := (rows 35 70 13 200 400 34 64 128 256), losses := [] }

theorem u18767 : Upper (D 7) (R 7) [34,68,9,192,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18768 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,7),(4,6)], upper := (rows 35 70 13 200 400 48 99 163 291), lower := (rows 35 70 13 200 400 48 64 128 256), losses := [{ target := 7, region := (rows 1 6 4 8 16 48 65 0 257), good := (rows 355 70 335 72 304 48 64 0 256) }] }

theorem u18768 : Upper (D 7) (R 7) [34,68,9,192,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18768 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18769 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 13 266 81 48 224 160 416), lower := (rows 35 70 13 266 81 48 64 128 256), losses := [] }

theorem u18769 : Upper (D 7) (R 7) [34,68,9,258,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18769 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18770 : Route 9 := (fun mask => (mask,id))

def c18770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18770 : Upper (D 7) (R 7) [34,68,9,258,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,65,128] 13 (by decide) (choices 1) [16,32,128] r18770 c18770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5134
  · exact u5135
  · exact u5136

def b18771 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 266 112 33 208 144 400), lower := (rows 35 70 13 266 112 33 64 128 256), losses := [] }

theorem u18771 : Upper (D 7) (R 7) [34,68,9,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18772 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 266 112 48 193 129 385), lower := (rows 35 70 13 266 112 48 64 128 256), losses := [] }

theorem u18772 : Upper (D 7) (R 7) [34,68,9,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18772 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18773 : Route 9 := (fun mask => (mask,id))

def c18773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u18773 : Upper (D 7) (R 7) [34,68,9,258,96,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,96,128] 13 (by decide) (choices 1) [1,16,128] r18773 c18773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5137
  · exact u5138
  · exact u5139

def b18774 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 456, targets := 1 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(3,0),(4,1)], upper := (rows 35 70 13 266 145 48 224 224 480), lower := (rows 35 70 13 266 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 16 48 113 177 305), good := (rows 490 78 462 266 504 496 64 128 256) }] }

theorem u18774 : Upper (D 7) (R 7) [34,68,9,258,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18774 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18775 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 266 145 96 240 176 432), lower := (rows 35 70 13 266 145 96 64 128 256), losses := [] }

theorem u18775 : Upper (D 7) (R 7) [34,68,9,258,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r18776 : Route 9 := (fun mask => (mask,id))

def c18776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u18776 : Upper (D 7) (R 7) [34,68,9,258,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,9,258,129,128] 13 (by decide) (choices 1) [16,32] r18776 c18776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5140
  · exact u5141

def b18777 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 13 266 176 33 208 208 464), lower := (rows 35 70 13 266 176 33 64 128 256), losses := [] }

theorem u18777 : Upper (D 7) (R 7) [34,68,9,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18778 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 13 266 176 48 193 193 449), lower := (rows 35 70 13 266 176 48 64 128 256), losses := [] }

theorem u18778 : Upper (D 7) (R 7) [34,68,9,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18778 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18779 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 70 13 266 176 96 209 145 401), lower := (rows 35 70 13 266 176 96 64 128 256), losses := [] }

theorem u18779 : Upper (D 7) (R 7) [34,68,9,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u18779
end Delivery.IrregularNine14.P07
