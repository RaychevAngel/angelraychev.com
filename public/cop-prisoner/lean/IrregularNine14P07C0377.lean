import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0115

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r22620 : Route 9 := (fun mask => (mask,id))

def c22620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22620 : Upper (D 7) (R 7) [36,72,3,144,288,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,288,128] 13 (by decide) (choices 1) [1,2] r22620 c22620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6913
  · exact u6914

def b22621 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 474, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 74 7 152 336 33 226 162 418), lower := (rows 37 74 7 152 336 33 64 128 256), losses := [] }

theorem u22621 : Upper (D 7) (R 7) [36,72,3,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22622 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 74 7 152 336 34 225 161 417), lower := (rows 37 74 7 152 336 34 64 128 256), losses := [] }

theorem u22622 : Upper (D 7) (R 7) [36,72,3,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22622 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22623 : Route 9 := (fun mask => (mask,id))

def c22623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22623 : Upper (D 7) (R 7) [36,72,3,144,320,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,144,320,128] 13 (by decide) (choices 1) [1,2,32] r22623 c22623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6915
  · exact u6916
  · exact u6917

def b22624 : PairBound 9 := { available := 400, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 81 34 464 400 400), lower := (rows 37 74 7 168 81 34 64 128 256), losses := [] }

theorem u22624 : Upper (D 7) (R 7) [36,72,3,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22624 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22625 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 53, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 37 74 7 168 81 48 450 386 386), lower := (rows 37 74 7 168 81 48 64 128 256), losses := [] }

theorem u22625 : Upper (D 7) (R 7) [36,72,3,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22626 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 7 168 81 160 338 402 274), lower := (rows 37 74 7 168 81 160 64 128 256), losses := [] }

theorem u22626 : Upper (D 7) (R 7) [36,72,3,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22626 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22627 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 74 7 168 81 288 210 146 402), lower := (rows 37 74 7 168 81 288 64 128 256), losses := [] }

theorem u22627 : Upper (D 7) (R 7) [36,72,3,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22627 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22628 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 145 34 336 464 336), lower := (rows 37 74 7 168 145 34 64 128 256), losses := [] }

theorem u22628 : Upper (D 7) (R 7) [36,72,3,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22628 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22629 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 145 48 322 450 322), lower := (rows 37 74 7 168 145 48 64 128 256), losses := [] }

theorem u22629 : Upper (D 7) (R 7) [36,72,3,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22629 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22630 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 168 145 96 338 402 274), lower := (rows 37 74 7 168 145 96 64 128 256), losses := [] }

theorem u22630 : Upper (D 7) (R 7) [36,72,3,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22631 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 74 7 168 145 288 82 210 338), lower := (rows 37 74 7 168 145 288 64 128 256), losses := [] }

theorem u22631 : Upper (D 7) (R 7) [36,72,3,160,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22631 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22632 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 146 33 336 464 336), lower := (rows 37 74 7 168 146 33 64 128 256), losses := [] }

theorem u22632 : Upper (D 7) (R 7) [36,72,3,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22633 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 146 48 321 449 321), lower := (rows 37 74 7 168 146 48 64 128 256), losses := [] }

theorem u22633 : Upper (D 7) (R 7) [36,72,3,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22633 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22634 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 37 74 7 168 146 96 337 401 273), lower := (rows 37 74 7 168 146 96 64 128 256), losses := [] }

theorem u22634 : Upper (D 7) (R 7) [36,72,3,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22635 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 2, region := 208, targets := 32 }], pairs := [(0,7),(2,7),(4,5)], upper := (rows 37 74 7 168 146 288 81 209 337), lower := (rows 37 74 7 168 146 288 64 128 256), losses := [] }

theorem u22635 : Upper (D 7) (R 7) [36,72,3,160,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22635 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22636 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 208 33 338 402 274), lower := (rows 37 74 7 168 208 33 64 128 256), losses := [] }

theorem u22636 : Upper (D 7) (R 7) [36,72,3,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22637 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 208 34 337 401 273), lower := (rows 37 74 7 168 208 34 64 128 256), losses := [] }

theorem u22637 : Upper (D 7) (R 7) [36,72,3,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22638 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 208 48 323 387 259), lower := (rows 37 74 7 168 208 48 64 128 256), losses := [] }

theorem u22638 : Upper (D 7) (R 7) [36,72,3,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22638 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22639 : Route 9 := (fun mask => (mask,id))

def c22639 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22639 : Upper (D 7) (R 7) [36,72,3,160,192,256] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,192,256] 13 (by decide) (choices 1) [1,2,16] r22639 c22639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6918
  · exact u6919
  · exact u6920

def b22640 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 273 34 208 208 464), lower := (rows 37 74 7 168 273 34 64 128 256), losses := [] }

theorem u22640 : Upper (D 7) (R 7) [36,72,3,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22641 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 2, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 37 74 7 168 273 48 194 194 450), lower := (rows 37 74 7 168 273 48 64 128 256), losses := [] }

theorem u22641 : Upper (D 7) (R 7) [36,72,3,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22641 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22642 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 37 74 7 168 273 96 210 146 402), lower := (rows 37 74 7 168 273 96 64 128 256), losses := [] }

theorem u22642 : Upper (D 7) (R 7) [36,72,3,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22643 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 7 168 273 160 82 210 338), lower := (rows 37 74 7 168 273 160 64 128 256), losses := [] }

theorem u22643 : Upper (D 7) (R 7) [36,72,3,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22644 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 274 33 208 208 464), lower := (rows 37 74 7 168 274 33 64 128 256), losses := [] }

theorem u22644 : Upper (D 7) (R 7) [36,72,3,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22645 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 74 7 168 274 48 193 193 449), lower := (rows 37 74 7 168 274 48 64 128 256), losses := [] }

theorem u22645 : Upper (D 7) (R 7) [36,72,3,160,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22645 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22646 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 37 74 7 168 274 96 209 145 401), lower := (rows 37 74 7 168 274 96 64 128 256), losses := [] }

theorem u22646 : Upper (D 7) (R 7) [36,72,3,160,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22646 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22647 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 7 168 274 160 81 209 337), lower := (rows 37 74 7 168 274 160 64 128 256), losses := [] }

theorem u22647 : Upper (D 7) (R 7) [36,72,3,160,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22648 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 336 33 210 146 402), lower := (rows 37 74 7 168 336 33 64 128 256), losses := [] }

theorem u22648 : Upper (D 7) (R 7) [36,72,3,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22649 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 336 34 209 145 401), lower := (rows 37 74 7 168 336 34 64 128 256), losses := [] }

theorem u22649 : Upper (D 7) (R 7) [36,72,3,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22649 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22650 : Route 9 := (fun mask => (mask,id))

def c22650 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22650 : Upper (D 7) (R 7) [36,72,3,160,320,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,160,320,16] 13 (by decide) (choices 1) [1,2,128] r22650 c22650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6921
  · exact u6922
  · exact u6923

def b22651 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 7 168 336 160 83 147 275), lower := (rows 37 74 7 168 336 160 64 128 256), losses := [] }

theorem u22651 : Upper (D 7) (R 7) [36,72,3,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22651 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22652 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 400 33 82 210 338), lower := (rows 37 74 7 168 400 33 64 128 256), losses := [] }

theorem u22652 : Upper (D 7) (R 7) [36,72,3,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22652 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22653 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 168 400 34 81 209 337), lower := (rows 37 74 7 168 400 34 64 128 256), losses := [] }

theorem u22653 : Upper (D 7) (R 7) [36,72,3,160,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22653 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22654 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 74 7 168 400 48 67 195 323), lower := (rows 37 74 7 168 400 48 64 128 256), losses := [] }

theorem u22654 : Upper (D 7) (R 7) [36,72,3,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22654 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22655 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 37 74 7 168 400 96 83 147 275), lower := (rows 37 74 7 168 400 96 64 128 256), losses := [] }

theorem u22655 : Upper (D 7) (R 7) [36,72,3,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22655 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22656 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 5, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 265 112 34 208 144 400), lower := (rows 37 74 7 265 112 34 64 128 256), losses := [] }

theorem u22656 : Upper (D 7) (R 7) [36,72,3,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22657 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 265 112 48 194 130 386), lower := (rows 37 74 7 265 112 48 64 128 256), losses := [] }

theorem u22657 : Upper (D 7) (R 7) [36,72,3,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22657 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22658 : Route 9 := (fun mask => (mask,id))

def c22658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22658 : Upper (D 7) (R 7) [36,72,3,257,96,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,96,128] 13 (by decide) (choices 1) [2,16,128] r22658 c22658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6924
  · exact u6925
  · exact u6926

def b22659 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 74 7 265 146 48 224 224 480), lower := (rows 37 74 7 265 146 48 64 128 256), losses := [] }

theorem u22659 : Upper (D 7) (R 7) [36,72,3,257,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22659 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22660 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 265 146 96 240 176 432), lower := (rows 37 74 7 265 146 96 64 128 256), losses := [] }

theorem u22660 : Upper (D 7) (R 7) [36,72,3,257,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22661 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 242, targets := 1 },{ cop := 4, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 74 7 265 146 160 112 240 368), lower := (rows 37 74 7 265 146 160 64 128 256), losses := [] }

theorem u22661 : Upper (D 7) (R 7) [36,72,3,257,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22661 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22662 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 265 176 34 208 208 464), lower := (rows 37 74 7 265 176 34 64 128 256), losses := [] }

theorem u22662 : Upper (D 7) (R 7) [36,72,3,257,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22663 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 265 176 48 194 194 450), lower := (rows 37 74 7 265 176 48 64 128 256), losses := [] }

theorem u22663 : Upper (D 7) (R 7) [36,72,3,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22663 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22664 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 37 74 7 265 176 96 210 146 402), lower := (rows 37 74 7 265 176 96 64 128 256), losses := [] }

theorem u22664 : Upper (D 7) (R 7) [36,72,3,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22664 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22665 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 265 176 160 82 210 338), lower := (rows 37 74 7 265 176 160 64 128 256), losses := [] }

theorem u22665 : Upper (D 7) (R 7) [36,72,3,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22666 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 265 208 34 240 176 432), lower := (rows 37 74 7 265 208 34 64 128 256), losses := [] }

theorem u22666 : Upper (D 7) (R 7) [36,72,3,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22667 : Route 9 := (fun mask => (mask,id))

def c22667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u22667 : Upper (D 7) (R 7) [36,72,3,257,192,16] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,192,16] 13 (by decide) (choices 1) [2,32,128] r22667 c22667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6927
  · exact u6928
  · exact u6929

def r22668 : Route 9 := (fun mask => (mask,id))

def c22668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22668 : Upper (D 7) (R 7) [36,72,3,257,192,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,257,192,128] 13 (by decide) (choices 1) [2,16,32] r22668 c22668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6930
  · exact u6931
  · exact u6932

def b22669 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 266 112 33 208 144 400), lower := (rows 37 74 7 266 112 33 64 128 256), losses := [] }

theorem u22669 : Upper (D 7) (R 7) [36,72,3,258,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22669 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22670 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 266 112 48 193 129 385), lower := (rows 37 74 7 266 112 48 64 128 256), losses := [] }

theorem u22670 : Upper (D 7) (R 7) [36,72,3,258,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22670 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22671 : Route 9 := (fun mask => (mask,id))

def c22671 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22671 : Upper (D 7) (R 7) [36,72,3,258,96,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,96,128] 13 (by decide) (choices 1) [1,16,128] r22671 c22671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6933
  · exact u6934
  · exact u6935

def b22672 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 266 176 33 208 208 464), lower := (rows 37 74 7 266 176 33 64 128 256), losses := [] }

theorem u22672 : Upper (D 7) (R 7) [36,72,3,258,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22672 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22673 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 7 266 176 48 193 193 449), lower := (rows 37 74 7 266 176 48 64 128 256), losses := [] }

theorem u22673 : Upper (D 7) (R 7) [36,72,3,258,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22673 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22674 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,1)], upper := (rows 37 74 7 266 176 96 209 145 401), lower := (rows 37 74 7 266 176 96 64 128 256), losses := [] }

theorem u22674 : Upper (D 7) (R 7) [36,72,3,258,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22674 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22675 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 37 74 7 266 176 160 81 209 337), lower := (rows 37 74 7 266 176 160 64 128 256), losses := [] }

theorem u22675 : Upper (D 7) (R 7) [36,72,3,258,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22675 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22676 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 37 74 7 266 208 33 240 176 432), lower := (rows 37 74 7 266 208 33 64 128 256), losses := [] }

theorem u22676 : Upper (D 7) (R 7) [36,72,3,258,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22676 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22677 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1),(3,6),(4,1)], upper := (rows 37 74 7 266 208 48 225 161 417), lower := (rows 37 74 7 266 208 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 12 16 48 0 129 257), good := (rows 429 10 399 266 176 48 0 128 256) }] }

theorem u22677 : Upper (D 7) (R 7) [36,72,3,258,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22677 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22678 : Route 9 := (fun mask => (mask,id))

def c22678 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22678 : Upper (D 7) (R 7) [36,72,3,258,192,128] 13 := by
  apply FastRouting.sound _ _ [36,72,3,258,192,128] 13 (by decide) (choices 1) [1,16,32] r22678 c22678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6936
  · exact u6937
  · exact u6938

def b22679 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 74 7 280 112 33 194 130 386), lower := (rows 37 74 7 280 112 33 64 128 256), losses := [] }

theorem u22679 : Upper (D 7) (R 7) [36,72,3,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22679 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22679
end Delivery.IrregularNine14.P07
