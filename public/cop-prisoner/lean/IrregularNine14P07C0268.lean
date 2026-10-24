import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0057
import IrregularNine14P07C0058

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16080 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 145 160 322 450 322), lower := (rows 13 50 7 104 145 160 64 128 256), losses := [] }

theorem u16080 : Upper (D 7) (R 7) [12,48,3,96,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16081 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 50 7 104 145 288 194 194 450), lower := (rows 13 50 7 104 145 288 64 128 256), losses := [] }

theorem u16081 : Upper (D 7) (R 7) [12,48,3,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16081 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16082 : PairBound 9 := { available := 448, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 104 146 33 448 448 448), lower := (rows 13 50 7 104 146 33 64 128 256), losses := [] }

theorem u16082 : Upper (D 7) (R 7) [12,48,3,96,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16083 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 50 7 104 146 96 449 385 385), lower := (rows 13 50 7 104 146 96 64 128 256), losses := [] }

theorem u16083 : Upper (D 7) (R 7) [12,48,3,96,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16084 : PairBound 9 := { available := 321, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 7 104 146 160 321 449 321), lower := (rows 13 50 7 104 146 160 64 128 256), losses := [] }

theorem u16084 : Upper (D 7) (R 7) [12,48,3,96,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16084 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16085 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 489, targets := 2 },{ cop := 2, region := 208, targets := 32 }], pairs := [(0,1),(3,1),(4,5)], upper := (rows 13 50 7 104 146 288 193 193 449), lower := (rows 13 50 7 104 146 288 64 128 256), losses := [] }

theorem u16085 : Upper (D 7) (R 7) [12,48,3,96,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16085 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16086 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 104 208 33 450 386 386), lower := (rows 13 50 7 104 208 33 64 128 256), losses := [] }

theorem u16086 : Upper (D 7) (R 7) [12,48,3,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16086 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16087 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 104 208 34 449 385 385), lower := (rows 13 50 7 104 208 34 64 128 256), losses := [] }

theorem u16087 : Upper (D 7) (R 7) [12,48,3,96,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16088 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 208 160 323 387 259), lower := (rows 13 50 7 104 208 160 64 128 256), losses := [] }

theorem u16088 : Upper (D 7) (R 7) [12,48,3,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16089 : Route 9 := (fun mask => (mask,id))

def c16089 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16089 : Upper (D 7) (R 7) [12,48,3,96,192,256] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,192,256] 13 (by decide) (choices 1) [1,2,128] r16089 c16089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3477
  · exact u3478
  · exact u3479

def b16090 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 104 273 34 192 192 448), lower := (rows 13 50 7 104 273 34 64 128 256), losses := [] }

theorem u16090 : Upper (D 7) (R 7) [12,48,3,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16090 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16091 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 50 7 104 273 96 194 130 386), lower := (rows 13 50 7 104 273 96 64 128 256), losses := [] }

theorem u16091 : Upper (D 7) (R 7) [12,48,3,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16092 : Route 9 := (fun mask => (mask,id))

def c16092 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16092 : Upper (D 7) (R 7) [12,48,3,96,257,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,257,128] 13 (by decide) (choices 1) [2,128] r16092 c16092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3480
  · exact u3481

def b16093 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 104 274 33 192 192 448), lower := (rows 13 50 7 104 274 33 64 128 256), losses := [] }

theorem u16093 : Upper (D 7) (R 7) [12,48,3,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16094 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 50 7 104 274 96 193 129 385), lower := (rows 13 50 7 104 274 96 64 128 256), losses := [] }

theorem u16094 : Upper (D 7) (R 7) [12,48,3,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16095 : Route 9 := (fun mask => (mask,id))

def c16095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16095 : Upper (D 7) (R 7) [12,48,3,96,258,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,258,128] 13 (by decide) (choices 1) [1,128] r16095 c16095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3482
  · exact u3483

def b16096 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 104 336 33 194 130 386), lower := (rows 13 50 7 104 336 33 64 128 256), losses := [] }

theorem u16096 : Upper (D 7) (R 7) [12,48,3,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16097 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 50 7 104 336 34 193 129 385), lower := (rows 13 50 7 104 336 34 64 128 256), losses := [] }

theorem u16097 : Upper (D 7) (R 7) [12,48,3,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16098 : Route 9 := (fun mask => (mask,id))

def c16098 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16098 : Upper (D 7) (R 7) [12,48,3,96,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,96,320,128] 13 (by decide) (choices 1) [1,2,128] r16098 c16098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3484
  · exact u3485
  · exact u3486

def b16099 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 7 104 400 33 194 194 450), lower := (rows 13 50 7 104 400 33 64 128 256), losses := [] }

theorem u16099 : Upper (D 7) (R 7) [12,48,3,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16099 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16100 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 464, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 7 104 400 34 193 193 449), lower := (rows 13 50 7 104 400 34 64 128 256), losses := [] }

theorem u16100 : Upper (D 7) (R 7) [12,48,3,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16101 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 13 50 7 104 400 96 195 131 387), lower := (rows 13 50 7 104 400 96 64 128 256), losses := [] }

theorem u16101 : Upper (D 7) (R 7) [12,48,3,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16101 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16102 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 104 400 160 67 195 323), lower := (rows 13 50 7 104 400 160 64 128 256), losses := [] }

theorem u16102 : Upper (D 7) (R 7) [12,48,3,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16102 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16103 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 200 82 33 480 416 416), lower := (rows 13 50 7 200 82 33 64 128 256), losses := [] }

theorem u16103 : Upper (D 7) (R 7) [12,48,3,192,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16104 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 489, targets := 2 },{ cop := 3, region := 50, targets := 1 }], pairs := [(0,1),(1,0),(3,1),(4,0)], upper := (rows 13 50 7 200 82 160 353 417 289), lower := (rows 13 50 7 200 82 160 64 128 256), losses := [] }

theorem u16104 : Upper (D 7) (R 7) [12,48,3,192,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16105 : Route 9 := (fun mask => (mask,id))

def c16105 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16105 : Upper (D 7) (R 7) [12,48,3,192,66,256] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,66,256] 13 (by decide) (choices 1) [1,32,128] r16105 c16105
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3487
  · exact u3488
  · exact u3489

def b16106 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 200 273 34 224 224 480), lower := (rows 13 50 7 200 273 34 64 128 256), losses := [] }

theorem u16106 : Upper (D 7) (R 7) [12,48,3,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16107 : Route 9 := (fun mask => (mask,id))

def c16107 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16107 : Upper (D 7) (R 7) [12,48,3,192,257,64] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,257,64] 13 (by decide) (choices 1) [2,32,128] r16107 c16107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3490
  · exact u3491
  · exact u3492

def b16108 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 233, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 200 274 33 224 224 480), lower := (rows 13 50 7 200 274 33 64 128 256), losses := [] }

theorem u16108 : Upper (D 7) (R 7) [12,48,3,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16109 : Route 9 := (fun mask => (mask,id))

def c16109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16109 : Upper (D 7) (R 7) [12,48,3,192,258,64] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,258,64] 13 (by decide) (choices 1) [1,32,128] r16109 c16109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3493
  · exact u3494
  · exact u3495

def r16110 : Route 9 := (fun mask => (mask,id))

def c16110 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16110 : Upper (D 7) (R 7) [12,48,3,192,320,1] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,1] 13 (by decide) (choices 1) [2,32,128] r16110 c16110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3496
  · exact u3497
  · exact u3498

def r16111 : Route 9 := (fun mask => (mask,id))

def c16111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16111 : Upper (D 7) (R 7) [12,48,3,192,320,2] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,2] 13 (by decide) (choices 1) [1,32,128] r16111 c16111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3499
  · exact u3500
  · exact u3501

def r16112 : Route 9 := (fun mask => (mask,id))

def c16112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16112 : Upper (D 7) (R 7) [12,48,3,192,320,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,192,320,128] 13 (by decide) (choices 1) [1,2,32] r16112 c16112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3502
  · exact u3503
  · exact u3504

def b16113 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 242, targets := 1 },{ cop := 4, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 7 265 208 34 224 224 480), lower := (rows 13 50 7 265 208 34 64 128 256), losses := [] }

theorem u16113 : Upper (D 7) (R 7) [12,48,3,257,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16114 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 0, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 7 265 208 96 226 162 418), lower := (rows 13 50 7 265 208 96 64 128 256), losses := [] }

theorem u16114 : Upper (D 7) (R 7) [12,48,3,257,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16115 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 296 81 34 192 192 448), lower := (rows 13 50 7 296 81 34 64 128 256), losses := [] }

theorem u16115 : Upper (D 7) (R 7) [12,48,3,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16116 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 7 296 81 96 194 130 386), lower := (rows 13 50 7 296 81 96 64 128 256), losses := [] }

theorem u16116 : Upper (D 7) (R 7) [12,48,3,288,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16117 : Route 9 := (fun mask => (mask,id))

def c16117 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16117 : Upper (D 7) (R 7) [12,48,3,288,65,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288,65,128] 13 (by decide) (choices 1) [2,128] r16117 c16117
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3505
  · exact u3506

def b16118 : PairBound 9 := { available := 192, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 296 82 33 192 192 448), lower := (rows 13 50 7 296 82 33 64 128 256), losses := [] }

theorem u16118 : Upper (D 7) (R 7) [12,48,3,288,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16119 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 7 296 82 96 193 129 385), lower := (rows 13 50 7 296 82 96 64 128 256), losses := [] }

theorem u16119 : Upper (D 7) (R 7) [12,48,3,288,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16120 : Route 9 := (fun mask => (mask,id))

def c16120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16120 : Upper (D 7) (R 7) [12,48,3,288,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,288,66,128] 13 (by decide) (choices 1) [1,128] r16120 c16120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3507
  · exact u3508

def b16121 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 50 7 296 208 33 194 194 450), lower := (rows 13 50 7 296 208 33 64 128 256), losses := [] }

theorem u16121 : Upper (D 7) (R 7) [12,48,3,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16122 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 34, targets := 193 },{ cop := 0, region := 208, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(4,1)], upper := (rows 13 50 7 296 208 34 193 193 449), lower := (rows 13 50 7 296 208 34 64 128 256), losses := [] }

theorem u16122 : Upper (D 7) (R 7) [12,48,3,288,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16123 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 397, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 50 7 296 208 96 195 131 387), lower := (rows 13 50 7 296 208 96 64 128 256), losses := [] }

theorem u16123 : Upper (D 7) (R 7) [12,48,3,288,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16124 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 55, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 50 7 328 82 33 224 160 416), lower := (rows 13 50 7 328 82 33 64 128 256), losses := [] }

theorem u16124 : Upper (D 7) (R 7) [12,48,3,320,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16125 : Route 9 := (fun mask => (mask,id))

def c16125 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16125 : Upper (D 7) (R 7) [12,48,3,320,66,128] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,66,128] 13 (by decide) (choices 1) [1,32,128] r16125 c16125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3509
  · exact u3510
  · exact u3511

def b16126 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 38, targets := 192 }], pairs := [(1,6),(1,7),(2,6),(2,7)], upper := (rows 13 50 7 328 145 34 224 224 480), lower := (rows 13 50 7 328 145 34 64 128 256), losses := [] }

theorem u16126 : Upper (D 7) (R 7) [12,48,3,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16127 : Route 9 := (fun mask => (mask,id))

def c16127 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16127 : Upper (D 7) (R 7) [12,48,3,320,129,64] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,129,64] 13 (by decide) (choices 1) [2,32,128] r16127 c16127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3512
  · exact u3513
  · exact u3514

def b16128 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 328 145 160 98 226 354), lower := (rows 13 50 7 328 145 160 64 128 256), losses := [] }

theorem u16128 : Upper (D 7) (R 7) [12,48,3,320,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16129 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 489, targets := 2 }], pairs := [(0,1),(1,0),(3,0),(4,0)], upper := (rows 13 50 7 328 146 33 224 224 480), lower := (rows 13 50 7 328 146 33 64 128 256), losses := [] }

theorem u16129 : Upper (D 7) (R 7) [12,48,3,320,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16130 : Route 9 := (fun mask => (mask,id))

def c16130 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16130 : Upper (D 7) (R 7) [12,48,3,320,130,64] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,130,64] 13 (by decide) (choices 1) [1,32,128] r16130 c16130
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3515
  · exact u3516
  · exact u3517

def b16131 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 18, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 50 7 328 146 160 97 225 353), lower := (rows 13 50 7 328 146 160 64 128 256), losses := [] }

theorem u16131 : Upper (D 7) (R 7) [12,48,3,320,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16132 : Route 9 := (fun mask => (mask,id))

def c16132 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16132 : Upper (D 7) (R 7) [12,48,3,320,192,1] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,192,1] 13 (by decide) (choices 1) [2,32,128] r16132 c16132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3518
  · exact u3519
  · exact u3520

def r16133 : Route 9 := (fun mask => (mask,id))

def c16133 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u16133 : Upper (D 7) (R 7) [12,48,3,320,192,2] 13 := by
  apply FastRouting.sound _ _ [12,48,3,320,192,2] 13 (by decide) (choices 1) [1,32,128] r16133 c16133
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3521
  · exact u3522
  · exact u3523

def b16134 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 7 328 208 160 99 163 291), lower := (rows 13 50 7 328 208 160 64 128 256), losses := [] }

theorem u16134 : Upper (D 7) (R 7) [12,48,3,320,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16135 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 457, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 73 146 34 448 448 448), lower := (rows 13 50 37 73 146 34 64 128 256), losses := [] }

theorem u16135 : Upper (D 7) (R 7) [12,48,33,65,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16136 : PairBound 9 := { available := 386, camps := [{ cop := 5, region := 13, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 13 50 37 73 146 96 450 386 386), lower := (rows 13 50 37 73 146 96 64 128 256), losses := [] }

theorem u16136 : Upper (D 7) (R 7) [12,48,33,65,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16137 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 333, targets := 128 },{ cop := 0, region := 498, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 13 50 37 73 146 160 322 450 322), lower := (rows 13 50 37 73 146 160 64 128 256), losses := [] }

theorem u16137 : Upper (D 7) (R 7) [12,48,33,65,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16138 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 13 50 37 73 146 288 194 194 450), lower := (rows 13 50 37 73 146 288 64 128 256), losses := [] }

theorem u16138 : Upper (D 7) (R 7) [12,48,33,65,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16138 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16139 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 201, targets := 34 }], pairs := [(0,1),(0,5),(3,1),(3,5)], upper := (rows 13 50 37 73 274 34 192 192 448), lower := (rows 13 50 37 73 274 34 64 128 256), losses := [] }

theorem u16139 : Upper (D 7) (R 7) [12,48,33,65,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16139
end Delivery.IrregularNine14.P07
