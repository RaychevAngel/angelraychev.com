import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0062
import IrregularNine14P07C0063

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16500 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 56 208 160 323 387 259), lower := (rows 13 98 7 56 208 160 64 128 256), losses := [] }

theorem u16500 : Upper (D 7) (R 7) [12,96,3,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16501 : Route 9 := (fun mask => (mask,id))

def c16501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16501 : Upper (D 7) (R 7) [12,96,3,48,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,192,256] 13 (by decide) (choices 1) [1,2,128] r16501 c16501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3760
  · exact u3761
  · exact u3762

def b16502 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 56 273 34 192 192 448), lower := (rows 13 98 7 56 273 34 64 128 256), losses := [] }

theorem u16502 : Upper (D 7) (R 7) [12,96,3,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16503 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 56 273 96 194 130 386), lower := (rows 13 98 7 56 273 96 64 128 256), losses := [] }

theorem u16503 : Upper (D 7) (R 7) [12,96,3,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16504 : Route 9 := (fun mask => (mask,id))

def c16504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16504 : Upper (D 7) (R 7) [12,96,3,48,257,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,257,128] 13 (by decide) (choices 1) [2,128] r16504 c16504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3763
  · exact u3764

def b16505 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 13 98 7 56 274 33 192 192 448), lower := (rows 13 98 7 56 274 33 64 128 256), losses := [] }

theorem u16505 : Upper (D 7) (R 7) [12,96,3,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16506 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 56 274 96 193 129 385), lower := (rows 13 98 7 56 274 96 64 128 256), losses := [] }

theorem u16506 : Upper (D 7) (R 7) [12,96,3,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16507 : Route 9 := (fun mask => (mask,id))

def c16507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16507 : Upper (D 7) (R 7) [12,96,3,48,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,258,128] 13 (by decide) (choices 1) [1,128] r16507 c16507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3765
  · exact u3766

def b16508 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 56 336 33 194 130 386), lower := (rows 13 98 7 56 336 33 64 128 256), losses := [] }

theorem u16508 : Upper (D 7) (R 7) [12,96,3,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16509 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 47, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 13 98 7 56 336 34 193 129 385), lower := (rows 13 98 7 56 336 34 64 128 256), losses := [] }

theorem u16509 : Upper (D 7) (R 7) [12,96,3,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16510 : Route 9 := (fun mask => (mask,id))

def c16510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16510 : Upper (D 7) (R 7) [12,96,3,48,320,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,48,320,128] 13 (by decide) (choices 1) [1,2,128] r16510 c16510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3767
  · exact u3768
  · exact u3769

def b16511 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 56 400 33 194 194 450), lower := (rows 13 98 7 56 400 33 64 128 256), losses := [] }

theorem u16511 : Upper (D 7) (R 7) [12,96,3,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16511 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16512 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 13 98 7 56 400 34 193 193 449), lower := (rows 13 98 7 56 400 34 64 128 256), losses := [] }

theorem u16512 : Upper (D 7) (R 7) [12,96,3,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16513 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 56 400 96 195 131 387), lower := (rows 13 98 7 56 400 96 64 128 256), losses := [] }

theorem u16513 : Upper (D 7) (R 7) [12,96,3,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16514 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 56 400 160 67 195 323), lower := (rows 13 98 7 56 400 160 64 128 256), losses := [] }

theorem u16514 : Upper (D 7) (R 7) [12,96,3,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16514 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16515 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 4, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 137 176 34 336 464 336), lower := (rows 13 98 7 137 176 34 64 128 256), losses := [] }

theorem u16515 : Upper (D 7) (R 7) [12,96,3,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16515 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16516 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 137 176 48 322 450 322), lower := (rows 13 98 7 137 176 48 64 128 256), losses := [] }

theorem u16516 : Upper (D 7) (R 7) [12,96,3,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16516 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16517 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 137 176 96 338 402 274), lower := (rows 13 98 7 137 176 96 64 128 256), losses := [] }

theorem u16517 : Upper (D 7) (R 7) [12,96,3,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16517 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16518 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 7 137 176 288 82 210 338), lower := (rows 13 98 7 137 176 288 64 128 256), losses := [] }

theorem u16518 : Upper (D 7) (R 7) [12,96,3,129,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16518 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16519 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 498, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 13 98 7 137 274 48 224 224 480), lower := (rows 13 98 7 137 274 48 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 16 48 114 178 306), good := (rows 13 480 461 137 496 496 64 128 256) }] }

theorem u16519 : Upper (D 7) (R 7) [12,96,3,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16519 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16520 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 137 274 96 240 176 432), lower := (rows 13 98 7 137 274 96 64 128 256), losses := [] }

theorem u16520 : Upper (D 7) (R 7) [12,96,3,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16521 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 7 137 274 160 112 240 368), lower := (rows 13 98 7 137 274 160 64 128 256), losses := [] }

theorem u16521 : Upper (D 7) (R 7) [12,96,3,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16522 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 137 304 34 208 208 464), lower := (rows 13 98 7 137 304 34 64 128 256), losses := [] }

theorem u16522 : Upper (D 7) (R 7) [12,96,3,129,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16523 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 141, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 137 304 48 194 194 450), lower := (rows 13 98 7 137 304 48 64 128 256), losses := [] }

theorem u16523 : Upper (D 7) (R 7) [12,96,3,129,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16523 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16524 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 137 304 96 210 146 402), lower := (rows 13 98 7 137 304 96 64 128 256), losses := [] }

theorem u16524 : Upper (D 7) (R 7) [12,96,3,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16525 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 5, region := 338, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 7 137 304 160 82 210 338), lower := (rows 13 98 7 137 304 160 64 128 256), losses := [] }

theorem u16525 : Upper (D 7) (R 7) [12,96,3,129,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16526 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 2 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,1)], upper := (rows 13 98 7 137 400 34 112 240 368), lower := (rows 13 98 7 137 400 34 64 128 256), losses := [] }

theorem u16526 : Upper (D 7) (R 7) [12,96,3,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16527 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 7 137 400 48 98 226 354), lower := (rows 13 98 7 137 400 48 64 128 256), losses := [] }

theorem u16527 : Upper (D 7) (R 7) [12,96,3,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16527 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16528 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 137 400 96 114 178 306), lower := (rows 13 98 7 137 400 96 64 128 256), losses := [] }

theorem u16528 : Upper (D 7) (R 7) [12,96,3,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16529 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 48, targets := 192 },{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(4,6),(4,7)], upper := (rows 13 98 7 152 49 34 448 448 448), lower := (rows 13 98 7 152 49 34 64 128 256), losses := [] }

theorem u16529 : Upper (D 7) (R 7) [12,96,3,144,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16530 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 152 49 96 450 386 386), lower := (rows 13 98 7 152 49 96 64 128 256), losses := [] }

theorem u16530 : Upper (D 7) (R 7) [12,96,3,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16531 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 326, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 152 49 160 322 450 322), lower := (rows 13 98 7 152 49 160 64 128 256), losses := [] }

theorem u16531 : Upper (D 7) (R 7) [12,96,3,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16532 : Route 9 := (fun mask => (mask,id))

def c16532 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16532 : Upper (D 7) (R 7) [12,96,3,144,33,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,33,256] 13 (by decide) (choices 1) [2,128] r16532 c16532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3770
  · exact u3771

def b16533 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 13 98 7 152 273 34 224 224 480), lower := (rows 13 98 7 152 273 34 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 98 162 290), good := (rows 29 480 477 152 273 480 64 128 256) }] }

theorem u16533 : Upper (D 7) (R 7) [12,96,3,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16534 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 152 273 96 226 162 418), lower := (rows 13 98 7 152 273 96 64 128 256), losses := [] }

theorem u16534 : Upper (D 7) (R 7) [12,96,3,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16535 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 5, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 7 152 273 160 98 226 354), lower := (rows 13 98 7 152 273 160 64 128 256), losses := [{ target := 7, region := (rows 1 34 4 8 20 32 98 0 290), good := (rows 29 354 343 24 273 354 64 0 256) }] }

theorem u16535 : Upper (D 7) (R 7) [12,96,3,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16536 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 7 152 274 33 224 224 480), lower := (rows 13 98 7 152 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 103 167 295), good := (rows 493 480 485 152 472 481 64 128 256) }] }

theorem u16536 : Upper (D 7) (R 7) [12,96,3,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16537 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 152 274 96 225 161 417), lower := (rows 13 98 7 152 274 96 64 128 256), losses := [] }

theorem u16537 : Upper (D 7) (R 7) [12,96,3,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m16538_1 : Upper (D 7) (R 7) [12,96,3,144,258,128,1] 13 :=
  permutation_upper _ _ _ [12,96,3,144,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3772

theorem m16538_32 : Upper (D 7) (R 7) [12,96,3,144,258,128,32] 13 :=
  permutation_upper _ _ _ [12,96,3,144,258,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3773

def r16538 : Route 9 := (fun mask => (mask,id))

def c16538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16538 : Upper (D 7) (R 7) [12,96,3,144,258,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,258,128] 13 (by decide) (choices 1) [1,32] r16538 c16538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16538_1
  · exact m16538_32

def r16539 : Route 9 := (fun mask => (mask,id))

def c16539 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16539 : Upper (D 7) (R 7) [12,96,3,144,288,1] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,288,1] 13 (by decide) (choices 1) [2,128] r16539 c16539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3774
  · exact u3775

def r16540 : Route 9 := (fun mask => (mask,id))

def c16540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u16540 : Upper (D 7) (R 7) [12,96,3,144,288,2] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,288,2] 13 (by decide) (choices 1) [1,128] r16540 c16540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3776
  · exact u3777

def b16541 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 152 304 96 195 131 387), lower := (rows 13 98 7 152 304 96 64 128 256), losses := [] }

theorem u16541 : Upper (D 7) (R 7) [12,96,3,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16542 : Route 9 := (fun mask => (mask,id))

def c16542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16542 : Upper (D 7) (R 7) [12,96,3,144,288,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,144,288,128] 13 (by decide) (choices 1) [1,2] r16542 c16542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3778
  · exact u3779

def b16543 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 168 81 34 464 400 400), lower := (rows 13 98 7 168 81 34 64 128 256), losses := [] }

theorem u16543 : Upper (D 7) (R 7) [12,96,3,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16543 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16544 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 168 81 48 450 386 386), lower := (rows 13 98 7 168 81 48 64 128 256), losses := [] }

theorem u16544 : Upper (D 7) (R 7) [12,96,3,160,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16544 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16545 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 7 168 81 160 338 402 274), lower := (rows 13 98 7 168 81 160 64 128 256), losses := [] }

theorem u16545 : Upper (D 7) (R 7) [12,96,3,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16546 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 426, targets := 1 },{ cop := 2, region := 208, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 98 7 168 81 288 210 146 402), lower := (rows 13 98 7 168 81 288 64 128 256), losses := [] }

theorem u16546 : Upper (D 7) (R 7) [12,96,3,160,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16546 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16547 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 45, targets := 64 },{ cop := 5, region := 466, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(3,6)], upper := (rows 13 98 7 168 146 33 336 464 336), lower := (rows 13 98 7 168 146 33 64 128 256), losses := [] }

theorem u16547 : Upper (D 7) (R 7) [12,96,3,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16548 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 146 48 321 449 321), lower := (rows 13 98 7 168 146 48 64 128 256), losses := [] }

theorem u16548 : Upper (D 7) (R 7) [12,96,3,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16548 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16549 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 168 146 96 337 401 273), lower := (rows 13 98 7 168 146 96 64 128 256), losses := [] }

theorem u16549 : Upper (D 7) (R 7) [12,96,3,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16550 : Route 9 := (fun mask => (mask,id))

def c16550 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16550 : Upper (D 7) (R 7) [12,96,3,160,130,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,130,256] 13 (by decide) (choices 1) [1,16] r16550 c16550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3780
  · exact u3781

def b16551 : PairBound 9 := { available := 274, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 168 208 33 338 402 274), lower := (rows 13 98 7 168 208 33 64 128 256), losses := [] }

theorem u16551 : Upper (D 7) (R 7) [12,96,3,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16552 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 168 208 34 337 401 273), lower := (rows 13 98 7 168 208 34 64 128 256), losses := [] }

theorem u16552 : Upper (D 7) (R 7) [12,96,3,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16552 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16553 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 168 208 48 323 387 259), lower := (rows 13 98 7 168 208 48 64 128 256), losses := [] }

theorem u16553 : Upper (D 7) (R 7) [12,96,3,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16553 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r16554 : Route 9 := (fun mask => (mask,id))

def c16554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16554 : Upper (D 7) (R 7) [12,96,3,160,192,256] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,192,256] 13 (by decide) (choices 1) [1,2,16] r16554 c16554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3782
  · exact u3783
  · exact u3784

def b16555 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 7 168 273 34 208 208 464), lower := (rows 13 98 7 168 273 34 64 128 256), losses := [] }

theorem u16555 : Upper (D 7) (R 7) [12,96,3,160,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16556 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 2, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 13 98 7 168 273 48 194 194 450), lower := (rows 13 98 7 168 273 48 64 128 256), losses := [] }

theorem u16556 : Upper (D 7) (R 7) [12,96,3,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16556 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16557 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 168 273 96 210 146 402), lower := (rows 13 98 7 168 273 96 64 128 256), losses := [] }

theorem u16557 : Upper (D 7) (R 7) [12,96,3,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16558 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 7 168 273 160 82 210 338), lower := (rows 13 98 7 168 273 160 64 128 256), losses := [] }

theorem u16558 : Upper (D 7) (R 7) [12,96,3,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16559 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 400, targets := 32 }], pairs := [(1,0),(3,0),(4,0),(4,5)], upper := (rows 13 98 7 168 274 33 208 208 464), lower := (rows 13 98 7 168 274 33 64 128 256), losses := [] }

theorem u16559 : Upper (D 7) (R 7) [12,96,3,160,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u16559
end Delivery.IrregularNine14.P07
