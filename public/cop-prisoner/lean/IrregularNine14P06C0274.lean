import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0069

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r16440 : Route 9 := (fun mask => (mask,id))

def c16440 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16440 : Upper (D 6) (R 6) [10,132,257,48,65,4] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48,65,4] 13 (by decide) (choices 1) [2,32] r16440 c16440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4148
  · exact u4149

def b16441 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 56 81 96 102 166 294), lower := (rows 11 134 261 56 81 96 64 128 256), losses := [] }

theorem u16441 : Upper (D 6) (R 6) [10,132,257,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16442 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 261 56 82 33 100 228 356), lower := (rows 11 134 261 56 82 33 64 128 256), losses := [] }

theorem u16442 : Upper (D 6) (R 6) [10,132,257,48,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16443 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 356, targets := 2 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 134 261 56 82 36 97 225 353), lower := (rows 11 134 261 56 82 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 38 64 128 256), good := (rows 42 166 292 56 122 36 64 128 256) },{ target := 1, region := (rows 1 0 5 24 16 39 69 133 261), good := (rows 493 484 485 56 120 484 64 128 256) }] }

theorem u16443 : Upper (D 6) (R 6) [10,132,257,48,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16444 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 56 82 96 101 165 293), lower := (rows 11 134 261 56 82 96 64 128 256), losses := [] }

theorem u16444 : Upper (D 6) (R 6) [10,132,257,48,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16445 : PairBound 9 := { available := 98, camps := [], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 261 56 84 33 98 226 354), lower := (rows 11 134 261 56 84 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 64 128 256), good := (rows 41 164 293 56 124 33 64 128 256) },{ target := 2, region := (rows 1 2 0 24 16 37 67 131 259), good := (rows 491 482 481 56 120 481 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 37 0 128 256), good := (rows 43 166 293 56 60 33 0 128 256) }] }

theorem u16445 : Upper (D 6) (R 6) [10,132,257,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16446 : Route 9 := (fun mask => (mask,id))

def c16446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16446 : Upper (D 6) (R 6) [10,132,257,48,68,2] 13 := by
  apply FastRouting.sound _ _ [10,132,257,48,68,2] 13 (by decide) (choices 1) [1,32] r16446 c16446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4150
  · exact u4151

def b16447 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 56 84 96 99 163 291), lower := (rows 11 134 261 56 84 96 64 128 256), losses := [] }

theorem u16447 : Upper (D 6) (R 6) [10,132,257,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16448 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 68 },{ cop := 4, region := 324, targets := 2 }], pairs := [(2,1),(4,2),(4,6)], upper := (rows 11 134 261 104 49 34 84 212 340), lower := (rows 11 134 261 104 49 34 64 128 256), losses := [] }

theorem u16448 : Upper (D 6) (R 6) [10,132,257,96,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16449 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 11 134 261 104 49 36 82 210 338), lower := (rows 11 134 261 104 49 36 64 128 256), losses := [] }

theorem u16449 : Upper (D 6) (R 6) [10,132,257,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16450 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 261 104 49 48 70 198 326), lower := (rows 11 134 261 104 49 48 64 128 256), losses := [] }

theorem u16450 : Upper (D 6) (R 6) [10,132,257,96,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16450 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16451 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 104 49 96 86 150 278), lower := (rows 11 134 261 104 49 96 64 128 256), losses := [] }

theorem u16451 : Upper (D 6) (R 6) [10,132,257,96,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16452 : Route 9 := (fun mask => (mask,id))

def c16452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16452 : Upper (D 6) (R 6) [10,132,257,96,34,1] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96,34,1] 13 (by decide) (choices 1) [4,16] r16452 c16452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4152
  · exact u4153

def b16453 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 48, targets := 65 },{ cop := 4, region := 73, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 134 261 104 50 36 81 209 337), lower := (rows 11 134 261 104 50 36 64 128 256), losses := [] }

theorem u16453 : Upper (D 6) (R 6) [10,132,257,96,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16454 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 261 104 50 48 69 197 325), lower := (rows 11 134 261 104 50 48 64 128 256), losses := [] }

theorem u16454 : Upper (D 6) (R 6) [10,132,257,96,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16454 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16455 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 104 50 96 85 149 277), lower := (rows 11 134 261 104 50 96 64 128 256), losses := [] }

theorem u16455 : Upper (D 6) (R 6) [10,132,257,96,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16456 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 48, targets := 66 },{ cop := 4, region := 194, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 11 134 261 104 52 33 82 210 338), lower := (rows 11 134 261 104 52 33 64 128 256), losses := [] }

theorem u16456 : Upper (D 6) (R 6) [10,132,257,96,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16457 : Route 9 := (fun mask => (mask,id))

def c16457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16457 : Upper (D 6) (R 6) [10,132,257,96,36,2] 13 := by
  apply FastRouting.sound _ _ [10,132,257,96,36,2] 13 (by decide) (choices 1) [1,16] r16457 c16457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4154
  · exact u4155

def b16458 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 134 261 104 52 48 67 195 323), lower := (rows 11 134 261 104 52 48 64 128 256), losses := [] }

theorem u16458 : Upper (D 6) (R 6) [10,132,257,96,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16458 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16459 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 261 104 52 96 83 147 275), lower := (rows 11 134 261 104 52 96 64 128 256), losses := [] }

theorem u16459 : Upper (D 6) (R 6) [10,132,257,96,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16460 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 262 25 52 33 96 224 352), lower := (rows 11 134 262 25 52 33 64 128 256), losses := [] }

theorem u16460 : Upper (D 6) (R 6) [10,132,258,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16461 : Route 9 := (fun mask => (mask,id))

def c16461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16461 : Upper (D 6) (R 6) [10,132,258,17,36,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,17,36,64] 13 (by decide) (choices 1) [1,32] r16461 c16461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4156
  · exact u4157

def b16462 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 134 262 25 112 33 100 228 356), lower := (rows 11 134 262 25 112 33 64 128 256), losses := [] }

theorem u16462 : Upper (D 6) (R 6) [10,132,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m16463_1 : Upper (D 6) (R 6) [10,132,258,17,96,4,1] 13 :=
  permutation_upper _ _ _ [10,132,258,17,96,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4158

def r16463 : Route 9 := (fun mask => (mask,id))

def c16463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16463 : Upper (D 6) (R 6) [10,132,258,17,96,4] 13 := by
  apply FastRouting.sound _ _ [10,132,258,17,96,4] 13 (by decide) (choices 1) [1,32] r16463 c16463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m16463_1
  · exact u4159

def b16464 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 25 112 96 101 165 293), lower := (rows 11 134 262 25 112 96 64 128 256), losses := [] }

theorem u16464 : Upper (D 6) (R 6) [10,132,258,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16465 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 262 28 49 33 96 224 352), lower := (rows 11 134 262 28 49 33 64 128 256), losses := [] }

theorem u16465 : Upper (D 6) (R 6) [10,132,258,20,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16466 : Route 9 := (fun mask => (mask,id))

def c16466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16466 : Upper (D 6) (R 6) [10,132,258,20,33,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20,33,64] 13 (by decide) (choices 1) [1,32] r16466 c16466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4160
  · exact u4161

def r16467 : Route 9 := (fun mask => (mask,id))

def c16467 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16467 : Upper (D 6) (R 6) [10,132,258,20,96,1] 13 := by
  apply FastRouting.sound _ _ [10,132,258,20,96,1] 13 (by decide) (choices 1) [1,32] r16467 c16467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4162
  · exact u4163

def b16468 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 28 112 96 97 161 289), lower := (rows 11 134 262 28 112 96 64 128 256), losses := [] }

theorem u16468 : Upper (D 6) (R 6) [10,132,258,20,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16469 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 262 41 52 33 80 208 336), lower := (rows 11 134 262 41 52 33 64 128 256), losses := [] }

theorem u16469 : Upper (D 6) (R 6) [10,132,258,33,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16470 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 134 262 41 52 48 65 193 321), lower := (rows 11 134 262 41 52 48 64 128 256), losses := [] }

theorem u16470 : Upper (D 6) (R 6) [10,132,258,33,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16470 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16471 : Route 9 := (fun mask => (mask,id))

def c16471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16471 : Upper (D 6) (R 6) [10,132,258,33,36,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,36,64] 13 (by decide) (choices 1) [1,16] r16471 c16471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4164
  · exact u4165

def b16472 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 80, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 134 262 41 81 36 112 240 368), lower := (rows 11 134 262 41 81 36 64 128 256), losses := [] }

theorem u16472 : Upper (D 6) (R 6) [10,132,258,33,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16473 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 262 41 81 48 100 228 356), lower := (rows 11 134 262 41 81 48 64 128 256), losses := [] }

theorem u16473 : Upper (D 6) (R 6) [10,132,258,33,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16473 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16474 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 40, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 134 262 41 81 96 116 180 308), lower := (rows 11 134 262 41 81 96 64 128 256), losses := [] }

theorem u16474 : Upper (D 6) (R 6) [10,132,258,33,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16475 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 262 41 84 33 112 240 368), lower := (rows 11 134 262 41 84 33 64 128 256), losses := [] }

theorem u16475 : Upper (D 6) (R 6) [10,132,258,33,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16476 : Route 9 := (fun mask => (mask,id))

def c16476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16476 : Upper (D 6) (R 6) [10,132,258,33,68,16] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,68,16] 13 (by decide) (choices 1) [1,32] r16476 c16476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4166
  · exact u4167

def r16477 : Route 9 := (fun mask => (mask,id))

def c16477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16477 : Upper (D 6) (R 6) [10,132,258,33,68,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,33,68,64] 13 (by decide) (choices 1) [1,16,32] r16477 c16477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4168
  · exact u4169
  · exact u4170

def b16478 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 262 41 112 33 84 212 340), lower := (rows 11 134 262 41 112 33 64 128 256), losses := [] }

theorem u16478 : Upper (D 6) (R 6) [10,132,258,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16479 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 80, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 11 134 262 41 112 36 81 209 337), lower := (rows 11 134 262 41 112 36 64 128 256), losses := [] }

theorem u16479 : Upper (D 6) (R 6) [10,132,258,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16480 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 262 41 112 48 69 197 325), lower := (rows 11 134 262 41 112 48 64 128 256), losses := [] }

theorem u16480 : Upper (D 6) (R 6) [10,132,258,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16480 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16481 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 41 112 96 85 149 277), lower := (rows 11 134 262 41 112 96 64 128 256), losses := [] }

theorem u16481 : Upper (D 6) (R 6) [10,132,258,33,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16482 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 134 262 44 81 33 112 240 368), lower := (rows 11 134 262 44 81 33 64 128 256), losses := [] }

theorem u16482 : Upper (D 6) (R 6) [10,132,258,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16483 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 134 262 44 81 48 97 225 353), lower := (rows 11 134 262 44 81 48 64 128 256), losses := [] }

theorem u16483 : Upper (D 6) (R 6) [10,132,258,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16483 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16484 : Route 9 := (fun mask => (mask,id))

def c16484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16484 : Upper (D 6) (R 6) [10,132,258,36,65,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,36,65,64] 13 (by decide) (choices 1) [1,16,32] r16484 c16484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4171
  · exact u4172
  · exact u4173

def b16485 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 1, region := 41, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 134 262 44 112 33 81 209 337), lower := (rows 11 134 262 44 112 33 64 128 256), losses := [] }

theorem u16485 : Upper (D 6) (R 6) [10,132,258,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16486 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 262 44 112 48 65 193 321), lower := (rows 11 134 262 44 112 48 64 128 256), losses := [] }

theorem u16486 : Upper (D 6) (R 6) [10,132,258,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16486 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16487 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 44 112 96 81 145 273), lower := (rows 11 134 262 44 112 96 64 128 256), losses := [] }

theorem u16487 : Upper (D 6) (R 6) [10,132,258,36,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16488 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 134 262 56 21 33 96 224 352), lower := (rows 11 134 262 56 21 33 64 128 256), losses := [] }

theorem u16488 : Upper (D 6) (R 6) [10,132,258,48,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16489 : Route 9 := (fun mask => (mask,id))

def c16489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16489 : Upper (D 6) (R 6) [10,132,258,48,5,64] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,5,64] 13 (by decide) (choices 1) [1,32] r16489 c16489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4174
  · exact u4175

def b16490 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 11 134 262 56 81 33 100 228 356), lower := (rows 11 134 262 56 81 33 64 128 256), losses := [] }

theorem u16490 : Upper (D 6) (R 6) [10,132,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16491 : Route 9 := (fun mask => (mask,id))

def c16491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16491 : Upper (D 6) (R 6) [10,132,258,48,65,4] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,65,4] 13 (by decide) (choices 1) [1,32] r16491 c16491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4176
  · exact u4177

def b16492 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 56 81 96 101 165 293), lower := (rows 11 134 262 56 81 96 64 128 256), losses := [] }

theorem u16492 : Upper (D 6) (R 6) [10,132,258,48,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16493 : Route 9 := (fun mask => (mask,id))

def c16493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16493 : Upper (D 6) (R 6) [10,132,258,48,68,1] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,68,1] 13 (by decide) (choices 1) [1,32] r16493 c16493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4178
  · exact u4179

def b16494 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 56 84 96 97 161 289), lower := (rows 11 134 262 56 84 96 64 128 256), losses := [] }

theorem u16494 : Upper (D 6) (R 6) [10,132,258,48,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r16495 : Route 9 := (fun mask => (mask,id))

def c16495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u16495 : Upper (D 6) (R 6) [10,132,258,96,5,1] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96,5,1] 13 (by decide) (choices 1) [16,32] r16495 c16495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4180
  · exact u4181

def b16496 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 104, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 134 262 104 21 48 97 225 353), lower := (rows 11 134 262 104 21 48 64 128 256), losses := [] }

theorem u16496 : Upper (D 6) (R 6) [10,132,258,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16496 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16497 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 134 262 104 21 96 113 177 305), lower := (rows 11 134 262 104 21 96 64 128 256), losses := [] }

theorem u16497 : Upper (D 6) (R 6) [10,132,258,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16498 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 262 104 49 33 84 212 340), lower := (rows 11 134 262 104 49 33 64 128 256), losses := [] }

theorem u16498 : Upper (D 6) (R 6) [10,132,258,96,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b16499 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 72, targets := 6 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(3,2)], upper := (rows 11 134 262 104 49 36 81 209 337), lower := (rows 11 134 262 104 49 36 64 128 256), losses := [] }

theorem u16499 : Upper (D 6) (R 6) [10,132,258,96,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b16499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u16499
end Delivery.IrregularNine14.P06
