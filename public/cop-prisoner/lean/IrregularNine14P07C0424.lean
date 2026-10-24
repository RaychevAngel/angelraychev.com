import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0147

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r25440 : Route 9 := (fun mask => (mask,id))

def c25440 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25440 : Upper (D 7) (R 7) [36,192,257,65,136,2] 13 := by
  apply FastRouting.sound _ _ [36,192,257,65,136,2] 13 (by decide) (choices 1) [2,16,32] r25440 c25440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8830
  · exact u8831
  · exact u8832

def r25441 : Route 9 := (fun mask => (mask,id))

def c25441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25441 : Upper (D 7) (R 7) [36,192,257,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,192,257,65,136,16] 13 (by decide) (choices 1) [2,32] r25441 c25441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8833
  · exact u8834

def r25442 : Route 9 := (fun mask => (mask,id))

def c25442 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25442 : Upper (D 7) (R 7) [36,192,257,65,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,257,65,160,2] 13 (by decide) (choices 1) [2,8,16] r25442 c25442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8835
  · exact u8836
  · exact u8837

def b25443 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 210, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 37 194 261 73 176 40 82 146 274), lower := (rows 37 194 261 73 176 40 64 128 256), losses := [] }

theorem u25443 : Upper (D 7) (R 7) [36,192,257,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25443 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25444 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 261 73 176 48 74 138 266), lower := (rows 37 194 261 73 176 48 64 128 256), losses := [] }

theorem u25444 : Upper (D 7) (R 7) [36,192,257,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25444 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25445 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 37, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 37 194 261 88 176 33 74 138 266), lower := (rows 37 194 261 88 176 33 64 128 256), losses := [] }

theorem u25445 : Upper (D 7) (R 7) [36,192,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25446 : Route 9 := (fun mask => (mask,id))

def c25446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25446 : Upper (D 7) (R 7) [36,192,257,80,160,2] 13 := by
  apply FastRouting.sound _ _ [36,192,257,80,160,2] 13 (by decide) (choices 1) [1,2,8] r25446 c25446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8838
  · exact u8839
  · exact u8840

def b25447 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 1, region := 56, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 37 194 261 88 176 40 67 131 259), lower := (rows 37 194 261 88 176 40 64 128 256), losses := [] }

theorem u25447 : Upper (D 7) (R 7) [36,192,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25447 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25448 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 11 56 33 208 208 464), lower := (rows 37 194 262 11 56 33 64 128 256), losses := [] }

theorem u25448 : Upper (D 7) (R 7) [36,192,258,3,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25449 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 262 11 56 48 193 193 449), lower := (rows 37 194 262 11 56 48 64 128 256), losses := [] }

theorem u25449 : Upper (D 7) (R 7) [36,192,258,3,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25449 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25450 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,7),(4,0),(4,1)], upper := (rows 37 194 262 11 56 96 209 145 401), lower := (rows 37 194 262 11 56 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 128 256), good := (rows 36 226 294 58 56 96 96 128 256) },{ target := 1, region := (rows 5 0 4 8 24 122 72 136 264), good := (rows 37 224 293 505 504 96 96 128 256) },{ target := 7, region := (rows 5 2 4 12 29 98 64 0 256), good := (rows 61 98 319 59 56 96 96 0 256) }] }

theorem u25450 : Upper (D 7) (R 7) [36,192,258,3,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25451 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 262 11 81 40 240 176 432), lower := (rows 37 194 262 11 81 40 64 128 256), losses := [] }

theorem u25451 : Upper (D 7) (R 7) [36,192,258,3,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25451 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25452 : Route 9 := (fun mask => (mask,id))

def c25452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u25452 : Upper (D 7) (R 7) [36,192,258,3,65,16] 13 := by
  apply FastRouting.sound _ _ [36,192,258,3,65,16] 13 (by decide) (choices 1) [8,32,128] r25452 c25452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8841
  · exact u8842
  · exact u8843

def b25453 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 194 262 11 81 160 120 184 312), lower := (rows 37 194 262 11 81 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 170 72 136 264), good := (rows 37 224 293 505 81 160 64 160 256) },{ target := 6, region := (rows 5 2 4 12 16 162 0 128 256), good := (rows 45 162 303 43 17 160 0 160 256) }] }

theorem u25453 : Upper (D 7) (R 7) [36,192,258,3,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25454 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 11 88 33 240 176 432), lower := (rows 37 194 262 11 88 33 64 128 256), losses := [] }

theorem u25454 : Upper (D 7) (R 7) [36,192,258,3,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25455 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 194 262 11 88 48 225 161 417), lower := (rows 37 194 262 11 88 48 64 128 256), losses := [{ target := 6, region := (rows 17 2 12 8 16 48 0 177 305), good := (rows 421 130 262 399 445 433 0 128 256) }] }

theorem u25455 : Upper (D 7) (R 7) [36,192,258,3,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25455 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25456 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 240, targets := 2 }], pairs := [(0,1),(0,6),(3,6),(4,1)], upper := (rows 37 194 262 11 88 160 113 177 305), lower := (rows 37 194 262 11 88 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 24 186 72 136 264), good := (rows 37 224 293 505 504 160 64 160 256) },{ target := 6, region := (rows 5 2 4 12 16 162 0 128 256), good := (rows 45 162 303 43 24 160 0 160 256) }] }

theorem u25456 : Upper (D 7) (R 7) [36,192,258,3,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25457 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 11 112 33 216 152 408), lower := (rows 37 194 262 11 112 33 64 128 256), losses := [] }

theorem u25457 : Upper (D 7) (R 7) [36,192,258,3,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25458 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 262 11 112 40 209 145 401), lower := (rows 37 194 262 11 112 40 64 128 256), losses := [] }

theorem u25458 : Upper (D 7) (R 7) [36,192,258,3,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25458 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25459 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 262 11 112 48 201 137 393), lower := (rows 37 194 262 11 112 48 64 128 256), losses := [] }

theorem u25459 : Upper (D 7) (R 7) [36,192,258,3,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25459 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25460 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(0,1),(0,6),(4,0),(4,1)], upper := (rows 37 194 262 11 112 160 89 153 281), lower := (rows 37 194 262 11 112 160 64 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 26 170 72 136 264), good := (rows 37 240 309 505 112 160 64 160 256) },{ target := 6, region := (rows 5 2 4 12 16 162 0 128 256), good := (rows 45 162 303 43 48 160 0 160 256) }] }

theorem u25460 : Upper (D 7) (R 7) [36,192,258,3,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25461 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 25 26 33 224 224 480), lower := (rows 37 194 262 25 26 33 64 128 256), losses := [] }

theorem u25461 : Upper (D 7) (R 7) [36,192,258,17,10,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25462 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 225, targets := 2 }], pairs := [(0,1),(0,7),(3,7),(4,7)], upper := (rows 37 194 262 25 26 96 225 161 417), lower := (rows 37 194 262 25 26 96 64 128 256), losses := [{ target := 7, region := (rows 5 2 4 13 20 98 64 0 256), good := (rows 61 98 319 25 58 96 96 0 256) }] }

theorem u25462 : Upper (D 7) (R 7) [36,192,258,17,10,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25463 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 25 50 33 200 200 456), lower := (rows 37 194 262 25 50 33 64 128 256), losses := [] }

theorem u25463 : Upper (D 7) (R 7) [36,192,258,17,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25464 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 262 25 50 40 193 193 449), lower := (rows 37 194 262 25 50 40 64 128 256), losses := [] }

theorem u25464 : Upper (D 7) (R 7) [36,192,258,17,34,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25465 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 397, targets := 64 },{ cop := 1, region := 48, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 37 194 262 25 50 96 201 137 393), lower := (rows 37 194 262 25 50 96 64 128 256), losses := [] }

theorem u25465 : Upper (D 7) (R 7) [36,192,258,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25466 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(2,6)], upper := (rows 37 194 262 25 88 33 226 162 418), lower := (rows 37 194 262 25 88 33 64 128 256), losses := [] }

theorem u25466 : Upper (D 7) (R 7) [36,192,258,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25467 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 293, targets := 64 }], pairs := [(0,6),(2,6),(3,1),(4,1)], upper := (rows 37 194 262 25 88 34 225 161 417), lower := (rows 37 194 262 25 88 34 64 128 256), losses := [] }

theorem u25467 : Upper (D 7) (R 7) [36,192,258,17,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25468 : Route 9 := (fun mask => (mask,id))

def c25468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25468 : Upper (D 7) (R 7) [36,192,258,17,72,128] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,72,128] 13 (by decide) (choices 1) [1,2,32] r25468 c25468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8844
  · exact u8845
  · exact u8846

def b25469 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 262 25 112 33 202 138 394), lower := (rows 37 194 262 25 112 33 64 128 256), losses := [] }

theorem u25469 : Upper (D 7) (R 7) [36,192,258,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25470 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 48, targets := 129 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 37 194 262 25 112 34 201 137 393), lower := (rows 37 194 262 25 112 34 64 128 256), losses := [] }

theorem u25470 : Upper (D 7) (R 7) [36,192,258,17,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25471 : Route 9 := (fun mask => (mask,id))

def c25471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25471 : Upper (D 7) (R 7) [36,192,258,17,96,8] 13 := by
  apply FastRouting.sound _ _ [36,192,258,17,96,8] 13 (by decide) (choices 1) [1,2,128] r25471 c25471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8847
  · exact u8848
  · exact u8849

def b25472 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 48, targets := 1 },{ cop := 1, region := 48, targets := 2 }], pairs := [(1,5),(2,5),(4,0),(4,1)], upper := (rows 37 194 262 25 112 160 75 139 267), lower := (rows 37 194 262 25 112 160 64 128 256), losses := [] }

theorem u25472 : Upper (D 7) (R 7) [36,192,258,17,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25473 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 57, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 26 56 33 193 193 449), lower := (rows 37 194 262 26 56 33 64 128 256), losses := [] }

theorem u25473 : Upper (D 7) (R 7) [36,192,258,18,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25474 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 37 194 262 26 56 96 193 129 385), lower := (rows 37 194 262 26 56 96 64 128 256), losses := [] }

theorem u25474 : Upper (D 7) (R 7) [36,192,258,18,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25475 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 194 262 26 81 33 232 168 424), lower := (rows 37 194 262 26 81 33 64 128 256), losses := [] }

theorem u25475 : Upper (D 7) (R 7) [36,192,258,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25476 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(2,6),(4,1)], upper := (rows 37 194 262 26 81 40 225 161 417), lower := (rows 37 194 262 26 81 40 64 128 256), losses := [] }

theorem u25476 : Upper (D 7) (R 7) [36,192,258,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25476 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25477 : Route 9 := (fun mask => (mask,id))

def c25477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25477 : Upper (D 7) (R 7) [36,192,258,18,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,258,18,65,128] 13 (by decide) (choices 1) [1,8,32] r25477 c25477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8850
  · exact u8851
  · exact u8852

def b25478 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,1),(0,6),(0,7),(2,6)], upper := (rows 37 194 262 26 112 33 201 137 393), lower := (rows 37 194 262 26 112 33 64 128 256), losses := [] }

theorem u25478 : Upper (D 7) (R 7) [36,192,258,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25479 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 194 262 26 112 40 193 129 385), lower := (rows 37 194 262 26 112 40 64 128 256), losses := [] }

theorem u25479 : Upper (D 7) (R 7) [36,192,258,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25479 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25480 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 56, targets := 1 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 37 194 262 26 112 160 73 137 265), lower := (rows 37 194 262 26 112 160 64 128 256), losses := [] }

theorem u25480 : Upper (D 7) (R 7) [36,192,258,18,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25481 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 42 81 33 216 152 408), lower := (rows 37 194 262 42 81 33 64 128 256), losses := [] }

theorem u25481 : Upper (D 7) (R 7) [36,192,258,34,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25481 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25482 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 37 194 262 42 81 40 209 145 401), lower := (rows 37 194 262 42 81 40 64 128 256), losses := [] }

theorem u25482 : Upper (D 7) (R 7) [36,192,258,34,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25482 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25483 : Route 9 := (fun mask => (mask,id))

def c25483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u25483 : Upper (D 7) (R 7) [36,192,258,34,65,16] 13 := by
  apply FastRouting.sound _ _ [36,192,258,34,65,16] 13 (by decide) (choices 1) [1,8,128] r25483 c25483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8853
  · exact u8854
  · exact u8855

def b25484 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 262 42 81 160 89 153 281), lower := (rows 37 194 262 42 81 160 64 128 256), losses := [] }

theorem u25484 : Upper (D 7) (R 7) [36,192,258,34,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25485 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 37 194 262 42 88 33 209 145 401), lower := (rows 37 194 262 42 88 33 64 128 256), losses := [] }

theorem u25485 : Upper (D 7) (R 7) [36,192,258,34,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25486 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 37 194 262 42 88 48 193 129 385), lower := (rows 37 194 262 42 88 48 64 128 256), losses := [] }

theorem u25486 : Upper (D 7) (R 7) [36,192,258,34,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25486 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25487 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 341, targets := 128 },{ cop := 1, region := 40, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(4,7)], upper := (rows 37 194 262 42 88 160 81 145 273), lower := (rows 37 194 262 42 88 160 64 128 256), losses := [] }

theorem u25487 : Upper (D 7) (R 7) [36,192,258,34,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25488 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 194 262 56 81 33 202 138 394), lower := (rows 37 194 262 56 81 33 64 128 256), losses := [] }

theorem u25488 : Upper (D 7) (R 7) [36,192,258,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25489 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 262 56 81 34 201 137 393), lower := (rows 37 194 262 56 81 34 64 128 256), losses := [] }

theorem u25489 : Upper (D 7) (R 7) [36,192,258,48,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25490 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 37 194 262 56 81 40 195 131 387), lower := (rows 37 194 262 56 81 40 64 128 256), losses := [] }

theorem u25490 : Upper (D 7) (R 7) [36,192,258,48,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25490 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25491 : Route 9 := (fun mask => (mask,id))

def c25491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25491 : Upper (D 7) (R 7) [36,192,258,48,65,128] 13 := by
  apply FastRouting.sound _ _ [36,192,258,48,65,128] 13 (by decide) (choices 1) [1,2,8] r25491 c25491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8856
  · exact u8857
  · exact u8858

def b25492 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 262 73 145 34 120 184 312), lower := (rows 37 194 262 73 145 34 64 128 256), losses := [] }

theorem u25492 : Upper (D 7) (R 7) [36,192,258,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25493 : Route 9 := (fun mask => (mask,id))

def c25493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25493 : Upper (D 7) (R 7) [36,192,258,65,129,8] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,129,8] 13 (by decide) (choices 1) [2,16,32] r25493 c25493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8859
  · exact u8860
  · exact u8861

def r25494 : Route 9 := (fun mask => (mask,id))

def c25494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25494 : Upper (D 7) (R 7) [36,192,258,65,136,1] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,136,1] 13 (by decide) (choices 1) [2,16,32] r25494 c25494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8862
  · exact u8863
  · exact u8864

def b25495 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 2, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 37 194 262 73 152 34 113 177 305), lower := (rows 37 194 262 73 152 34 64 128 256), losses := [] }

theorem u25495 : Upper (D 7) (R 7) [36,192,258,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25496 : Route 9 := (fun mask => (mask,id))

def c25496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25496 : Upper (D 7) (R 7) [36,192,258,65,136,16] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,136,16] 13 (by decide) (choices 1) [1,2,32] r25496 c25496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8865
  · exact u8866
  · exact u8867

def r25497 : Route 9 := (fun mask => (mask,id))

def c25497 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25497 : Upper (D 7) (R 7) [36,192,258,65,160,1] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,160,1] 13 (by decide) (choices 1) [2,8,16] r25497 c25497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8868
  · exact u8869
  · exact u8870

def b25498 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 48, targets := 65 }], pairs := [(3,1),(4,0),(4,1),(4,6)], upper := (rows 37 194 262 73 176 34 89 153 281), lower := (rows 37 194 262 73 176 34 64 128 256), losses := [] }

theorem u25498 : Upper (D 7) (R 7) [36,192,258,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r25499 : Route 9 := (fun mask => (mask,id))

def c25499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u25499 : Upper (D 7) (R 7) [36,192,258,65,160,8] 13 := by
  apply FastRouting.sound _ _ [36,192,258,65,160,8] 13 (by decide) (choices 1) [1,2,16] r25499 c25499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8871
  · exact u8872
  · exact u8873

#print axioms u25499
end Delivery.IrregularNine14.P07
