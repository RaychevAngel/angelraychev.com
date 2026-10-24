import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0021

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12480 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 274 33 200 200 456), lower := (rows 7 35 196 56 274 33 64 128 256), losses := [] }

theorem u12480 : Upper (D 7) (R 7) [6,33,192,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12481 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 196 56 274 40 193 193 449), lower := (rows 7 35 196 56 274 40 64 128 256), losses := [] }

theorem u12481 : Upper (D 7) (R 7) [6,33,192,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12481 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12482 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 408, targets := 64 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(1,7),(3,6),(4,6)], upper := (rows 7 35 196 56 274 96 201 137 393), lower := (rows 7 35 196 56 274 96 64 128 256), losses := [] }

theorem u12482 : Upper (D 7) (R 7) [6,33,192,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12482 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12483 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 280 33 194 194 450), lower := (rows 7 35 196 56 280 33 64 128 256), losses := [] }

theorem u12483 : Upper (D 7) (R 7) [6,33,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12483 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12484 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 280 34 193 193 449), lower := (rows 7 35 196 56 280 34 64 128 256), losses := [] }

theorem u12484 : Upper (D 7) (R 7) [6,33,192,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12484 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12485 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 1, region := 408, targets := 64 }], pairs := [(0,5),(2,5),(3,6),(4,6)], upper := (rows 7 35 196 56 280 96 195 131 387), lower := (rows 7 35 196 56 280 96 64 128 256), losses := [] }

theorem u12485 : Upper (D 7) (R 7) [6,33,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12486 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 336 33 202 138 394), lower := (rows 7 35 196 56 336 33 64 128 256), losses := [] }

theorem u12486 : Upper (D 7) (R 7) [6,33,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12487 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 56 336 34 201 137 393), lower := (rows 7 35 196 56 336 34 64 128 256), losses := [] }

theorem u12487 : Upper (D 7) (R 7) [6,33,192,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12488 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 35 196 56 336 40 195 131 387), lower := (rows 7 35 196 56 336 40 64 128 256), losses := [] }

theorem u12488 : Upper (D 7) (R 7) [6,33,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12488 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12489 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 56 336 160 75 139 267), lower := (rows 7 35 196 56 336 160 64 128 256), losses := [] }

theorem u12489 : Upper (D 7) (R 7) [6,33,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12490 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 146 40 368 432 304), lower := (rows 7 35 196 73 146 40 64 128 256), losses := [] }

theorem u12490 : Upper (D 7) (R 7) [6,33,192,65,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12490 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12491 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 7 35 196 73 146 48 360 424 296), lower := (rows 7 35 196 73 146 48 64 128 256), losses := [] }

theorem u12491 : Upper (D 7) (R 7) [6,33,192,65,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12491 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12492 : Route 9 := (fun mask => (mask,id))

def c12492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12492 : Upper (D 7) (R 7) [6,33,192,65,130,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,130,256] 13 (by decide) (choices 1) [8,16,32] r12492 c12492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1289
  · exact u1290
  · exact u1291

def b12493 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 152 34 368 432 304), lower := (rows 7 35 196 73 152 34 64 128 256), losses := [] }

theorem u12493 : Upper (D 7) (R 7) [6,33,192,65,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12494 : PairBound 9 := { available := 290, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 35 196 73 152 48 354 418 290), lower := (rows 7 35 196 73 152 48 64 128 256), losses := [] }

theorem u12494 : Upper (D 7) (R 7) [6,33,192,65,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12494 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12495 : Route 9 := (fun mask => (mask,id))

def c12495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12495 : Upper (D 7) (R 7) [6,33,192,65,136,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,136,256] 13 (by decide) (choices 1) [2,16,32] r12495 c12495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1292
  · exact u1293
  · exact u1294

def b12496 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 176 34 344 408 280), lower := (rows 7 35 196 73 176 34 64 128 256), losses := [] }

theorem u12496 : Upper (D 7) (R 7) [6,33,192,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12497 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 176 40 338 402 274), lower := (rows 7 35 196 73 176 40 64 128 256), losses := [] }

theorem u12497 : Upper (D 7) (R 7) [6,33,192,65,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12497 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12498 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 196 73 176 48 330 394 266), lower := (rows 7 35 196 73 176 48 64 128 256), losses := [] }

theorem u12498 : Upper (D 7) (R 7) [6,33,192,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12498 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12499 : Route 9 := (fun mask => (mask,id))

def c12499 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12499 : Upper (D 7) (R 7) [6,33,192,65,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,65,160,256] 13 (by decide) (choices 1) [2,8,16] r12499 c12499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def b12500 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 274 40 240 176 432), lower := (rows 7 35 196 73 274 40 64 128 256), losses := [] }

theorem u12500 : Upper (D 7) (R 7) [6,33,192,65,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12500 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12501 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 204, targets := 2 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 196 73 274 48 232 168 424), lower := (rows 7 35 196 73 274 48 64 128 256), losses := [] }

theorem u12501 : Upper (D 7) (R 7) [6,33,192,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12501 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12502 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 73 274 160 120 184 312), lower := (rows 7 35 196 73 274 160 64 128 256), losses := [] }

theorem u12502 : Upper (D 7) (R 7) [6,33,192,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12503 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 280 34 240 176 432), lower := (rows 7 35 196 73 280 34 64 128 256), losses := [] }

theorem u12503 : Upper (D 7) (R 7) [6,33,192,65,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12503 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12504 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(1,6),(2,0),(4,6)], upper := (rows 7 35 196 73 280 48 226 162 418), lower := (rows 7 35 196 73 280 48 64 128 256), losses := [] }

theorem u12504 : Upper (D 7) (R 7) [6,33,192,65,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12504 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12505 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 73 280 160 114 178 306), lower := (rows 7 35 196 73 280 160 64 128 256), losses := [] }

theorem u12505 : Upper (D 7) (R 7) [6,33,192,65,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12506 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 304 34 216 152 408), lower := (rows 7 35 196 73 304 34 64 128 256), losses := [] }

theorem u12506 : Upper (D 7) (R 7) [6,33,192,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12507 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 304 40 210 146 402), lower := (rows 7 35 196 73 304 40 64 128 256), losses := [] }

theorem u12507 : Upper (D 7) (R 7) [6,33,192,65,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12507 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12508 : PairBound 9 := { available := 138, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 196 73 304 48 202 138 394), lower := (rows 7 35 196 73 304 48 64 128 256), losses := [] }

theorem u12508 : Upper (D 7) (R 7) [6,33,192,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12508 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12509 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 73 304 160 90 154 282), lower := (rows 7 35 196 73 304 160 64 128 256), losses := [] }

theorem u12509 : Upper (D 7) (R 7) [6,33,192,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12510 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 73 400 34 120 184 312), lower := (rows 7 35 196 73 400 34 64 128 256), losses := [] }

theorem u12510 : Upper (D 7) (R 7) [6,33,192,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12511 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 400 40 114 178 306), lower := (rows 7 35 196 73 400 40 64 128 256), losses := [] }

theorem u12511 : Upper (D 7) (R 7) [6,33,192,65,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12511 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12512 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 72, targets := 128 }], pairs := [(1,6),(3,7),(4,6)], upper := (rows 7 35 196 73 400 48 106 170 298), lower := (rows 7 35 196 73 400 48 64 128 256), losses := [] }

theorem u12512 : Upper (D 7) (R 7) [6,33,192,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12512 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12513 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 152 33 368 432 304), lower := (rows 7 35 196 74 152 33 64 128 256), losses := [] }

theorem u12513 : Upper (D 7) (R 7) [6,33,192,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12514 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 452, targets := 2 },{ cop := 1, region := 328, targets := 128 }], pairs := [(2,1),(3,7),(4,1)], upper := (rows 7 35 196 74 152 48 353 417 289), lower := (rows 7 35 196 74 152 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 56 66 130 258), good := (rows 453 485 196 508 188 48 64 128 256) }] }

theorem u12514 : Upper (D 7) (R 7) [6,33,192,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12514 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12515 : Route 9 := (fun mask => (mask,id))

def c12515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12515 : Upper (D 7) (R 7) [6,33,192,66,136,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,136,256] 13 (by decide) (choices 1) [1,16,32] r12515 c12515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1298
  · exact u1299
  · exact u1300

def b12516 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 176 33 344 408 280), lower := (rows 7 35 196 74 176 33 64 128 256), losses := [] }

theorem u12516 : Upper (D 7) (R 7) [6,33,192,66,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12517 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 74 176 40 337 401 273), lower := (rows 7 35 196 74 176 40 64 128 256), losses := [] }

theorem u12517 : Upper (D 7) (R 7) [6,33,192,66,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12517 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12518 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 35 196 74 176 48 329 393 265), lower := (rows 7 35 196 74 176 48 64 128 256), losses := [] }

theorem u12518 : Upper (D 7) (R 7) [6,33,192,66,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12518 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12519 : Route 9 := (fun mask => (mask,id))

def c12519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12519 : Upper (D 7) (R 7) [6,33,192,66,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,160,256] 13 (by decide) (choices 1) [1,8,16] r12519 c12519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1301
  · exact u1302
  · exact u1303

def b12520 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 74 273 40 240 176 432), lower := (rows 7 35 196 74 273 40 64 128 256), losses := [] }

theorem u12520 : Upper (D 7) (R 7) [6,33,192,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12520 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12521 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,0),(3,0)], upper := (rows 7 35 196 74 273 48 232 168 424), lower := (rows 7 35 196 74 273 48 64 128 256), losses := [] }

theorem u12521 : Upper (D 7) (R 7) [6,33,192,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12521 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12522 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 74 273 160 120 184 312), lower := (rows 7 35 196 74 273 160 64 128 256), losses := [] }

theorem u12522 : Upper (D 7) (R 7) [6,33,192,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12523 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 280 33 240 176 432), lower := (rows 7 35 196 74 280 33 64 128 256), losses := [] }

theorem u12523 : Upper (D 7) (R 7) [6,33,192,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12524 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 196, targets := 2 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 35 196 74 280 48 225 161 417), lower := (rows 7 35 196 74 280 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 56 66 130 258), good := (rows 453 485 196 508 316 48 64 128 256) },{ target := 6, region := (rows 1 2 4 8 24 56 0 130 258), good := (rows 391 419 132 442 312 48 0 128 256) }] }

theorem u12524 : Upper (D 7) (R 7) [6,33,192,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12524 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12525 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 74 280 160 113 177 305), lower := (rows 7 35 196 74 280 160 64 128 256), losses := [] }

theorem u12525 : Upper (D 7) (R 7) [6,33,192,66,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12526 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 304 33 216 152 408), lower := (rows 7 35 196 74 304 33 64 128 256), losses := [] }

theorem u12526 : Upper (D 7) (R 7) [6,33,192,66,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12527 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 74 304 40 209 145 401), lower := (rows 7 35 196 74 304 40 64 128 256), losses := [] }

theorem u12527 : Upper (D 7) (R 7) [6,33,192,66,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12527 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12528 : PairBound 9 := { available := 137, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 7 35 196 74 304 48 201 137 393), lower := (rows 7 35 196 74 304 48 64 128 256), losses := [] }

theorem u12528 : Upper (D 7) (R 7) [6,33,192,66,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12529 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 74 304 160 89 153 281), lower := (rows 7 35 196 74 304 160 64 128 256), losses := [] }

theorem u12529 : Upper (D 7) (R 7) [6,33,192,66,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12530 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 74 400 33 120 184 312), lower := (rows 7 35 196 74 400 33 64 128 256), losses := [] }

theorem u12530 : Upper (D 7) (R 7) [6,33,192,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12531 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 43, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 74 400 40 113 177 305), lower := (rows 7 35 196 74 400 40 64 128 256), losses := [] }

theorem u12531 : Upper (D 7) (R 7) [6,33,192,66,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12531 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12532 : Route 9 := (fun mask => (mask,id))

def c12532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12532 : Upper (D 7) (R 7) [6,33,192,66,384,16] 13 := by
  apply FastRouting.sound _ _ [6,33,192,66,384,16] 13 (by decide) (choices 1) [1,8,32] r12532 c12532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1304
  · exact u1305
  · exact u1306

def b12533 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 476, targets := 1 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 176 33 330 394 266), lower := (rows 7 35 196 88 176 33 64 128 256), losses := [] }

theorem u12533 : Upper (D 7) (R 7) [6,33,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12534 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 476, targets := 2 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 7 35 196 88 176 34 329 393 265), lower := (rows 7 35 196 88 176 34 64 128 256), losses := [] }

theorem u12534 : Upper (D 7) (R 7) [6,33,192,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12535 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 196 88 176 40 323 387 259), lower := (rows 7 35 196 88 176 40 64 128 256), losses := [] }

theorem u12535 : Upper (D 7) (R 7) [6,33,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12535 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12536 : Route 9 := (fun mask => (mask,id))

def c12536 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12536 : Upper (D 7) (R 7) [6,33,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160,256] 13 (by decide) (choices 1) [1,2,8] r12536 c12536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1307
  · exact u1308
  · exact u1309

def b12537 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 192 }], pairs := [(0,6),(0,7),(1,6),(1,7)], upper := (rows 7 35 196 88 273 34 232 168 424), lower := (rows 7 35 196 88 273 34 64 128 256), losses := [] }

theorem u12537 : Upper (D 7) (R 7) [6,33,192,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r12538 : Route 9 := (fun mask => (mask,id))

def c12538 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12538 : Upper (D 7) (R 7) [6,33,192,80,257,8] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257,8] 13 (by decide) (choices 1) [2,32,128] r12538 c12538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1310
  · exact u1311
  · exact u1312

def b12539 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 344, targets := 128 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(1,6),(3,7),(4,7)], upper := (rows 7 35 196 88 273 160 106 170 298), lower := (rows 7 35 196 88 273 160 64 128 256), losses := [] }

theorem u12539 : Upper (D 7) (R 7) [6,33,192,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u12539
end Delivery.IrregularNine14.P07
