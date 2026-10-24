import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0088

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19500 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 140 56 274 33 193 193 449), lower := (rows 35 70 140 56 274 33 64 128 256), losses := [] }

theorem u19500 : Upper (D 7) (R 7) [34,68,136,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19501 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(2,6),(3,6),(4,5),(4,6)], upper := (rows 35 70 140 56 274 96 193 129 385), lower := (rows 35 70 140 56 274 96 64 128 256), losses := [] }

theorem u19501 : Upper (D 7) (R 7) [34,68,136,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19501 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19502 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 }], pairs := [(0,6),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 56 274 160 65 193 321), lower := (rows 35 70 140 56 274 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 164 0 128 256), good := (rows 35 39 172 56 275 160 0 160 256) }] }

theorem u19502 : Upper (D 7) (R 7) [34,68,136,48,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19502 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19503 : Route 9 := (fun mask => (mask,id))

def c19503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19503 : Upper (D 7) (R 7) [34,68,136,48,320,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,48,320,1] 13 (by decide) (choices 1) [1,2,128] r19503 c19503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5309
  · exact u5310
  · exact u5311

def b19504 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,1),(4,5)], upper := (rows 35 70 140 56 336 34 193 129 385), lower := (rows 35 70 140 56 336 34 64 128 256), losses := [] }

theorem u19504 : Upper (D 7) (R 7) [34,68,136,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19505 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 0, region := 336, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,7),(4,5),(4,7)], upper := (rows 35 70 140 56 336 160 67 131 259), lower := (rows 35 70 140 56 336 160 64 128 256), losses := [] }

theorem u19505 : Upper (D 7) (R 7) [34,68,136,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19505 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19506 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(4,5)], upper := (rows 35 70 140 56 400 33 67 195 323), lower := (rows 35 70 140 56 400 33 64 128 256), losses := [] }

theorem u19506 : Upper (D 7) (R 7) [34,68,136,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19507 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 56 400 34 65 193 321), lower := (rows 35 70 140 56 400 34 64 128 256), losses := [] }

theorem u19507 : Upper (D 7) (R 7) [34,68,136,48,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19507 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19508 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 70 140 56 400 96 67 131 259), lower := (rows 35 70 140 56 400 96 64 128 256), losses := [] }

theorem u19508 : Upper (D 7) (R 7) [34,68,136,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19508 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19509 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 145 34 368 432 304), lower := (rows 35 70 140 73 145 34 64 128 256), losses := [] }

theorem u19509 : Upper (D 7) (R 7) [34,68,136,65,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19509 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19510 : PairBound 9 := { available := 290, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 }], pairs := [(0,6),(3,7),(4,6)], upper := (rows 35 70 140 73 145 48 354 418 290), lower := (rows 35 70 140 73 145 48 64 128 256), losses := [] }

theorem u19510 : Upper (D 7) (R 7) [34,68,136,65,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19510 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19511 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 73 145 288 114 178 306), lower := (rows 35 70 140 73 145 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 27 315 0 131 259), good := (rows 435 439 188 445 433 288 0 128 288) }] }

theorem u19511 : Upper (D 7) (R 7) [34,68,136,65,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19511 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19512 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 176 33 338 402 274), lower := (rows 35 70 140 73 176 33 64 128 256), losses := [] }

theorem u19512 : Upper (D 7) (R 7) [34,68,136,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19512 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19513 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 176 34 337 401 273), lower := (rows 35 70 140 73 176 34 64 128 256), losses := [] }

theorem u19513 : Upper (D 7) (R 7) [34,68,136,65,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19514 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 73 176 48 323 387 259), lower := (rows 35 70 140 73 176 48 64 128 256), losses := [] }

theorem u19514 : Upper (D 7) (R 7) [34,68,136,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19514 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19515 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 140 73 176 288 83 147 275), lower := (rows 35 70 140 73 176 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 31 299 0 131 259), good := (rows 435 439 188 445 176 288 0 128 288) }] }

theorem u19515 : Upper (D 7) (R 7) [34,68,136,65,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19515 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19516 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 273 34 240 176 432), lower := (rows 35 70 140 73 273 34 64 128 256), losses := [] }

theorem u19516 : Upper (D 7) (R 7) [34,68,136,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19517 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 70 140 73 273 48 226 162 418), lower := (rows 35 70 140 73 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 65 129 257), good := (rows 482 70 142 462 496 48 64 128 256) }] }

theorem u19517 : Upper (D 7) (R 7) [34,68,136,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19517 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19518 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 73 273 160 114 178 306), lower := (rows 35 70 140 73 273 160 64 128 256), losses := [] }

theorem u19518 : Upper (D 7) (R 7) [34,68,136,65,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19519 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 274 33 240 176 432), lower := (rows 35 70 140 73 274 33 64 128 256), losses := [] }

theorem u19519 : Upper (D 7) (R 7) [34,68,136,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19520 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 140 73 274 48 225 161 417), lower := (rows 35 70 140 73 274 48 64 128 256), losses := [] }

theorem u19520 : Upper (D 7) (R 7) [34,68,136,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19520 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19521 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 73 274 160 113 177 305), lower := (rows 35 70 140 73 274 160 64 128 256), losses := [] }

theorem u19521 : Upper (D 7) (R 7) [34,68,136,65,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19522 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 304 33 210 146 402), lower := (rows 35 70 140 73 304 33 64 128 256), losses := [] }

theorem u19522 : Upper (D 7) (R 7) [34,68,136,65,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19523 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 304 34 209 145 401), lower := (rows 35 70 140 73 304 34 64 128 256), losses := [] }

theorem u19523 : Upper (D 7) (R 7) [34,68,136,65,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19524 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 70 140 73 304 48 195 131 387), lower := (rows 35 70 140 73 304 48 64 128 256), losses := [] }

theorem u19524 : Upper (D 7) (R 7) [34,68,136,65,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19524 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19525 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 73 304 160 83 147 275), lower := (rows 35 70 140 73 304 160 64 128 256), losses := [] }

theorem u19525 : Upper (D 7) (R 7) [34,68,136,65,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19526 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 73 400 33 114 178 306), lower := (rows 35 70 140 73 400 33 64 128 256), losses := [] }

theorem u19526 : Upper (D 7) (R 7) [34,68,136,65,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19527 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 73 400 34 113 177 305), lower := (rows 35 70 140 73 400 34 64 128 256), losses := [] }

theorem u19527 : Upper (D 7) (R 7) [34,68,136,65,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19528 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 72, targets := 128 }], pairs := [(0,6),(3,7),(4,6)], upper := (rows 35 70 140 73 400 48 99 163 291), lower := (rows 35 70 140 73 400 48 64 128 256), losses := [] }

theorem u19528 : Upper (D 7) (R 7) [34,68,136,65,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19528 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19529 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,6)], upper := (rows 35 70 140 88 273 33 226 162 418), lower := (rows 35 70 140 88 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 26 20 24 16 32 65 129 257), good := (rows 482 70 142 94 478 480 64 128 256) }] }

theorem u19529 : Upper (D 7) (R 7) [34,68,136,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19530 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 88 273 34 225 161 417), lower := (rows 35 70 140 88 273 34 64 128 256), losses := [] }

theorem u19530 : Upper (D 7) (R 7) [34,68,136,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19531 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 88 273 160 99 163 291), lower := (rows 35 70 140 88 273 160 64 128 256), losses := [] }

theorem u19531 : Upper (D 7) (R 7) [34,68,136,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19532 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(4,6)], upper := (rows 35 70 140 88 274 33 225 161 417), lower := (rows 35 70 140 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 19 59 0 187 315), good := (rows 435 439 428 445 435 433 0 128 256) }] }

theorem u19532 : Upper (D 7) (R 7) [34,68,136,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19533 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 88 274 160 97 161 289), lower := (rows 35 70 140 88 274 160 64 128 256), losses := [] }

theorem u19533 : Upper (D 7) (R 7) [34,68,136,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19534 : Route 9 := (fun mask => (mask,id))

def c19534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u19534 : Upper (D 7) (R 7) [34,68,136,80,288,1] 13 := by
  apply FastRouting.sound _ _ [34,68,136,80,288,1] 13 (by decide) (choices 1) [1,2,128] r19534 c19534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5312
  · exact u5313
  · exact u5314

def b19535 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 88 304 34 193 129 385), lower := (rows 35 70 140 88 304 34 64 128 256), losses := [] }

theorem u19535 : Upper (D 7) (R 7) [34,68,136,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19536 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 88 304 160 67 131 259), lower := (rows 35 70 140 88 304 160 64 128 256), losses := [] }

theorem u19536 : Upper (D 7) (R 7) [34,68,136,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19537 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 145 33 338 402 274), lower := (rows 35 70 140 104 145 33 64 128 256), losses := [] }

theorem u19537 : Upper (D 7) (R 7) [34,68,136,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19538 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 104 145 34 337 401 273), lower := (rows 35 70 140 104 145 34 64 128 256), losses := [] }

theorem u19538 : Upper (D 7) (R 7) [34,68,136,96,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19539 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 140 104 145 48 323 387 259), lower := (rows 35 70 140 104 145 48 64 128 256), losses := [] }

theorem u19539 : Upper (D 7) (R 7) [34,68,136,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19539 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19540 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 140 104 145 288 83 147 275), lower := (rows 35 70 140 104 145 288 64 128 256), losses := [] }

theorem u19540 : Upper (D 7) (R 7) [34,68,136,96,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19540 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19541 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 273 33 210 146 402), lower := (rows 35 70 140 104 273 33 64 128 256), losses := [] }

theorem u19541 : Upper (D 7) (R 7) [34,68,136,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19541 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19542 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 104 273 34 209 145 401), lower := (rows 35 70 140 104 273 34 64 128 256), losses := [] }

theorem u19542 : Upper (D 7) (R 7) [34,68,136,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19542 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19543 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 140 104 273 48 195 131 387), lower := (rows 35 70 140 104 273 48 64 128 256), losses := [] }

theorem u19543 : Upper (D 7) (R 7) [34,68,136,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19543 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19544 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 104 273 160 83 147 275), lower := (rows 35 70 140 104 273 160 64 128 256), losses := [] }

theorem u19544 : Upper (D 7) (R 7) [34,68,136,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19545 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 274 33 209 145 401), lower := (rows 35 70 140 104 274 33 64 128 256), losses := [] }

theorem u19545 : Upper (D 7) (R 7) [34,68,136,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19546 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 70 140 104 274 48 193 129 385), lower := (rows 35 70 140 104 274 48 64 128 256), losses := [] }

theorem u19546 : Upper (D 7) (R 7) [34,68,136,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19546 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19547 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 140 104 274 160 81 145 273), lower := (rows 35 70 140 104 274 160 64 128 256), losses := [] }

theorem u19547 : Upper (D 7) (R 7) [34,68,136,96,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19548 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 41, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 70 140 104 400 33 83 147 275), lower := (rows 35 70 140 104 400 33 64 128 256), losses := [] }

theorem u19548 : Upper (D 7) (R 7) [34,68,136,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19549 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 104 400 34 81 145 273), lower := (rows 35 70 140 104 400 34 64 128 256), losses := [] }

theorem u19549 : Upper (D 7) (R 7) [34,68,136,96,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19549 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19550 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 70 140 104 400 48 67 131 259), lower := (rows 35 70 140 104 400 48 64 128 256), losses := [] }

theorem u19550 : Upper (D 7) (R 7) [34,68,136,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19550 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19551 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 81 34 240 176 432), lower := (rows 35 70 140 265 81 34 64 128 256), losses := [] }

theorem u19551 : Upper (D 7) (R 7) [34,68,136,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19551 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19552 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 70 140 265 81 48 226 162 418), lower := (rows 35 70 140 265 81 48 64 128 256), losses := [] }

theorem u19552 : Upper (D 7) (R 7) [34,68,136,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19552 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19553 : Route 9 := (fun mask => (mask,id))

def c19553 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19553 : Upper (D 7) (R 7) [34,68,136,257,65,128] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,65,128] 13 (by decide) (choices 1) [2,16,32] r19553 c19553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5315
  · exact u5316
  · exact u5317

def b19554 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(4,0),(4,7)], upper := (rows 35 70 140 265 112 33 210 146 402), lower := (rows 35 70 140 265 112 33 64 128 256), losses := [] }

theorem u19554 : Upper (D 7) (R 7) [34,68,136,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19554 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19555 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 112 34 209 145 401), lower := (rows 35 70 140 265 112 34 64 128 256), losses := [] }

theorem u19555 : Upper (D 7) (R 7) [34,68,136,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19555 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19556 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 140 265 112 48 195 131 387), lower := (rows 35 70 140 265 112 48 64 128 256), losses := [] }

theorem u19556 : Upper (D 7) (R 7) [34,68,136,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19556 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19557 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 35 70 140 265 112 160 83 147 275), lower := (rows 35 70 140 265 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 164 64 128 256), good := (rows 50 118 172 264 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 18 164 64 128 256), good := (rows 49 116 172 265 112 160 64 160 256) }] }

theorem u19557 : Upper (D 7) (R 7) [34,68,136,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19557 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19558 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 140 265 145 34 112 240 368), lower := (rows 35 70 140 265 145 34 64 128 256), losses := [] }

theorem u19558 : Upper (D 7) (R 7) [34,68,136,257,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19559 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(1,0),(2,0),(3,7)], upper := (rows 35 70 140 265 145 48 98 226 354), lower := (rows 35 70 140 265 145 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 65 129 257), good := (rows 482 70 142 462 496 48 64 128 256) }] }

theorem u19559 : Upper (D 7) (R 7) [34,68,136,257,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19559 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19559
end Delivery.IrregularNine14.P07
