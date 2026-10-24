import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0001

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r480 : Route 9 := (fun mask => (mask,id))

def c480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u480 : Upper (D 10) (R 10) [6,40,96,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192,1] 13 (by decide) (choices 1) [16,32,256] r480 c480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u76
  · exact u77
  · exact u78

def b481 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 392 208 48 353 417 289), lower := (rows 7 42 100 392 208 48 64 128 256), losses := [] }

theorem u481 : Upper (D 10) (R 10) [6,40,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b481 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 100 392 208 288 113 177 305), lower := (rows 7 42 100 392 208 288 64 128 256), losses := [] }

theorem u482 : Upper (D 10) (R 10) [6,40,96,384,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b482 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 59, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 196 88 176 33 352 416 288), lower := (rows 7 42 196 88 176 33 64 128 256), losses := [] }

theorem u483 : Upper (D 10) (R 10) [6,40,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b483 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r484 : Route 9 := (fun mask => (mask,id))

def c484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u484 : Upper (D 10) (R 10) [6,40,192,80,160,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160,256] 13 (by decide) (choices 1) [1,32,256] r484 c484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u79
  · exact u80
  · exact u81

def b485 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 88 304 33 480 416 416), lower := (rows 7 42 196 88 304 33 64 128 256), losses := [] }

theorem u485 : Upper (D 10) (R 10) [6,40,192,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b485 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r486 : Route 9 := (fun mask => (mask,id))

def c486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u486 : Upper (D 10) (R 10) [6,40,192,80,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,128] 13 (by decide) (choices 1) [1,32,256] r486 c486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u82
  · exact u83
  · exact u84

def b487 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 196 88 304 288 225 161 417), lower := (rows 7 42 196 88 304 288 64 128 256), losses := [] }

theorem u487 : Upper (D 10) (R 10) [6,40,192,80,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b487 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 88 400 33 352 416 288), lower := (rows 7 42 196 88 400 33 64 128 256), losses := [] }

theorem u488 : Upper (D 10) (R 10) [6,40,192,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b488 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 88 400 288 97 161 289), lower := (rows 7 42 196 88 400 288 64 128 256), losses := [] }

theorem u489 : Upper (D 10) (R 10) [6,40,192,80,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b489 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 42 196 265 112 48 480 416 416), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u490 : Upper (D 10) (R 10) [6,40,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b490 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 336, targets := 128 },{ cop := 2, region := 48, targets := 256 }], pairs := [(4,7),(4,8)], upper := (rows 7 42 196 265 112 160 368 432 304), lower := (rows 7 42 196 265 112 160 64 128 256), losses := [] }

theorem u491 : Upper (D 10) (R 10) [6,40,192,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b491 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 265 112 288 240 176 432), lower := (rows 7 42 196 265 112 288 64 128 256), losses := [] }

theorem u492 : Upper (D 10) (R 10) [6,40,192,257,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b492 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 265 304 48 224 224 480), lower := (rows 7 42 196 265 304 48 64 128 256), losses := [] }

theorem u493 : Upper (D 10) (R 10) [6,40,192,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b493 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 400, targets := 64 },{ cop := 4, region := 196, targets := 256 }], pairs := [(2,8),(4,6)], upper := (rows 7 42 196 265 304 96 240 176 432), lower := (rows 7 42 196 265 304 96 64 128 256), losses := [] }

theorem u494 : Upper (D 10) (R 10) [6,40,192,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b494 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 196 265 336 48 224 160 416), lower := (rows 7 42 196 265 336 48 64 128 256), losses := [] }

theorem u495 : Upper (D 10) (R 10) [6,40,192,257,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b495 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 336, targets := 128 },{ cop := 4, region := 164, targets := 256 }], pairs := [(2,8),(4,7)], upper := (rows 7 42 196 265 336 160 112 176 304), lower := (rows 7 42 196 265 336 160 64 128 256), losses := [] }

theorem u496 : Upper (D 10) (R 10) [6,40,192,257,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b496 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6),(3,6)], upper := (rows 7 42 196 280 49 96 480 416 416), lower := (rows 7 42 196 280 49 96 64 128 256), losses := [] }

theorem u497 : Upper (D 10) (R 10) [6,40,192,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b497 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 280 49 288 224 224 480), lower := (rows 7 42 196 280 49 288 64 128 256), losses := [] }

theorem u498 : Upper (D 10) (R 10) [6,40,192,272,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b498 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 280 112 33 480 416 416), lower := (rows 7 42 196 280 112 33 64 128 256), losses := [] }

theorem u499 : Upper (D 10) (R 10) [6,40,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b499 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r500 : Route 9 := (fun mask => (mask,id))

def c500 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u500 : Upper (D 10) (R 10) [6,40,192,272,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96,128] 13 (by decide) (choices 1) [1,32,256] r500 c500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u85
  · exact u86
  · exact u87

def b501 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 280 112 288 225 161 417), lower := (rows 7 42 196 280 112 288 64 128 256), losses := [] }

theorem u501 : Upper (D 10) (R 10) [6,40,192,272,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b501 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 42 196 328 49 48 480 416 416), lower := (rows 7 42 196 328 49 48 64 128 256), losses := [] }

theorem u502 : Upper (D 10) (R 10) [6,40,192,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b502 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 42 196 328 49 160 368 432 304), lower := (rows 7 42 196 328 49 160 64 128 256), losses := [] }

theorem u503 : Upper (D 10) (R 10) [6,40,192,320,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b503 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 328 49 288 240 176 432), lower := (rows 7 42 196 328 49 288 64 128 256), losses := [] }

theorem u504 : Upper (D 10) (R 10) [6,40,192,320,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b504 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 196 328 176 33 368 432 304), lower := (rows 7 42 196 328 176 33 64 128 256), losses := [] }

theorem u505 : Upper (D 10) (R 10) [6,40,192,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b505 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 328 176 48 353 417 289), lower := (rows 7 42 196 328 176 48 64 128 256), losses := [] }

theorem u506 : Upper (D 10) (R 10) [6,40,192,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b506 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 213, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 42 196 328 176 288 113 177 305), lower := (rows 7 42 196 328 176 288 64 128 256), losses := [] }

theorem u507 : Upper (D 10) (R 10) [6,40,192,320,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b507 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 328 304 33 240 176 432), lower := (rows 7 42 196 328 304 33 64 128 256), losses := [] }

theorem u508 : Upper (D 10) (R 10) [6,40,192,320,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b508 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 50, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 328 304 48 225 161 417), lower := (rows 7 42 196 328 304 48 64 128 256), losses := [] }

theorem u509 : Upper (D 10) (R 10) [6,40,192,320,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b509 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r510 : Route 9 := (fun mask => (mask,id))

def c510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u510 : Upper (D 10) (R 10) [6,40,192,320,288,128] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288,128] 13 (by decide) (choices 1) [1,16,32] r510 c510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u88
  · exact u89
  · exact u90

def b511 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 196 328 400 33 112 176 304), lower := (rows 7 42 196 328 400 33 64 128 256), losses := [] }

theorem u511 : Upper (D 10) (R 10) [6,40,192,320,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b511 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 196 328 400 48 97 161 289), lower := (rows 7 42 196 328 400 48 64 128 256), losses := [] }

theorem u512 : Upper (D 10) (R 10) [6,40,192,320,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b512 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 67 140 296 176 48 352 480 352), lower := (rows 7 67 140 296 176 48 64 128 256), losses := [] }

theorem u513 : Upper (D 10) (R 10) [6,65,136,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b513 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 304, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 296 176 96 368 432 304), lower := (rows 7 67 140 296 176 96 64 128 256), losses := [] }

theorem u514 : Upper (D 10) (R 10) [6,65,136,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b514 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 140 296 176 288 112 240 368), lower := (rows 7 67 140 296 176 288 64 128 256), losses := [] }

theorem u515 : Upper (D 10) (R 10) [6,65,136,288,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b515 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 67 140 296 400 48 96 224 352), lower := (rows 7 67 140 296 400 48 64 128 256), losses := [] }

theorem u516 : Upper (D 10) (R 10) [6,65,136,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b516 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 140 296 400 96 112 176 304), lower := (rows 7 67 140 296 400 96 64 128 256), losses := [] }

theorem u517 : Upper (D 10) (R 10) [6,65,136,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b517 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 416, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 56 280 96 480 416 416), lower := (rows 7 67 164 56 280 96 64 128 256), losses := [] }

theorem u518 : Upper (D 10) (R 10) [6,65,160,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b518 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 67 164 56 280 160 352 480 352), lower := (rows 7 67 164 56 280 160 64 128 256), losses := [] }

theorem u519 : Upper (D 10) (R 10) [6,65,160,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b519 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 67 164 56 280 288 224 224 480), lower := (rows 7 67 164 56 280 288 64 128 256), losses := [] }

theorem u520 : Upper (D 10) (R 10) [6,65,160,48,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b520 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 7 67 164 56 400 40 352 480 352), lower := (rows 7 67 164 56 400 40 64 128 256), losses := [] }

theorem u521 : Upper (D 10) (R 10) [6,65,160,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b521 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 56 400 96 360 424 296), lower := (rows 7 67 164 56 400 96 64 128 256), losses := [] }

theorem u522 : Upper (D 10) (R 10) [6,65,160,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b522 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 164 56 400 288 104 232 360), lower := (rows 7 67 164 56 400 288 64 128 256), losses := [] }

theorem u523 : Upper (D 10) (R 10) [6,65,160,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b523 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 152 304 40 352 480 352), lower := (rows 7 67 164 152 304 40 64 128 256), losses := [] }

theorem u524 : Upper (D 10) (R 10) [6,65,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b524 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 152 304 96 360 424 296), lower := (rows 7 67 164 152 304 96 64 128 256), losses := [] }

theorem u525 : Upper (D 10) (R 10) [6,65,160,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b525 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 104, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 67 164 152 304 288 104 232 360), lower := (rows 7 67 164 152 304 288 64 128 256), losses := [] }

theorem u526 : Upper (D 10) (R 10) [6,65,160,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b526 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 7 67 164 296 400 40 112 240 368), lower := (rows 7 67 164 296 400 40 64 128 256), losses := [] }

theorem u527 : Upper (D 10) (R 10) [6,65,160,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b527 [(5,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 296 400 48 104 232 360), lower := (rows 7 67 164 296 400 48 64 128 256), losses := [] }

theorem u528 : Upper (D 10) (R 10) [6,65,160,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b528 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 412, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 67 164 296 400 96 120 184 312), lower := (rows 7 67 164 296 400 96 64 128 256), losses := [] }

theorem u529 : Upper (D 10) (R 10) [6,65,160,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b529 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 148 41 304 96 480 416 416), lower := (rows 7 74 148 41 304 96 64 128 256), losses := [] }

theorem u530 : Upper (D 10) (R 10) [6,72,144,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b530 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 338, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 41 304 160 352 480 352), lower := (rows 7 74 148 41 304 160 64 128 256), losses := [] }

theorem u531 : Upper (D 10) (R 10) [6,72,144,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b531 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 148 41 304 288 224 224 480), lower := (rows 7 74 148 41 304 288 64 128 256), losses := [] }

theorem u532 : Upper (D 10) (R 10) [6,72,144,33,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b532 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 148 168 304 33 352 480 352), lower := (rows 7 74 148 168 304 33 64 128 256), losses := [] }

theorem u533 : Upper (D 10) (R 10) [6,72,144,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b533 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r534 : Route 9 := (fun mask => (mask,id))

def c534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u534 : Upper (D 10) (R 10) [6,72,144,160,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,144,160,288,64] 13 (by decide) (choices 1) [1,32,256] r534 c534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u91
  · exact u92
  · exact u93

def b535 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 148 168 304 288 97 225 353), lower := (rows 7 74 148 168 304 288 64 128 256), losses := [] }

theorem u535 : Upper (D 10) (R 10) [6,72,144,160,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b535 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 7 74 148 296 336 33 224 160 416), lower := (rows 7 74 148 296 336 33 64 128 256), losses := [] }

theorem u536 : Upper (D 10) (R 10) [6,72,144,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b536 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r537 : Route 9 := (fun mask => (mask,id))

def c537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u537 : Upper (D 10) (R 10) [6,72,144,288,320,128] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,320,128] 13 (by decide) (choices 1) [1,32] r537 c537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u94
  · exact u95

def b538 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 41 112 48 448 384 384), lower := (rows 7 74 164 41 112 48 64 128 256), losses := [] }

theorem u538 : Upper (D 10) (R 10) [6,72,160,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b538 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 41 112 160 336 400 272), lower := (rows 7 74 164 41 112 160 64 128 256), losses := [] }

theorem u539 : Upper (D 10) (R 10) [6,72,160,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b539 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P10
