import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0001
import IrregularNine14P10C0002

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r540 : Route 9 := (fun mask => (mask,id))

def c540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u540 : Upper (D 10) (R 10) [6,72,160,33,96,256] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,96,256] 13 (by decide) (choices 1) [16,128,256] r540 c540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u96
  · exact u97
  · exact u98

def b541 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 41 208 48 352 416 288), lower := (rows 7 74 164 41 208 48 64 128 256), losses := [] }

theorem u541 : Upper (D 10) (R 10) [6,72,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b541 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r542 : Route 9 := (fun mask => (mask,id))

def c542 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u542 : Upper (D 10) (R 10) [6,72,160,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,192,256] 13 (by decide) (choices 1) [16,32,256] r542 c542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u99
  · exact u100
  · exact u101

def b543 : PairBound 9 := { available := 448, camps := [{ cop := 8, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 164 41 304 48 448 448 448), lower := (rows 7 74 164 41 304 48 64 128 256), losses := [] }

theorem u543 : Upper (D 10) (R 10) [6,72,160,33,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b543 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b544 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 164 41 304 96 464 400 400), lower := (rows 7 74 164 41 304 96 64 128 256), losses := [] }

theorem u544 : Upper (D 10) (R 10) [6,72,160,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b544 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b545 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 41 304 160 336 464 336), lower := (rows 7 74 164 41 304 160 64 128 256), losses := [] }

theorem u545 : Upper (D 10) (R 10) [6,72,160,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b545 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b546 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 41 304 288 208 208 464), lower := (rows 7 74 164 41 304 288 64 128 256), losses := [] }

theorem u546 : Upper (D 10) (R 10) [6,72,160,33,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b546 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b547 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 41 336 48 480 416 416), lower := (rows 7 74 164 41 336 48 64 128 256), losses := [] }

theorem u547 : Upper (D 10) (R 10) [6,72,160,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b547 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b548 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 41 336 160 368 432 304), lower := (rows 7 74 164 41 336 160 64 128 256), losses := [] }

theorem u548 : Upper (D 10) (R 10) [6,72,160,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b548 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r549 : Route 9 := (fun mask => (mask,id))

def c549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u549 : Upper (D 10) (R 10) [6,72,160,33,320,256] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,320,256] 13 (by decide) (choices 1) [16,32,128] r549 c549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u102
  · exact u103
  · exact u104

def b550 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 41 400 48 352 480 352), lower := (rows 7 74 164 41 400 48 64 128 256), losses := [] }

theorem u550 : Upper (D 10) (R 10) [6,72,160,33,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b550 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b551 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 164 41 400 96 368 432 304), lower := (rows 7 74 164 41 400 96 64 128 256), losses := [] }

theorem u551 : Upper (D 10) (R 10) [6,72,160,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b551 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r552 : Route 9 := (fun mask => (mask,id))

def c552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u552 : Upper (D 10) (R 10) [6,72,160,33,384,256] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,384,256] 13 (by decide) (choices 1) [16,32] r552 c552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u105
  · exact u106

def b553 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 388, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 56 273 96 480 416 416), lower := (rows 7 74 164 56 273 96 64 128 256), losses := [{ target := 6, region := (rows 3 2 44 8 19 32 0 172 300), good := (rows 407 415 420 444 273 420 0 128 256) }] }

theorem u553 : Upper (D 10) (R 10) [6,72,160,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b553 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b554 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 56 273 160 352 480 352), lower := (rows 7 74 164 56 273 160 64 128 256), losses := [] }

theorem u554 : Upper (D 10) (R 10) [6,72,160,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b554 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b555 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 56 273 288 224 224 480), lower := (rows 7 74 164 56 273 288 64 128 256), losses := [] }

theorem u555 : Upper (D 10) (R 10) [6,72,160,48,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b555 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b556 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 322, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 164 56 400 33 352 480 352), lower := (rows 7 74 164 56 400 33 64 128 256), losses := [] }

theorem u556 : Upper (D 10) (R 10) [6,72,160,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b556 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r557 : Route 9 := (fun mask => (mask,id))

def c557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u557 : Upper (D 10) (R 10) [6,72,160,48,384,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,384,64] 13 (by decide) (choices 1) [1,32,256] r557 c557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u107
  · exact u108
  · exact u109

def b558 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 56 400 288 97 225 353), lower := (rows 7 74 164 56 400 288 64 128 256), losses := [] }

theorem u558 : Upper (D 10) (R 10) [6,72,160,48,384,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b558 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b559 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 152 304 33 352 480 352), lower := (rows 7 74 164 152 304 33 64 128 256), losses := [] }

theorem u559 : Upper (D 10) (R 10) [6,72,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b559 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r560 : Route 9 := (fun mask => (mask,id))

def c560 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u560 : Upper (D 10) (R 10) [6,72,160,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,144,288,64] 13 (by decide) (choices 1) [1,32,256] r560 c560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u110
  · exact u111
  · exact u112

def b561 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 207, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 152 304 288 97 225 353), lower := (rows 7 74 164 152 304 288 64 128 256), losses := [] }

theorem u561 : Upper (D 10) (R 10) [6,72,160,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b561 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b562 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 265 112 48 480 416 416), lower := (rows 7 74 164 265 112 48 64 128 256), losses := [] }

theorem u562 : Upper (D 10) (R 10) [6,72,160,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b562 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b563 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 265 112 160 368 432 304), lower := (rows 7 74 164 265 112 160 64 128 256), losses := [] }

theorem u563 : Upper (D 10) (R 10) [6,72,160,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b563 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b564 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 212, targets := 256 }], pairs := [(2,8),(4,8)], upper := (rows 7 74 164 265 112 288 240 176 432), lower := (rows 7 74 164 265 112 288 64 128 256), losses := [] }

theorem u564 : Upper (D 10) (R 10) [6,72,160,257,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b564 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b565 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 265 208 48 352 416 288), lower := (rows 7 74 164 265 208 48 64 128 256), losses := [] }

theorem u565 : Upper (D 10) (R 10) [6,72,160,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b565 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b566 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 212, targets := 256 }], pairs := [(2,8),(4,8)], upper := (rows 7 74 164 265 208 288 112 176 304), lower := (rows 7 74 164 265 208 288 64 128 256), losses := [] }

theorem u566 : Upper (D 10) (R 10) [6,72,160,257,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b566 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b567 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 164 265 304 48 224 224 480), lower := (rows 7 74 164 265 304 48 64 128 256), losses := [] }

theorem u567 : Upper (D 10) (R 10) [6,72,160,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b567 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b568 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 164 265 304 96 240 176 432), lower := (rows 7 74 164 265 304 96 64 128 256), losses := [] }

theorem u568 : Upper (D 10) (R 10) [6,72,160,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b568 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b569 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 265 304 160 112 240 368), lower := (rows 7 74 164 265 304 160 64 128 256), losses := [] }

theorem u569 : Upper (D 10) (R 10) [6,72,160,257,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b569 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b570 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 265 400 48 96 224 352), lower := (rows 7 74 164 265 400 48 64 128 256), losses := [] }

theorem u570 : Upper (D 10) (R 10) [6,72,160,257,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b570 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b571 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 74 164 265 400 96 112 176 304), lower := (rows 7 74 164 265 400 96 64 128 256), losses := [] }

theorem u571 : Upper (D 10) (R 10) [6,72,160,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b571 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b572 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 164 280 49 96 480 416 416), lower := (rows 7 74 164 280 49 96 64 128 256), losses := [] }

theorem u572 : Upper (D 10) (R 10) [6,72,160,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b572 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b573 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 280 49 160 352 480 352), lower := (rows 7 74 164 280 49 160 64 128 256), losses := [] }

theorem u573 : Upper (D 10) (R 10) [6,72,160,272,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b573 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b574 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 196, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 74 164 280 49 288 224 224 480), lower := (rows 7 74 164 280 49 288 64 128 256), losses := [{ target := 8, region := (rows 9 10 52 8 16 32 116 180 0), good := (rows 199 75 228 223 245 228 64 128 0) }] }

theorem u574 : Upper (D 10) (R 10) [6,72,160,272,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b574 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b575 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 164 296 49 48 448 448 448), lower := (rows 7 74 164 296 49 48 64 128 256), losses := [] }

theorem u575 : Upper (D 10) (R 10) [6,72,160,288,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b575 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b576 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 164 296 49 96 464 400 400), lower := (rows 7 74 164 296 49 96 64 128 256), losses := [] }

theorem u576 : Upper (D 10) (R 10) [6,72,160,288,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b576 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b577 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 296 49 160 336 464 336), lower := (rows 7 74 164 296 49 160 64 128 256), losses := [] }

theorem u577 : Upper (D 10) (R 10) [6,72,160,288,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b577 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b578 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 296 49 288 208 208 464), lower := (rows 7 74 164 296 49 288 64 128 256), losses := [] }

theorem u578 : Upper (D 10) (R 10) [6,72,160,288,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b578 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b579 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 296 112 33 464 400 400), lower := (rows 7 74 164 296 112 33 64 128 256), losses := [] }

theorem u579 : Upper (D 10) (R 10) [6,72,160,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b579 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b580 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 296 112 48 449 385 385), lower := (rows 7 74 164 296 112 48 64 128 256), losses := [] }

theorem u580 : Upper (D 10) (R 10) [6,72,160,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b580 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b581 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 296 112 160 337 401 273), lower := (rows 7 74 164 296 112 160 64 128 256), losses := [] }

theorem u581 : Upper (D 10) (R 10) [6,72,160,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b581 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b582 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 296 112 288 209 145 401), lower := (rows 7 74 164 296 112 288 64 128 256), losses := [] }

theorem u582 : Upper (D 10) (R 10) [6,72,160,288,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b582 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r583 : Route 9 := (fun mask => (mask,id))

def c583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u583 : Upper (D 10) (R 10) [6,72,160,288,192,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,192,1] 13 (by decide) (choices 1) [16,32,256] r583 c583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u113
  · exact u114
  · exact u115

def b584 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 296 208 48 353 417 289), lower := (rows 7 74 164 296 208 48 64 128 256), losses := [] }

theorem u584 : Upper (D 10) (R 10) [6,72,160,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b584 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b585 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 215, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 296 208 288 113 177 305), lower := (rows 7 74 164 296 208 288 64 128 256), losses := [] }

theorem u585 : Upper (D 10) (R 10) [6,72,160,288,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b585 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b586 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 273 48 224 224 480), lower := (rows 7 74 164 296 273 48 64 128 256), losses := [] }

theorem u586 : Upper (D 10) (R 10) [6,72,160,288,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b586 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r587 : Route 9 := (fun mask => (mask,id))

def c587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u587 : Upper (D 10) (R 10) [6,72,160,288,257,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,257,64] 13 (by decide) (choices 1) [16,32,128] r587 c587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u116
  · exact u117
  · exact u118

def b588 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 296 273 160 112 240 368), lower := (rows 7 74 164 296 273 160 64 128 256), losses := [] }

theorem u588 : Upper (D 10) (R 10) [6,72,160,288,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b588 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r589 : Route 9 := (fun mask => (mask,id))

def c589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u589 : Upper (D 10) (R 10) [6,72,160,288,320,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,320,1] 13 (by decide) (choices 1) [16,32,128] r589 c589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u119
  · exact u120
  · exact u121

def b590 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 336 48 225 161 417), lower := (rows 7 74 164 296 336 48 64 128 256), losses := [] }

theorem u590 : Upper (D 10) (R 10) [6,72,160,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b590 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b591 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 164 296 336 160 113 177 305), lower := (rows 7 74 164 296 336 160 64 128 256), losses := [] }

theorem u591 : Upper (D 10) (R 10) [6,72,160,288,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b591 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r592 : Route 9 := (fun mask => (mask,id))

def c592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u592 : Upper (D 10) (R 10) [6,72,160,288,384,1] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,384,1] 13 (by decide) (choices 1) [16,32] r592 c592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u122
  · exact u123

def b593 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 296 400 48 97 225 353), lower := (rows 7 74 164 296 400 48 64 128 256), losses := [] }

theorem u593 : Upper (D 10) (R 10) [6,72,160,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b593 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r594 : Route 9 := (fun mask => (mask,id))

def c594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u594 : Upper (D 10) (R 10) [6,72,160,288,384,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,384,64] 13 (by decide) (choices 1) [1,16,32] r594 c594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u124
  · exact u125
  · exact u126

def b595 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 74 164 392 49 48 352 480 352), lower := (rows 7 74 164 392 49 48 64 128 256), losses := [] }

theorem u595 : Upper (D 10) (R 10) [6,72,160,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b595 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b596 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 164 392 49 96 368 432 304), lower := (rows 7 74 164 392 49 96 64 128 256), losses := [] }

theorem u596 : Upper (D 10) (R 10) [6,72,160,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b596 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b597 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6),(4,7)], upper := (rows 7 74 164 392 49 288 112 240 368), lower := (rows 7 74 164 392 49 288 64 128 256), losses := [] }

theorem u597 : Upper (D 10) (R 10) [6,72,160,384,33,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b597 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b598 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 164 392 112 33 368 432 304), lower := (rows 7 74 164 392 112 33 64 128 256), losses := [] }

theorem u598 : Upper (D 10) (R 10) [6,72,160,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b598 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b599 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 7 74 164 392 112 48 353 417 289), lower := (rows 7 74 164 392 112 48 64 128 256), losses := [] }

theorem u599 : Upper (D 10) (R 10) [6,72,160,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b599 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u599
end Delivery.IrregularNine14.P10
