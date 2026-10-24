import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0013

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10440 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 13 26 400 36 65 194 322), lower := (rows 97 162 13 26 400 36 65 128 256), losses := [] }

theorem u10440 : Upper (D 7) (R 7) [96,160,9,18,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10440 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10441 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 162 13 26 400 36 66 193 321), lower := (rows 97 162 13 26 400 36 66 128 256), losses := [] }

theorem u10441 : Upper (D 7) (R 7) [96,160,9,18,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10441 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10442 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 28 82 288 65 130 386), lower := (rows 97 162 13 28 82 288 65 128 256), losses := [] }

theorem u10442 : Upper (D 7) (R 7) [96,160,9,20,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10442 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10443 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 28 82 288 66 129 385), lower := (rows 97 162 13 28 82 288 66 128 256), losses := [] }

theorem u10443 : Upper (D 7) (R 7) [96,160,9,20,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10443 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10444 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 28 82 288 192 131 259), lower := (rows 97 162 13 28 82 288 192 128 256), losses := [] }

theorem u10444 : Upper (D 7) (R 7) [96,160,9,20,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10444 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10445 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 93, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 97 162 13 28 208 34 65 386 258), lower := (rows 97 162 13 28 208 34 65 128 256), losses := [] }

theorem u10445 : Upper (D 7) (R 7) [96,160,9,20,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10446 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 28 208 34 66 385 257), lower := (rows 97 162 13 28 208 34 66 128 256), losses := [] }

theorem u10446 : Upper (D 7) (R 7) [96,160,9,20,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10447 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 34, targets := 65 },{ cop := 1, region := 321, targets := 128 }], pairs := [(0,7),(1,0),(1,6)], upper := (rows 97 162 13 28 208 34 320 131 259), lower := (rows 97 162 13 28 208 34 320 128 256), losses := [] }

theorem u10447 : Upper (D 7) (R 7) [96,160,9,20,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10447 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10448 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 93, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 28 208 288 65 130 258), lower := (rows 97 162 13 28 208 288 65 128 256), losses := [] }

theorem u10448 : Upper (D 7) (R 7) [96,160,9,20,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10448 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10449 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 0, region := 130, targets := 64 }], pairs := [(1,6),(4,0),(4,5)], upper := (rows 97 162 13 28 208 288 66 131 259), lower := (rows 97 162 13 28 208 288 66 128 256), losses := [] }

theorem u10449 : Upper (D 7) (R 7) [96,160,9,20,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10449 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10450 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 28 336 34 65 130 386), lower := (rows 97 162 13 28 336 34 65 128 256), losses := [] }

theorem u10450 : Upper (D 7) (R 7) [96,160,9,20,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10451 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 28 336 34 66 129 385), lower := (rows 97 162 13 28 336 34 66 128 256), losses := [] }

theorem u10451 : Upper (D 7) (R 7) [96,160,9,20,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10452 : Route 9 := (fun mask => (mask,id))

def c10452 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10452 : Upper (D 7) (R 7) [96,160,9,20,320,2,128] 13 := by
  apply FastRouting.sound _ _ [96,160,9,20,320,2,128] 13 (by decide) (choices 1) [1,2] r10452 c10452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u791
  · exact u792

def b10453 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 1 },{ cop := 1, region := 65, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(4,0)], upper := (rows 97 162 13 28 400 34 65 194 322), lower := (rows 97 162 13 28 400 34 65 128 256), losses := [] }

theorem u10453 : Upper (D 7) (R 7) [96,160,9,20,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10454 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 28 400 34 66 193 321), lower := (rows 97 162 13 28 400 34 66 128 256), losses := [] }

theorem u10454 : Upper (D 7) (R 7) [96,160,9,20,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10455 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 145 288 66 148 276), lower := (rows 97 162 13 74 145 288 66 128 256), losses := [] }

theorem u10455 : Upper (D 7) (R 7) [96,160,9,66,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10455 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10456 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 13 74 145 288 68 146 274), lower := (rows 97 162 13 74 145 288 68 128 256), losses := [] }

theorem u10456 : Upper (D 7) (R 7) [96,160,9,66,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10456 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10457 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 97 162 13 74 145 288 80 134 262), lower := (rows 97 162 13 74 145 288 80 128 256), losses := [] }

theorem u10457 : Upper (D 7) (R 7) [96,160,9,66,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10457 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10458 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 162 13 74 148 288 65 146 274), lower := (rows 97 162 13 74 148 288 65 128 256), losses := [] }

theorem u10458 : Upper (D 7) (R 7) [96,160,9,66,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10458 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10459 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 148 288 66 145 273), lower := (rows 97 162 13 74 148 288 66 128 256), losses := [] }

theorem u10459 : Upper (D 7) (R 7) [96,160,9,66,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10459 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10460 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 97 162 13 74 148 288 80 131 259), lower := (rows 97 162 13 74 148 288 80 128 256), losses := [] }

theorem u10460 : Upper (D 7) (R 7) [96,160,9,66,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10460 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10461 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 273 48 66 132 388), lower := (rows 97 162 13 74 273 48 66 128 256), losses := [] }

theorem u10461 : Upper (D 7) (R 7) [96,160,9,66,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10461 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10462 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 13 74 273 48 68 130 386), lower := (rows 97 162 13 74 273 48 68 128 256), losses := [] }

theorem u10462 : Upper (D 7) (R 7) [96,160,9,66,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10462 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10463 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 13 74 273 48 192 134 262), lower := (rows 97 162 13 74 273 48 192 128 256), losses := [] }

theorem u10463 : Upper (D 7) (R 7) [96,160,9,66,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10463 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10464 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 162 13 74 274 48 65 132 388), lower := (rows 97 162 13 74 274 48 65 128 256), losses := [] }

theorem u10464 : Upper (D 7) (R 7) [96,160,9,66,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10464 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10465 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 13 74 274 48 68 129 385), lower := (rows 97 162 13 74 274 48 68 128 256), losses := [] }

theorem u10465 : Upper (D 7) (R 7) [96,160,9,66,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10465 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10466 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 13 74 274 48 192 133 261), lower := (rows 97 162 13 74 274 48 192 128 256), losses := [] }

theorem u10466 : Upper (D 7) (R 7) [96,160,9,66,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10466 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10467 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 162 13 74 276 48 65 130 386), lower := (rows 97 162 13 74 276 48 65 128 256), losses := [] }

theorem u10467 : Upper (D 7) (R 7) [96,160,9,66,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10467 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10468 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 74 276 48 66 129 385), lower := (rows 97 162 13 74 276 48 66 128 256), losses := [] }

theorem u10468 : Upper (D 7) (R 7) [96,160,9,66,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10468 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10469 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 13 74 276 48 192 131 259), lower := (rows 97 162 13 74 276 48 192 128 256), losses := [] }

theorem u10469 : Upper (D 7) (R 7) [96,160,9,66,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10469 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10470 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 88 145 34 66 388 260), lower := (rows 97 162 13 88 145 34 66 128 256), losses := [] }

theorem u10470 : Upper (D 7) (R 7) [96,160,9,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10471 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 76, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 97 162 13 88 145 34 68 386 258), lower := (rows 97 162 13 88 145 34 68 128 256), losses := [] }

theorem u10471 : Upper (D 7) (R 7) [96,160,9,80,129,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10471 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10472 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 178, targets := 64 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 145 34 320 134 262), lower := (rows 97 162 13 88 145 34 320 128 256), losses := [] }

theorem u10472 : Upper (D 7) (R 7) [96,160,9,80,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10472 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10473 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 88 273 34 66 132 388), lower := (rows 97 162 13 88 273 34 66 128 256), losses := [] }

theorem u10473 : Upper (D 7) (R 7) [96,160,9,80,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10474 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 76, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 97 162 13 88 273 34 68 130 386), lower := (rows 97 162 13 88 273 34 68 128 256), losses := [] }

theorem u10474 : Upper (D 7) (R 7) [96,160,9,80,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10474 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10475 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 1, region := 65, targets := 2 },{ cop := 2, region := 162, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 273 34 192 134 262), lower := (rows 97 162 13 88 273 34 192 128 256), losses := [] }

theorem u10475 : Upper (D 7) (R 7) [96,160,9,80,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10476 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 162 13 88 276 34 65 130 386), lower := (rows 97 162 13 88 276 34 65 128 256), losses := [] }

theorem u10476 : Upper (D 7) (R 7) [96,160,9,80,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10477 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 88 276 34 66 129 385), lower := (rows 97 162 13 88 276 34 66 128 256), losses := [] }

theorem u10477 : Upper (D 7) (R 7) [96,160,9,80,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10477 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10478 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 1, region := 65, targets := 2 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 276 34 192 131 259), lower := (rows 97 162 13 88 276 34 192 128 256), losses := [] }

theorem u10478 : Upper (D 7) (R 7) [96,160,9,80,260,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10479 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 162 13 88 400 34 65 134 262), lower := (rows 97 162 13 88 400 34 65 128 256), losses := [] }

theorem u10479 : Upper (D 7) (R 7) [96,160,9,80,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10480 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 88 400 34 66 133 261), lower := (rows 97 162 13 88 400 34 66 128 256), losses := [] }

theorem u10480 : Upper (D 7) (R 7) [96,160,9,80,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10481 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 402, targets := 64 },{ cop := 4, region := 34, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 97 162 13 88 400 34 68 131 259), lower := (rows 97 162 13 88 400 34 68 128 256), losses := [] }

theorem u10481 : Upper (D 7) (R 7) [96,160,9,80,384,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10481 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10482 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 140 82 288 65 146 274), lower := (rows 97 162 13 140 82 288 65 128 256), losses := [] }

theorem u10482 : Upper (D 7) (R 7) [96,160,9,132,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10482 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10483 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 429, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 140 82 288 66 145 273), lower := (rows 97 162 13 140 82 288 66 128 256), losses := [] }

theorem u10483 : Upper (D 7) (R 7) [96,160,9,132,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10483 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10484 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 13 140 82 288 80 131 259), lower := (rows 97 162 13 140 82 288 80 128 256), losses := [] }

theorem u10484 : Upper (D 7) (R 7) [96,160,9,132,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10484 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10485 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 77, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 97 162 13 140 274 48 65 194 322), lower := (rows 97 162 13 140 274 48 65 128 256), losses := [] }

theorem u10485 : Upper (D 7) (R 7) [96,160,9,132,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10485 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10486 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 140, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 97 162 13 140 274 48 66 193 321), lower := (rows 97 162 13 140 274 48 66 128 256), losses := [] }

theorem u10486 : Upper (D 7) (R 7) [96,160,9,132,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10486 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10487 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 81, targets := 128 },{ cop := 2, region := 418, targets := 1 }], pairs := [(0,7),(1,0),(4,7)], upper := (rows 97 162 13 152 82 288 65 134 262), lower := (rows 97 162 13 152 82 288 65 128 256), losses := [] }

theorem u10487 : Upper (D 7) (R 7) [96,160,9,144,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10487 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10488 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 97 162 13 152 82 288 66 133 261), lower := (rows 97 162 13 152 82 288 66 128 256), losses := [] }

theorem u10488 : Upper (D 7) (R 7) [96,160,9,144,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10488 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10489 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7),(1,6)], upper := (rows 97 162 13 152 82 288 68 131 259), lower := (rows 97 162 13 152 82 288 68 128 256), losses := [] }

theorem u10489 : Upper (D 7) (R 7) [96,160,9,144,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10489 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10490 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 152 273 34 66 196 324), lower := (rows 97 162 13 152 273 34 66 128 256), losses := [] }

theorem u10490 : Upper (D 7) (R 7) [96,160,9,144,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10491 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 162 13 152 273 34 68 194 322), lower := (rows 97 162 13 152 273 34 68 128 256), losses := [{ target := 0, region := (rows 0 223 4 24 16 255 68 197 325), good := (rows 482 162 494 186 442 34 486 162 256) }] }

theorem u10491 : Upper (D 7) (R 7) [96,160,9,144,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10491 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10492 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 33, targets := 130 }], pairs := [(0,1),(0,7),(2,5),(3,5)], upper := (rows 97 162 13 152 274 33 66 196 324), lower := (rows 97 162 13 152 274 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 37 91 82 0 82 131 259), good := (rows 477 478 397 216 474 397 474 128 256) }] }

theorem u10492 : Upper (D 7) (R 7) [96,160,9,144,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10493 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 152 274 33 68 194 322), lower := (rows 97 162 13 152 274 33 68 128 256), losses := [] }

theorem u10493 : Upper (D 7) (R 7) [96,160,9,144,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10493 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10494 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 1, region := 65, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 152 276 34 65 194 322), lower := (rows 97 162 13 152 276 34 65 128 256), losses := [] }

theorem u10494 : Upper (D 7) (R 7) [96,160,9,144,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10495 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 152 276 34 66 193 321), lower := (rows 97 162 13 152 276 34 66 128 256), losses := [] }

theorem u10495 : Upper (D 7) (R 7) [96,160,9,144,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10496 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 162, targets := 65 },{ cop := 5, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(1,0),(1,6)], upper := (rows 97 162 13 152 336 34 65 134 262), lower := (rows 97 162 13 152 336 34 65 128 256), losses := [] }

theorem u10496 : Upper (D 7) (R 7) [96,160,9,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10497 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 152 336 34 66 133 261), lower := (rows 97 162 13 152 336 34 66 128 256), losses := [] }

theorem u10497 : Upper (D 7) (R 7) [96,160,9,144,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r10498 : Route 9 := (fun mask => (mask,id))

def c10498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10498 : Upper (D 7) (R 7) [96,160,9,144,320,2,4] 13 := by
  apply FastRouting.sound _ _ [96,160,9,144,320,2,4] 13 (by decide) (choices 1) [1,2] r10498 c10498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u793
  · exact u794

def b10499 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 412, targets := 34 }], pairs := [(2,1),(2,5),(3,1),(3,5)], upper := (rows 97 162 13 200 273 34 66 148 276), lower := (rows 97 162 13 200 273 34 66 128 256), losses := [] }

theorem u10499 : Upper (D 7) (R 7) [96,160,9,192,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10499
end Delivery.IrregularNine14.P07
