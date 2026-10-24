import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0120

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b23460 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 268 73 82 36 113 177 305), lower := (rows 35 134 268 73 82 36 64 128 256), losses := [] }

theorem u23460 : Upper (D 6) (R 6) [34,132,264,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23461 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 268 73 82 48 101 165 293), lower := (rows 35 134 268 73 82 48 64 128 256), losses := [] }

theorem u23461 : Upper (D 6) (R 6) [34,132,264,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23461 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23462 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 268 73 84 33 114 178 306), lower := (rows 35 134 268 73 84 33 64 128 256), losses := [] }

theorem u23462 : Upper (D 6) (R 6) [34,132,264,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23463 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 73 84 34 113 177 305), lower := (rows 35 134 268 73 84 34 64 128 256), losses := [] }

theorem u23463 : Upper (D 6) (R 6) [34,132,264,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23464 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 73 84 48 99 163 291), lower := (rows 35 134 268 73 84 48 64 128 256), losses := [] }

theorem u23464 : Upper (D 6) (R 6) [34,132,264,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23464 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23465 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 48, targets := 2 }], pairs := [(0,2),(0,6),(4,1)], upper := (rows 35 134 268 73 112 33 86 150 278), lower := (rows 35 134 268 73 112 33 64 128 256), losses := [] }

theorem u23465 : Upper (D 6) (R 6) [34,132,264,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23466 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 73 112 34 85 149 277), lower := (rows 35 134 268 73 112 34 64 128 256), losses := [] }

theorem u23466 : Upper (D 6) (R 6) [34,132,264,65,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23467 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 134 268 73 112 36 83 147 275), lower := (rows 35 134 268 73 112 36 64 128 256), losses := [] }

theorem u23467 : Upper (D 6) (R 6) [34,132,264,65,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23468 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 73 112 48 71 135 263), lower := (rows 35 134 268 73 112 48 64 128 256), losses := [] }

theorem u23468 : Upper (D 6) (R 6) [34,132,264,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23468 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23469 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 268 74 21 33 112 240 368), lower := (rows 35 134 268 74 21 33 64 128 256), losses := [] }

theorem u23469 : Upper (D 6) (R 6) [34,132,264,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23470 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 268 74 21 48 97 225 353), lower := (rows 35 134 268 74 21 48 64 128 256), losses := [] }

theorem u23470 : Upper (D 6) (R 6) [34,132,264,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23470 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23471 : Route 9 := (fun mask => (mask,id))

def c23471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23471 : Upper (D 6) (R 6) [34,132,264,66,5,64] 13 := by
  apply FastRouting.sound _ _ [34,132,264,66,5,64] 13 (by decide) (choices 1) [1,16,32] r23471 c23471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7227
  · exact u7228
  · exact u7229

def b23472 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 268 74 52 33 81 209 337), lower := (rows 35 134 268 74 52 33 64 128 256), losses := [] }

theorem u23472 : Upper (D 6) (R 6) [34,132,264,66,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23473 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 74 52 48 65 193 321), lower := (rows 35 134 268 74 52 48 64 128 256), losses := [] }

theorem u23473 : Upper (D 6) (R 6) [34,132,264,66,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23473 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23474 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 131, targets := 64 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 268 74 52 96 81 145 273), lower := (rows 35 134 268 74 52 96 64 128 256), losses := [] }

theorem u23474 : Upper (D 6) (R 6) [34,132,264,66,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23475 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 74 81 33 116 180 308), lower := (rows 35 134 268 74 81 33 64 128 256), losses := [] }

theorem u23475 : Upper (D 6) (R 6) [34,132,264,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23476 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 268 74 81 36 113 177 305), lower := (rows 35 134 268 74 81 36 64 128 256), losses := [] }

theorem u23476 : Upper (D 6) (R 6) [34,132,264,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23477 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 268 74 81 48 101 165 293), lower := (rows 35 134 268 74 81 48 64 128 256), losses := [] }

theorem u23477 : Upper (D 6) (R 6) [34,132,264,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23477 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23478 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 268 74 84 33 113 177 305), lower := (rows 35 134 268 74 84 33 64 128 256), losses := [] }

theorem u23478 : Upper (D 6) (R 6) [34,132,264,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23479 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 74 84 48 97 161 289), lower := (rows 35 134 268 74 84 48 64 128 256), losses := [] }

theorem u23479 : Upper (D 6) (R 6) [34,132,264,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23479 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23480 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 74 112 33 85 149 277), lower := (rows 35 134 268 74 112 33 64 128 256), losses := [] }

theorem u23480 : Upper (D 6) (R 6) [34,132,264,66,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23481 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 2 }], pairs := [(3,2),(4,1),(4,2)], upper := (rows 35 134 268 74 112 36 81 145 273), lower := (rows 35 134 268 74 112 36 64 128 256), losses := [] }

theorem u23481 : Upper (D 6) (R 6) [34,132,264,66,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23481 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23482 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 74 112 48 69 133 261), lower := (rows 35 134 268 74 112 48 64 128 256), losses := [] }

theorem u23482 : Upper (D 6) (R 6) [34,132,264,66,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23482 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23483 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 76 81 33 114 178 306), lower := (rows 35 134 268 76 81 33 64 128 256), losses := [] }

theorem u23483 : Upper (D 6) (R 6) [34,132,264,68,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23484 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 76 81 34 113 177 305), lower := (rows 35 134 268 76 81 34 64 128 256), losses := [] }

theorem u23484 : Upper (D 6) (R 6) [34,132,264,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23485 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 113, targets := 4 }], pairs := [(0,2),(4,2)], upper := (rows 35 134 268 76 81 48 99 163 291), lower := (rows 35 134 268 76 81 48 64 128 256), losses := [] }

theorem u23485 : Upper (D 6) (R 6) [34,132,264,68,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23485 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23486 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 268 76 112 33 83 147 275), lower := (rows 35 134 268 76 112 33 64 128 256), losses := [] }

theorem u23486 : Upper (D 6) (R 6) [34,132,264,68,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23487 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 76 112 34 81 145 273), lower := (rows 35 134 268 76 112 34 64 128 256), losses := [] }

theorem u23487 : Upper (D 6) (R 6) [34,132,264,68,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23488 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 134 268 76 112 48 67 131 259), lower := (rows 35 134 268 76 112 48 64 128 256), losses := [] }

theorem u23488 : Upper (D 6) (R 6) [34,132,264,68,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23488 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23489 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 268 88 21 33 98 226 354), lower := (rows 35 134 268 88 21 33 64 128 256), losses := [] }

theorem u23489 : Upper (D 6) (R 6) [34,132,264,80,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23490 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 88 21 34 97 225 353), lower := (rows 35 134 268 88 21 34 64 128 256), losses := [] }

theorem u23490 : Upper (D 6) (R 6) [34,132,264,80,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23491 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,6),(3,2)], upper := (rows 35 134 268 88 21 96 99 163 291), lower := (rows 35 134 268 88 21 96 64 128 256), losses := [{ target := 2, region := (rows 3 2 0 24 16 123 67 131 259), good := (rows 483 483 296 120 505 96 96 128 256) },{ target := 6, region := (rows 1 18 4 8 16 32 0 129 257), good := (rows 419 134 268 26 407 32 0 128 256) }] }

theorem u23491 : Upper (D 6) (R 6) [34,132,264,80,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23492 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(4,6)], upper := (rows 35 134 268 88 52 33 67 195 323), lower := (rows 35 134 268 88 52 33 64 128 256), losses := [] }

theorem u23492 : Upper (D 6) (R 6) [34,132,264,80,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23493 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 88 52 34 65 193 321), lower := (rows 35 134 268 88 52 34 64 128 256), losses := [] }

theorem u23493 : Upper (D 6) (R 6) [34,132,264,80,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23494 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 131, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 268 88 52 96 67 131 259), lower := (rows 35 134 268 88 52 96 64 128 256), losses := [] }

theorem u23494 : Upper (D 6) (R 6) [34,132,264,80,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23495 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 134 268 104 21 33 82 210 338), lower := (rows 35 134 268 104 21 33 64 128 256), losses := [] }

theorem u23495 : Upper (D 6) (R 6) [34,132,264,96,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23496 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 104 21 34 81 209 337), lower := (rows 35 134 268 104 21 34 64 128 256), losses := [] }

theorem u23496 : Upper (D 6) (R 6) [34,132,264,96,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23497 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 134 268 104 21 48 67 195 323), lower := (rows 35 134 268 104 21 48 64 128 256), losses := [] }

theorem u23497 : Upper (D 6) (R 6) [34,132,264,96,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23497 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23498 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 134 268 104 21 96 83 147 275), lower := (rows 35 134 268 104 21 96 64 128 256), losses := [] }

theorem u23498 : Upper (D 6) (R 6) [34,132,264,96,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23499 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 40, targets := 2 }], pairs := [(0,2),(0,6),(3,1)], upper := (rows 35 134 268 104 81 33 86 150 278), lower := (rows 35 134 268 104 81 33 64 128 256), losses := [] }

theorem u23499 : Upper (D 6) (R 6) [34,132,264,96,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23500 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 104 81 34 85 149 277), lower := (rows 35 134 268 104 81 34 64 128 256), losses := [] }

theorem u23500 : Upper (D 6) (R 6) [34,132,264,96,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23501 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 268 104 81 36 83 147 275), lower := (rows 35 134 268 104 81 36 64 128 256), losses := [] }

theorem u23501 : Upper (D 6) (R 6) [34,132,264,96,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23502 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 104 81 48 71 135 263), lower := (rows 35 134 268 104 81 48 64 128 256), losses := [] }

theorem u23502 : Upper (D 6) (R 6) [34,132,264,96,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23502 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23503 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 41, targets := 4 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 134 268 104 82 33 85 149 277), lower := (rows 35 134 268 104 82 33 64 128 256), losses := [] }

theorem u23503 : Upper (D 6) (R 6) [34,132,264,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23504 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(3,2),(4,2),(4,5)], upper := (rows 35 134 268 104 82 36 81 145 273), lower := (rows 35 134 268 104 82 36 64 128 256), losses := [] }

theorem u23504 : Upper (D 6) (R 6) [34,132,264,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23505 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 104 82 48 69 133 261), lower := (rows 35 134 268 104 82 48 64 128 256), losses := [] }

theorem u23505 : Upper (D 6) (R 6) [34,132,264,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23505 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23506 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 4, region := 163, targets := 64 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 268 104 84 33 83 147 275), lower := (rows 35 134 268 104 84 33 64 128 256), losses := [] }

theorem u23506 : Upper (D 6) (R 6) [34,132,264,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23507 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 268 104 84 34 81 145 273), lower := (rows 35 134 268 104 84 34 64 128 256), losses := [] }

theorem u23507 : Upper (D 6) (R 6) [34,132,264,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23508 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 268 104 84 48 67 131 259), lower := (rows 35 134 268 104 84 48 64 128 256), losses := [] }

theorem u23508 : Upper (D 6) (R 6) [34,132,264,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23508 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23509 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 13 81 34 88 216 344), lower := (rows 35 134 292 13 81 34 64 128 256), losses := [] }

theorem u23509 : Upper (D 6) (R 6) [34,132,288,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23510 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 292 13 81 40 82 210 338), lower := (rows 35 134 292 13 81 40 64 128 256), losses := [] }

theorem u23510 : Upper (D 6) (R 6) [34,132,288,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23510 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23511 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 292 13 81 48 74 202 330), lower := (rows 35 134 292 13 81 48 64 128 256), losses := [] }

theorem u23511 : Upper (D 6) (R 6) [34,132,288,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23511 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r23512 : Route 9 := (fun mask => (mask,id))

def c23512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u23512 : Upper (D 6) (R 6) [34,132,288,5,65,64] 13 := by
  apply FastRouting.sound _ _ [34,132,288,5,65,64] 13 (by decide) (choices 1) [2,8,16] r23512 c23512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7230
  · exact u7231
  · exact u7232

def b23513 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 292 13 82 33 88 216 344), lower := (rows 35 134 292 13 82 33 64 128 256), losses := [] }

theorem u23513 : Upper (D 6) (R 6) [34,132,288,5,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23513 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23514 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 36 }], pairs := [(4,2),(4,5)], upper := (rows 35 134 292 13 82 40 81 209 337), lower := (rows 35 134 292 13 82 40 64 128 256), losses := [] }

theorem u23514 : Upper (D 6) (R 6) [34,132,288,5,66,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23514 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23515 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 292 13 82 48 73 201 329), lower := (rows 35 134 292 13 82 48 64 128 256), losses := [] }

theorem u23515 : Upper (D 6) (R 6) [34,132,288,5,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23515 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23516 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 35 134 292 13 82 96 89 153 281), lower := (rows 35 134 292 13 82 96 64 128 256), losses := [] }

theorem u23516 : Upper (D 6) (R 6) [34,132,288,5,66,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23517 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 292 13 88 33 82 210 338), lower := (rows 35 134 292 13 88 33 64 128 256), losses := [] }

theorem u23517 : Upper (D 6) (R 6) [34,132,288,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23517 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23518 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 292 13 88 34 81 209 337), lower := (rows 35 134 292 13 88 34 64 128 256), losses := [] }

theorem u23518 : Upper (D 6) (R 6) [34,132,288,5,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23518 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b23519 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,5)], upper := (rows 35 134 292 13 88 48 67 195 323), lower := (rows 35 134 292 13 88 48 64 128 256), losses := [] }

theorem u23519 : Upper (D 6) (R 6) [34,132,288,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b23519 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u23519
end Delivery.IrregularNine14.P06
