import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0009

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7440 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 292, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1)], upper := (rows 35 138 261 73 22 36 80 224 352), lower := (rows 35 138 261 73 22 36 80 128 256), losses := [] }

theorem u7440 : Upper (D 6) (R 6) [34,136,257,65,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7440 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7441 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 73 22 36 96 208 336), lower := (rows 35 138 261 73 22 36 96 128 256), losses := [] }

theorem u7441 : Upper (D 6) (R 6) [34,136,257,65,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7442 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 293, targets := 64 },{ cop := 2, region := 72, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 35 138 261 73 82 36 68 176 304), lower := (rows 35 138 261 73 82 36 68 128 256), losses := [] }

theorem u7442 : Upper (D 6) (R 6) [34,136,257,65,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7443 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 138 261 73 82 36 80 164 292), lower := (rows 35 138 261 73 82 36 80 128 256), losses := [] }

theorem u7443 : Upper (D 6) (R 6) [34,136,257,65,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7443 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7444 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 73 82 36 96 148 276), lower := (rows 35 138 261 73 82 36 96 128 256), losses := [] }

theorem u7444 : Upper (D 6) (R 6) [34,136,257,65,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7445 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 36 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(3,5)], upper := (rows 35 138 261 73 84 36 66 176 304), lower := (rows 35 138 261 73 84 36 66 128 256), losses := [] }

theorem u7445 : Upper (D 6) (R 6) [34,136,257,65,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7446 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 73 84 36 80 162 290), lower := (rows 35 138 261 73 84 36 80 128 256), losses := [] }

theorem u7446 : Upper (D 6) (R 6) [34,136,257,65,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7446 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7447 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 261 73 84 36 96 146 274), lower := (rows 35 138 261 73 84 36 96 128 256), losses := [] }

theorem u7447 : Upper (D 6) (R 6) [34,136,257,65,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7448 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 3, region := 308, targets := 2 }], pairs := [(2,1),(3,2),(4,2)], upper := (rows 35 138 261 73 112 36 66 148 276), lower := (rows 35 138 261 73 112 36 66 128 256), losses := [] }

theorem u7448 : Upper (D 6) (R 6) [34,136,257,65,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7449 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 261 73 112 36 68 146 274), lower := (rows 35 138 261 73 112 36 68 128 256), losses := [] }

theorem u7449 : Upper (D 6) (R 6) [34,136,257,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7450 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 138 261 73 112 36 80 134 262), lower := (rows 35 138 261 73 112 36 80 128 256), losses := [] }

theorem u7450 : Upper (D 6) (R 6) [34,136,257,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7450 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7451 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 261 74 84 36 65 176 304), lower := (rows 35 138 261 74 84 36 65 128 256), losses := [] }

theorem u7451 : Upper (D 6) (R 6) [34,136,257,66,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7452 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 74 84 36 80 161 289), lower := (rows 35 138 261 74 84 36 80 128 256), losses := [] }

theorem u7452 : Upper (D 6) (R 6) [34,136,257,66,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7452 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7453 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 35 138 261 74 84 36 96 145 273), lower := (rows 35 138 261 74 84 36 96 128 256), losses := [] }

theorem u7453 : Upper (D 6) (R 6) [34,136,257,66,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7454 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 72, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 35 138 261 74 112 36 65 148 276), lower := (rows 35 138 261 74 112 36 65 128 256), losses := [] }

theorem u7454 : Upper (D 6) (R 6) [34,136,257,66,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7455 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 261 74 112 36 68 145 273), lower := (rows 35 138 261 74 112 36 68 128 256), losses := [] }

theorem u7455 : Upper (D 6) (R 6) [34,136,257,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7456 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 74 112 36 80 133 261), lower := (rows 35 138 261 74 112 36 80 128 256), losses := [] }

theorem u7456 : Upper (D 6) (R 6) [34,136,257,66,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7456 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7457 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 35 138 261 76 81 36 66 176 304), lower := (rows 35 138 261 76 81 36 66 128 256), losses := [] }

theorem u7457 : Upper (D 6) (R 6) [34,136,257,68,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7458 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 261 76 81 36 80 162 290), lower := (rows 35 138 261 76 81 36 80 128 256), losses := [] }

theorem u7458 : Upper (D 6) (R 6) [34,136,257,68,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7458 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7459 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 261 76 81 36 96 146 274), lower := (rows 35 138 261 76 81 36 96 128 256), losses := [] }

theorem u7459 : Upper (D 6) (R 6) [34,136,257,68,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7460 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 260, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 35 138 261 76 81 48 66 164 292), lower := (rows 35 138 261 76 81 48 66 128 256), losses := [] }

theorem u7460 : Upper (D 6) (R 6) [34,136,257,68,65,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7460 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7461 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 179, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 138 261 76 81 48 68 162 290), lower := (rows 35 138 261 76 81 48 68 128 256), losses := [] }

theorem u7461 : Upper (D 6) (R 6) [34,136,257,68,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7461 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7462 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 130, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 138 261 76 81 48 96 134 262), lower := (rows 35 138 261 76 81 48 96 128 256), losses := [] }

theorem u7462 : Upper (D 6) (R 6) [34,136,257,68,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7462 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7463 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 88, targets := 4 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(3,2),(4,2)], upper := (rows 35 138 261 104 81 36 66 148 276), lower := (rows 35 138 261 104 81 36 66 128 256), losses := [] }

theorem u7463 : Upper (D 6) (R 6) [34,136,257,96,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7464 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 147, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 35 138 261 104 81 36 68 146 274), lower := (rows 35 138 261 104 81 36 68 128 256), losses := [] }

theorem u7464 : Upper (D 6) (R 6) [34,136,257,96,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7465 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 138 261 104 81 36 80 134 262), lower := (rows 35 138 261 104 81 36 80 128 256), losses := [] }

theorem u7465 : Upper (D 6) (R 6) [34,136,257,96,65,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7465 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7466 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 3, region := 112, targets := 2 }], pairs := [(0,2),(2,0),(4,1)], upper := (rows 35 138 262 13 52 96 65 208 336), lower := (rows 35 138 262 13 52 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 5 8 81 96 64 224 352), good := (rows 438 138 262 28 436 496 500 128 256) }] }

theorem u7466 : Upper (D 6) (R 6) [34,136,258,5,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7467 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 138 262 13 52 96 80 193 321), lower := (rows 35 138 262 13 52 96 80 128 256), losses := [] }

theorem u7467 : Upper (D 6) (R 6) [34,136,258,5,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7467 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7468 : Route 9 := (fun mask => (mask,id))

def c7468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7468 : Upper (D 6) (R 6) [34,136,258,5,65,64,4] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,65,64,4] 13 (by decide) (choices 1) [16,32] r7468 c7468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u575
  · exact u576

def b7469 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 13 81 96 80 164 292), lower := (rows 35 138 262 13 81 96 80 128 256), losses := [] }

theorem u7469 : Upper (D 6) (R 6) [34,136,258,5,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7469 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7470 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 262 13 81 96 96 148 276), lower := (rows 35 138 262 13 81 96 96 128 256), losses := [] }

theorem u7470 : Upper (D 6) (R 6) [34,136,258,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7471 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 97, targets := 4 },{ cop := 3, region := 80, targets := 2 },{ cop := 3, region := 80, targets := 32 }], pairs := [(0,2),(4,1),(4,5)], upper := (rows 35 138 262 13 84 96 65 176 304), lower := (rows 35 138 262 13 84 96 65 128 256), losses := [] }

theorem u7471 : Upper (D 6) (R 6) [34,136,258,5,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7472 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 13 84 96 80 161 289), lower := (rows 35 138 262 13 84 96 80 128 256), losses := [] }

theorem u7472 : Upper (D 6) (R 6) [34,136,258,5,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7472 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7473 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 35 138 262 13 84 96 96 145 273), lower := (rows 35 138 262 13 84 96 96 128 256), losses := [] }

theorem u7473 : Upper (D 6) (R 6) [34,136,258,5,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7474 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(2,5)], upper := (rows 35 138 262 25 52 96 65 196 324), lower := (rows 35 138 262 25 52 96 65 128 256), losses := [] }

theorem u7474 : Upper (D 6) (R 6) [34,136,258,17,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7475 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(4,0),(4,1)], upper := (rows 35 138 262 25 52 96 68 193 321), lower := (rows 35 138 262 25 52 96 68 128 256), losses := [] }

theorem u7475 : Upper (D 6) (R 6) [34,136,258,17,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7476 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 260, targets := 1 },{ cop := 0, region := 260, targets := 64 },{ cop := 1, region := 97, targets := 4 }], pairs := [(0,2),(2,0),(2,6)], upper := (rows 35 138 262 25 84 96 65 164 292), lower := (rows 35 138 262 25 84 96 65 128 256), losses := [] }

theorem u7476 : Upper (D 6) (R 6) [34,136,258,17,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7477 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 171, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 262 25 84 96 68 161 289), lower := (rows 35 138 262 25 84 96 68 128 256), losses := [] }

theorem u7477 : Upper (D 6) (R 6) [34,136,258,17,68,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7478 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 390, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 262 25 84 96 96 133 261), lower := (rows 35 138 262 25 84 96 96 128 256), losses := [] }

theorem u7478 : Upper (D 6) (R 6) [34,136,258,17,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7479 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 138 262 44 81 96 65 148 276), lower := (rows 35 138 262 44 81 96 65 128 256), losses := [] }

theorem u7479 : Upper (D 6) (R 6) [34,136,258,36,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7480 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 104, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 35 138 262 44 81 96 68 145 273), lower := (rows 35 138 262 44 81 96 68 128 256), losses := [] }

theorem u7480 : Upper (D 6) (R 6) [34,136,258,36,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7481 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 44 81 96 80 133 261), lower := (rows 35 138 262 44 81 96 80 128 256), losses := [] }

theorem u7481 : Upper (D 6) (R 6) [34,136,258,36,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7481 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7482 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 262 73 84 36 65 176 304), lower := (rows 35 138 262 73 84 36 65 128 256), losses := [] }

theorem u7482 : Upper (D 6) (R 6) [34,136,258,65,68,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7483 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 138 262 73 84 36 80 161 289), lower := (rows 35 138 262 73 84 36 80 128 256), losses := [] }

theorem u7483 : Upper (D 6) (R 6) [34,136,258,65,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7483 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7484 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 262 73 84 36 96 145 273), lower := (rows 35 138 262 73 84 36 96 128 256), losses := [] }

theorem u7484 : Upper (D 6) (R 6) [34,136,258,65,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7485 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 138 262 73 112 36 65 148 276), lower := (rows 35 138 262 73 112 36 65 128 256), losses := [] }

theorem u7485 : Upper (D 6) (R 6) [34,136,258,65,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7486 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 138 262 73 112 36 68 145 273), lower := (rows 35 138 262 73 112 36 68 128 256), losses := [] }

theorem u7486 : Upper (D 6) (R 6) [34,136,258,65,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7487 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 88, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 138 262 73 112 36 80 133 261), lower := (rows 35 138 262 73 112 36 80 128 256), losses := [] }

theorem u7487 : Upper (D 6) (R 6) [34,136,258,65,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7487 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7488 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 227, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 138 276 13 22 96 65 224 352), lower := (rows 35 138 276 13 22 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 8 17 96 64 224 352), good := (rows 438 138 276 28 22 484 500 128 256) }] }

theorem u7488 : Upper (D 6) (R 6) [34,136,272,5,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7489 : Route 9 := (fun mask => (mask,id))

def c7489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7489 : Upper (D 6) (R 6) [34,136,272,5,6,64,32] 13 := by
  apply FastRouting.sound _ _ [34,136,272,5,6,64,32] 13 (by decide) (choices 1) [1,64] r7489 c7489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u577
  · exact u578

def b7490 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 2 }], pairs := [(0,2),(2,1),(4,2)], upper := (rows 35 138 276 13 81 96 66 164 292), lower := (rows 35 138 276 13 81 96 66 128 256), losses := [] }

theorem u7490 : Upper (D 6) (R 6) [34,136,272,5,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7491 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 226, targets := 1 },{ cop := 3, region := 80, targets := 2 },{ cop := 3, region := 80, targets := 32 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 35 138 276 13 81 96 68 162 290), lower := (rows 35 138 276 13 81 96 68 128 256), losses := [] }

theorem u7491 : Upper (D 6) (R 6) [34,136,272,5,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7492 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 276 13 81 96 96 134 262), lower := (rows 35 138 276 13 81 96 96 128 256), losses := [] }

theorem u7492 : Upper (D 6) (R 6) [34,136,272,5,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7493 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 4, region := 292, targets := 1 }], pairs := [(0,2),(2,0),(4,2)], upper := (rows 35 138 276 13 82 96 65 164 292), lower := (rows 35 138 276 13 82 96 65 128 256), losses := [] }

theorem u7493 : Upper (D 6) (R 6) [34,136,272,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7494 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 33, targets := 4 }], pairs := [(0,2),(1,2),(4,0)], upper := (rows 35 138 276 13 82 96 68 161 289), lower := (rows 35 138 276 13 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 126 76 128 256), good := (rows 50 250 372 108 114 96 100 128 256) },{ target := 2, region := (rows 17 10 0 8 16 112 64 149 277), good := (rows 419 138 433 395 499 96 480 128 256) }] }

theorem u7494 : Upper (D 6) (R 6) [34,136,272,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7495 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 113, targets := 4 },{ cop := 3, region := 130, targets := 32 }], pairs := [(0,2),(1,5),(4,2)], upper := (rows 35 138 276 13 82 96 96 133 261), lower := (rows 35 138 276 13 82 96 96 128 256), losses := [] }

theorem u7495 : Upper (D 6) (R 6) [34,136,272,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7495 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7496 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 138 276 14 81 96 65 164 292), lower := (rows 35 138 276 14 81 96 65 128 256), losses := [] }

theorem u7496 : Upper (D 6) (R 6) [34,136,272,6,65,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7497 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 340, targets := 2 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 35 138 276 14 81 96 68 161 289), lower := (rows 35 138 276 14 81 96 68 128 256), losses := [{ target := 6, region := (rows 1 18 20 28 16 32 0 129 257), good := (rows 419 138 286 14 415 32 12 128 256) }] }

theorem u7497 : Upper (D 6) (R 6) [34,136,272,6,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7498 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 398, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 138 276 14 81 96 96 133 261), lower := (rows 35 138 276 14 81 96 96 128 256), losses := [] }

theorem u7498 : Upper (D 6) (R 6) [34,136,272,6,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7499 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 88, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 138 276 73 82 36 65 164 292), lower := (rows 35 138 276 73 82 36 65 128 256), losses := [] }

theorem u7499 : Upper (D 6) (R 6) [34,136,272,65,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7499
end Delivery.IrregularNine14.P06
