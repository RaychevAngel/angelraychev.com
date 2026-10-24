import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0097

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19440 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 276 36 67 195 323), lower := (rows 35 67 44 152 276 36 64 128 256), losses := [] }

theorem u19440 : Upper (D 6) (R 6) [34,65,40,144,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19441 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 152 276 96 71 135 263), lower := (rows 35 67 44 152 276 96 64 128 256), losses := [] }

theorem u19441 : Upper (D 6) (R 6) [34,65,40,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19442 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 152 336 33 70 134 262), lower := (rows 35 67 44 152 336 33 64 128 256), losses := [] }

theorem u19442 : Upper (D 6) (R 6) [34,65,40,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19443 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 152 336 34 69 133 261), lower := (rows 35 67 44 152 336 34 64 128 256), losses := [] }

theorem u19443 : Upper (D 6) (R 6) [34,65,40,144,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19444 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 152 336 36 71 135 263), lower := (rows 35 67 44 152 336 36 64 128 256), losses := [] }

theorem u19444 : Upper (D 6) (R 6) [34,65,40,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19445 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 21 34 340 404 276), lower := (rows 35 67 44 200 21 34 64 128 256), losses := [] }

theorem u19445 : Upper (D 6) (R 6) [34,65,40,192,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19446 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 67 44 200 21 36 338 402 274), lower := (rows 35 67 44 200 21 36 64 128 256), losses := [] }

theorem u19446 : Upper (D 6) (R 6) [34,65,40,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19447 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 200 21 48 326 390 262), lower := (rows 35 67 44 200 21 48 64 128 256), losses := [] }

theorem u19447 : Upper (D 6) (R 6) [34,65,40,192,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19447 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19448 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 67 44 200 21 288 86 150 278), lower := (rows 35 67 44 200 21 288 64 128 256), losses := [] }

theorem u19448 : Upper (D 6) (R 6) [34,65,40,192,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19448 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19449 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 22 33 340 404 276), lower := (rows 35 67 44 200 22 33 64 128 256), losses := [] }

theorem u19449 : Upper (D 6) (R 6) [34,65,40,192,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19450 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 200 22 36 337 401 273), lower := (rows 35 67 44 200 22 36 64 128 256), losses := [] }

theorem u19450 : Upper (D 6) (R 6) [34,65,40,192,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19451 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 200 22 48 325 389 261), lower := (rows 35 67 44 200 22 48 64 128 256), losses := [] }

theorem u19451 : Upper (D 6) (R 6) [34,65,40,192,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19451 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19452 : Route 9 := (fun mask => (mask,id))

def c19452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19452 : Upper (D 6) (R 6) [34,65,40,192,6,256] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,6,256] 13 (by decide) (choices 1) [1,4,16] r19452 c19452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5836
  · exact u5837
  · exact u5838

def b19453 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 273 34 84 148 276), lower := (rows 35 67 44 200 273 34 64 128 256), losses := [] }

theorem u19453 : Upper (D 6) (R 6) [34,65,40,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19454 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 200 273 36 86 150 278), lower := (rows 35 67 44 200 273 36 64 128 256), losses := [] }

theorem u19454 : Upper (D 6) (R 6) [34,65,40,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19455 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 200 273 48 70 134 262), lower := (rows 35 67 44 200 273 48 64 128 256), losses := [] }

theorem u19455 : Upper (D 6) (R 6) [34,65,40,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19455 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19456 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 274 33 84 148 276), lower := (rows 35 67 44 200 274 33 64 128 256), losses := [] }

theorem u19456 : Upper (D 6) (R 6) [34,65,40,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19457 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 200 274 36 85 149 277), lower := (rows 35 67 44 200 274 36 64 128 256), losses := [] }

theorem u19457 : Upper (D 6) (R 6) [34,65,40,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19458 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 200 274 48 69 133 261), lower := (rows 35 67 44 200 274 48 64 128 256), losses := [] }

theorem u19458 : Upper (D 6) (R 6) [34,65,40,192,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19458 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19459 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 200 276 33 86 150 278), lower := (rows 35 67 44 200 276 33 64 128 256), losses := [] }

theorem u19459 : Upper (D 6) (R 6) [34,65,40,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19460 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 200 276 34 85 149 277), lower := (rows 35 67 44 200 276 34 64 128 256), losses := [] }

theorem u19460 : Upper (D 6) (R 6) [34,65,40,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19461 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 200 276 36 83 147 275), lower := (rows 35 67 44 200 276 36 64 128 256), losses := [] }

theorem u19461 : Upper (D 6) (R 6) [34,65,40,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19462 : Route 9 := (fun mask => (mask,id))

def c19462 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19462 : Upper (D 6) (R 6) [34,65,40,192,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,40,192,260,16] 13 (by decide) (choices 1) [1,2,4] r19462 c19462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5839
  · exact u5840
  · exact u5841

def b19463 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 392 21 34 84 212 340), lower := (rows 35 67 44 392 21 34 64 128 256), losses := [] }

theorem u19463 : Upper (D 6) (R 6) [34,65,40,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19464 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 458, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 67 44 392 21 36 82 210 338), lower := (rows 35 67 44 392 21 36 64 128 256), losses := [] }

theorem u19464 : Upper (D 6) (R 6) [34,65,40,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19465 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 392 21 48 70 198 326), lower := (rows 35 67 44 392 21 48 64 128 256), losses := [] }

theorem u19465 : Upper (D 6) (R 6) [34,65,40,384,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19465 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19466 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 392 21 96 86 150 278), lower := (rows 35 67 44 392 21 96 64 128 256), losses := [] }

theorem u19466 : Upper (D 6) (R 6) [34,65,40,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19467 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 392 22 33 84 212 340), lower := (rows 35 67 44 392 22 33 64 128 256), losses := [] }

theorem u19467 : Upper (D 6) (R 6) [34,65,40,384,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19468 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 22 36 81 209 337), lower := (rows 35 67 44 392 22 36 64 128 256), losses := [] }

theorem u19468 : Upper (D 6) (R 6) [34,65,40,384,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19469 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 392 22 48 69 197 325), lower := (rows 35 67 44 392 22 48 64 128 256), losses := [] }

theorem u19469 : Upper (D 6) (R 6) [34,65,40,384,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19469 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19470 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 44 392 22 96 85 149 277), lower := (rows 35 67 44 392 22 96 64 128 256), losses := [] }

theorem u19470 : Upper (D 6) (R 6) [34,65,40,384,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19471 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 392 84 33 86 150 278), lower := (rows 35 67 44 392 84 33 64 128 256), losses := [] }

theorem u19471 : Upper (D 6) (R 6) [34,65,40,384,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19472 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 392 84 34 85 149 277), lower := (rows 35 67 44 392 84 34 64 128 256), losses := [] }

theorem u19472 : Upper (D 6) (R 6) [34,65,40,384,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19473 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 44 392 84 36 83 147 275), lower := (rows 35 67 44 392 84 36 64 128 256), losses := [] }

theorem u19473 : Upper (D 6) (R 6) [34,65,40,384,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19474 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 44 392 84 48 71 135 263), lower := (rows 35 67 44 392 84 48 64 128 256), losses := [] }

theorem u19474 : Upper (D 6) (R 6) [34,65,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19474 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19475 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 25 400 34 76 140 268), lower := (rows 35 67 100 25 400 34 64 128 256), losses := [] }

theorem u19475 : Upper (D 6) (R 6) [34,65,96,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19476 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 25 400 36 78 142 270), lower := (rows 35 67 100 25 400 36 64 128 256), losses := [] }

theorem u19476 : Upper (D 6) (R 6) [34,65,96,17,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19477 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 25 400 40 70 134 262), lower := (rows 35 67 100 25 400 40 64 128 256), losses := [] }

theorem u19477 : Upper (D 6) (R 6) [34,65,96,17,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19477 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19478 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 28 145 34 332 396 268), lower := (rows 35 67 100 28 145 34 64 128 256), losses := [] }

theorem u19478 : Upper (D 6) (R 6) [34,65,96,20,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19479 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 28 145 36 330 394 266), lower := (rows 35 67 100 28 145 36 64 128 256), losses := [] }

theorem u19479 : Upper (D 6) (R 6) [34,65,96,20,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19480 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 28 145 40 326 390 262), lower := (rows 35 67 100 28 145 40 64 128 256), losses := [] }

theorem u19480 : Upper (D 6) (R 6) [34,65,96,20,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19480 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19481 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 28 145 288 78 142 270), lower := (rows 35 67 100 28 145 288 64 128 256), losses := [] }

theorem u19481 : Upper (D 6) (R 6) [34,65,96,20,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19481 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19482 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 28 152 33 326 390 262), lower := (rows 35 67 100 28 152 33 64 128 256), losses := [] }

theorem u19482 : Upper (D 6) (R 6) [34,65,96,20,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19482 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19483 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 28 152 34 325 389 261), lower := (rows 35 67 100 28 152 34 64 128 256), losses := [] }

theorem u19483 : Upper (D 6) (R 6) [34,65,96,20,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19484 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(1,2),(1,5),(2,0)], upper := (rows 35 67 100 28 152 36 323 387 259), lower := (rows 35 67 100 28 152 36 64 128 256), losses := [] }

theorem u19484 : Upper (D 6) (R 6) [34,65,96,20,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19485 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 28 152 288 71 135 263), lower := (rows 35 67 100 28 152 288 64 128 256), losses := [] }

theorem u19485 : Upper (D 6) (R 6) [34,65,96,20,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19485 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19486 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 28 400 33 78 142 270), lower := (rows 35 67 100 28 400 33 64 128 256), losses := [] }

theorem u19486 : Upper (D 6) (R 6) [34,65,96,20,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19487 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 28 400 34 77 141 269), lower := (rows 35 67 100 28 400 34 64 128 256), losses := [] }

theorem u19487 : Upper (D 6) (R 6) [34,65,96,20,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19488 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 28 400 36 75 139 267), lower := (rows 35 67 100 28 400 36 64 128 256), losses := [] }

theorem u19488 : Upper (D 6) (R 6) [34,65,96,20,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19488 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19489 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 28 400 40 71 135 263), lower := (rows 35 67 100 28 400 40 64 128 256), losses := [] }

theorem u19489 : Upper (D 6) (R 6) [34,65,96,20,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19489 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19490 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 137 274 36 92 156 284), lower := (rows 35 67 100 137 274 36 64 128 256), losses := [] }

theorem u19490 : Upper (D 6) (R 6) [34,65,96,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19491 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 137 274 40 84 148 276), lower := (rows 35 67 100 137 274 40 64 128 256), losses := [] }

theorem u19491 : Upper (D 6) (R 6) [34,65,96,129,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19491 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19492 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 100 137 274 48 76 140 268), lower := (rows 35 67 100 137 274 48 64 128 256), losses := [] }

theorem u19492 : Upper (D 6) (R 6) [34,65,96,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19492 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19493 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 276 34 92 156 284), lower := (rows 35 67 100 137 276 34 64 128 256), losses := [] }

theorem u19493 : Upper (D 6) (R 6) [34,65,96,129,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19494 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 137 276 36 90 154 282), lower := (rows 35 67 100 137 276 36 64 128 256), losses := [] }

theorem u19494 : Upper (D 6) (R 6) [34,65,96,129,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19495 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 100 137 276 40 86 150 278), lower := (rows 35 67 100 137 276 40 64 128 256), losses := [] }

theorem u19495 : Upper (D 6) (R 6) [34,65,96,129,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19495 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19496 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 137 276 48 78 142 270), lower := (rows 35 67 100 137 276 48 64 128 256), losses := [] }

theorem u19496 : Upper (D 6) (R 6) [34,65,96,129,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19496 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19497 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 137 280 34 84 148 276), lower := (rows 35 67 100 137 280 34 64 128 256), losses := [] }

theorem u19497 : Upper (D 6) (R 6) [34,65,96,129,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19498 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 137 280 36 86 150 278), lower := (rows 35 67 100 137 280 36 64 128 256), losses := [] }

theorem u19498 : Upper (D 6) (R 6) [34,65,96,129,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19499 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 137 280 48 70 134 262), lower := (rows 35 67 100 137 280 48 64 128 256), losses := [] }

theorem u19499 : Upper (D 6) (R 6) [34,65,96,129,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19499 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19499
end Delivery.IrregularNine14.P06
