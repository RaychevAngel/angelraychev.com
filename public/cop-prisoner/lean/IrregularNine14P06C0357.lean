import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0105

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21420 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 164 28 274 33 69 197 325), lower := (rows 35 74 164 28 274 33 64 128 256), losses := [] }

theorem u21420 : Upper (D 6) (R 6) [34,72,160,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21421 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 28 274 36 65 193 321), lower := (rows 35 74 164 28 274 36 64 128 256), losses := [] }

theorem u21421 : Upper (D 6) (R 6) [34,72,160,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21422 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 28 274 96 69 133 261), lower := (rows 35 74 164 28 274 96 64 128 256), losses := [] }

theorem u21422 : Upper (D 6) (R 6) [34,72,160,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21423 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 164 28 336 33 71 135 263), lower := (rows 35 74 164 28 336 33 64 128 256), losses := [] }

theorem u21423 : Upper (D 6) (R 6) [34,72,160,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21424 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 28 336 34 69 133 261), lower := (rows 35 74 164 28 336 34 64 128 256), losses := [] }

theorem u21424 : Upper (D 6) (R 6) [34,72,160,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21425 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 28 336 36 67 131 259), lower := (rows 35 74 164 28 336 36 64 128 256), losses := [] }

theorem u21425 : Upper (D 6) (R 6) [34,72,160,20,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21426 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 265 21 34 84 212 340), lower := (rows 35 74 164 265 21 34 64 128 256), losses := [] }

theorem u21426 : Upper (D 6) (R 6) [34,72,160,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21427 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 164 265 21 36 82 210 338), lower := (rows 35 74 164 265 21 36 64 128 256), losses := [] }

theorem u21427 : Upper (D 6) (R 6) [34,72,160,257,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21428 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 164 265 21 48 70 198 326), lower := (rows 35 74 164 265 21 48 64 128 256), losses := [] }

theorem u21428 : Upper (D 6) (R 6) [34,72,160,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21428 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21429 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 265 21 96 86 150 278), lower := (rows 35 74 164 265 21 96 64 128 256), losses := [] }

theorem u21429 : Upper (D 6) (R 6) [34,72,160,257,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21430 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 164 265 22 33 84 212 340), lower := (rows 35 74 164 265 22 33 64 128 256), losses := [] }

theorem u21430 : Upper (D 6) (R 6) [34,72,160,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21431 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 265 22 36 81 209 337), lower := (rows 35 74 164 265 22 36 64 128 256), losses := [] }

theorem u21431 : Upper (D 6) (R 6) [34,72,160,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21432 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 164 265 22 48 69 197 325), lower := (rows 35 74 164 265 22 48 64 128 256), losses := [] }

theorem u21432 : Upper (D 6) (R 6) [34,72,160,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21432 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21433 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 265 22 96 85 149 277), lower := (rows 35 74 164 265 22 96 64 128 256), losses := [] }

theorem u21433 : Upper (D 6) (R 6) [34,72,160,257,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21434 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 265 81 34 84 148 276), lower := (rows 35 74 164 265 81 34 64 128 256), losses := [] }

theorem u21434 : Upper (D 6) (R 6) [34,72,160,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21435 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 265 81 36 86 150 278), lower := (rows 35 74 164 265 81 36 64 128 256), losses := [] }

theorem u21435 : Upper (D 6) (R 6) [34,72,160,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21436 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 265 81 48 70 134 262), lower := (rows 35 74 164 265 81 48 64 128 256), losses := [] }

theorem u21436 : Upper (D 6) (R 6) [34,72,160,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21436 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21437 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 164 265 84 33 86 150 278), lower := (rows 35 74 164 265 84 33 64 128 256), losses := [] }

theorem u21437 : Upper (D 6) (R 6) [34,72,160,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21438 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 265 84 34 85 149 277), lower := (rows 35 74 164 265 84 34 64 128 256), losses := [] }

theorem u21438 : Upper (D 6) (R 6) [34,72,160,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21439 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 265 84 36 83 147 275), lower := (rows 35 74 164 265 84 36 64 128 256), losses := [] }

theorem u21439 : Upper (D 6) (R 6) [34,72,160,257,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21440 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 265 84 48 71 135 263), lower := (rows 35 74 164 265 84 48 64 128 256), losses := [] }

theorem u21440 : Upper (D 6) (R 6) [34,72,160,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21440 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21441 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 164 266 84 33 85 149 277), lower := (rows 35 74 164 266 84 33 64 128 256), losses := [] }

theorem u21441 : Upper (D 6) (R 6) [34,72,160,258,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21442 : PairBound 9 := { available := 17, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 266 84 36 81 145 273), lower := (rows 35 74 164 266 84 36 64 128 256), losses := [] }

theorem u21442 : Upper (D 6) (R 6) [34,72,160,258,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21443 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 164 266 84 48 69 133 261), lower := (rows 35 74 164 266 84 48 64 128 256), losses := [] }

theorem u21443 : Upper (D 6) (R 6) [34,72,160,258,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21443 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21444 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 164 268 21 33 82 210 338), lower := (rows 35 74 164 268 21 33 64 128 256), losses := [] }

theorem u21444 : Upper (D 6) (R 6) [34,72,160,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21445 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 268 21 34 81 209 337), lower := (rows 35 74 164 268 21 34 64 128 256), losses := [] }

theorem u21445 : Upper (D 6) (R 6) [34,72,160,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21446 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 74 164 268 21 48 67 195 323), lower := (rows 35 74 164 268 21 48 64 128 256), losses := [] }

theorem u21446 : Upper (D 6) (R 6) [34,72,160,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21446 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21447 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 268 21 96 83 147 275), lower := (rows 35 74 164 268 21 96 64 128 256), losses := [] }

theorem u21447 : Upper (D 6) (R 6) [34,72,160,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21448 : Route 9 := (fun mask => (mask,id))

def c21448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21448 : Upper (D 6) (R 6) [34,72,160,260,6,1] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,6,1] 13 (by decide) (choices 1) [1,16] r21448 c21448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6306
  · exact u6307

def b21449 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 164 268 22 48 65 193 321), lower := (rows 35 74 164 268 22 48 64 128 256), losses := [] }

theorem u21449 : Upper (D 6) (R 6) [34,72,160,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21449 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21450 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 268 22 96 81 145 273), lower := (rows 35 74 164 268 22 96 64 128 256), losses := [] }

theorem u21450 : Upper (D 6) (R 6) [34,72,160,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21451 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 164 268 81 33 86 150 278), lower := (rows 35 74 164 268 81 33 64 128 256), losses := [] }

theorem u21451 : Upper (D 6) (R 6) [34,72,160,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21452 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 268 81 34 85 149 277), lower := (rows 35 74 164 268 81 34 64 128 256), losses := [] }

theorem u21452 : Upper (D 6) (R 6) [34,72,160,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21453 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 268 81 36 83 147 275), lower := (rows 35 74 164 268 81 36 64 128 256), losses := [] }

theorem u21453 : Upper (D 6) (R 6) [34,72,160,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21454 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 268 81 48 71 135 263), lower := (rows 35 74 164 268 81 48 64 128 256), losses := [] }

theorem u21454 : Upper (D 6) (R 6) [34,72,160,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21454 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21455 : Route 9 := (fun mask => (mask,id))

def c21455 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21455 : Upper (D 6) (R 6) [34,72,160,260,68,1] 13 := by
  apply FastRouting.sound _ _ [34,72,160,260,68,1] 13 (by decide) (choices 1) [1,2,16] r21455 c21455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6308
  · exact u6309
  · exact u6310

def b21456 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 268 84 34 81 145 273), lower := (rows 35 74 164 268 84 34 64 128 256), losses := [] }

theorem u21456 : Upper (D 6) (R 6) [34,72,160,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21457 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 164 268 84 48 67 131 259), lower := (rows 35 74 164 268 84 48 64 128 256), losses := [] }

theorem u21457 : Upper (D 6) (R 6) [34,72,160,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21457 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21458 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 330, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 164 280 21 33 70 198 326), lower := (rows 35 74 164 280 21 33 64 128 256), losses := [] }

theorem u21458 : Upper (D 6) (R 6) [34,72,160,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21459 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 280 21 34 69 197 325), lower := (rows 35 74 164 280 21 34 64 128 256), losses := [] }

theorem u21459 : Upper (D 6) (R 6) [34,72,160,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21460 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 164 280 21 36 67 195 323), lower := (rows 35 74 164 280 21 36 64 128 256), losses := [] }

theorem u21460 : Upper (D 6) (R 6) [34,72,160,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21461 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 280 21 96 71 135 263), lower := (rows 35 74 164 280 21 96 64 128 256), losses := [] }

theorem u21461 : Upper (D 6) (R 6) [34,72,160,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21462 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 74 164 280 22 33 69 197 325), lower := (rows 35 74 164 280 22 33 64 128 256), losses := [] }

theorem u21462 : Upper (D 6) (R 6) [34,72,160,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21463 : PairBound 9 := { available := 65, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 280 22 36 65 193 321), lower := (rows 35 74 164 280 22 36 64 128 256), losses := [] }

theorem u21463 : Upper (D 6) (R 6) [34,72,160,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21464 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 164 280 22 96 69 133 261), lower := (rows 35 74 164 280 22 96 64 128 256), losses := [] }

theorem u21464 : Upper (D 6) (R 6) [34,72,160,272,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21465 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 74 164 280 84 33 71 135 263), lower := (rows 35 74 164 280 84 33 64 128 256), losses := [] }

theorem u21465 : Upper (D 6) (R 6) [34,72,160,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21466 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 164 280 84 34 69 133 261), lower := (rows 35 74 164 280 84 34 64 128 256), losses := [] }

theorem u21466 : Upper (D 6) (R 6) [34,72,160,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21467 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 74 164 280 84 36 67 131 259), lower := (rows 35 74 164 280 84 36 64 128 256), losses := [] }

theorem u21467 : Upper (D 6) (R 6) [34,72,160,272,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21468 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 13 52 33 338 402 274), lower := (rows 35 74 196 13 52 33 64 128 256), losses := [] }

theorem u21468 : Upper (D 6) (R 6) [34,72,192,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21469 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 13 52 34 337 401 273), lower := (rows 35 74 196 13 52 34 64 128 256), losses := [] }

theorem u21469 : Upper (D 6) (R 6) [34,72,192,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21470 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 196 13 52 48 323 387 259), lower := (rows 35 74 196 13 52 48 64 128 256), losses := [] }

theorem u21470 : Upper (D 6) (R 6) [34,72,192,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21470 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21471 : PairBound 9 := { available := 19, camps := [], pairs := [(0,6),(4,6)], upper := (rows 35 74 196 13 52 288 83 147 275), lower := (rows 35 74 196 13 52 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 24 291 0 130 258), good := (rows 419 443 132 61 52 288 0 128 288) }] }

theorem u21471 : Upper (D 6) (R 6) [34,72,192,5,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21471 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21472 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 13 273 34 116 180 308), lower := (rows 35 74 196 13 273 34 64 128 256), losses := [] }

theorem u21472 : Upper (D 6) (R 6) [34,72,192,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21473 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 35 74 196 13 273 36 114 178 306), lower := (rows 35 74 196 13 273 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 192 475 465 32 64 128 256) }] }

theorem u21473 : Upper (D 6) (R 6) [34,72,192,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21474 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 196, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 35 74 196 13 273 48 102 166 294), lower := (rows 35 74 196 13 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 29 8 16 48 65 129 257), good := (rows 486 78 196 462 500 52 64 128 256) }] }

theorem u21474 : Upper (D 6) (R 6) [34,72,192,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21474 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21475 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 13 274 33 116 180 308), lower := (rows 35 74 196 13 274 33 64 128 256), losses := [] }

theorem u21475 : Upper (D 6) (R 6) [34,72,192,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21476 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 272, targets := 4 },{ cop := 0, region := 272, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 35 74 196 13 274 36 113 177 305), lower := (rows 35 74 196 13 274 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 192 475 274 32 64 128 256) }] }

theorem u21476 : Upper (D 6) (R 6) [34,72,192,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21477 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 196 13 274 48 101 165 293), lower := (rows 35 74 196 13 274 48 64 128 256), losses := [] }

theorem u21477 : Upper (D 6) (R 6) [34,72,192,5,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21477 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21478 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 196 13 276 33 114 178 306), lower := (rows 35 74 196 13 276 33 64 128 256), losses := [] }

theorem u21478 : Upper (D 6) (R 6) [34,72,192,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21479 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 13 276 34 113 177 305), lower := (rows 35 74 196 13 276 34 64 128 256), losses := [] }

theorem u21479 : Upper (D 6) (R 6) [34,72,192,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21479
end Delivery.IrregularNine14.P06
