import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 274 33 68 224 352), lower := (rows 11 98 148 13 274 33 68 128 256), losses := [] }

theorem u3420 : Upper (D 6) (R 6) [10,96,144,5,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3421 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 148 13 274 36 96 193 321), lower := (rows 11 98 148 13 274 36 96 128 256), losses := [] }

theorem u3421 : Upper (D 6) (R 6) [10,96,144,5,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 304 34 65 196 324), lower := (rows 11 98 148 13 304 34 65 128 256), losses := [] }

theorem u3422 : Upper (D 6) (R 6) [10,96,144,5,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3423 : Route 9 := (fun mask => (mask,id))

def c3423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3423 : Upper (D 6) (R 6) [10,96,144,5,288,2,4] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,288,2,4] 13 (by decide) (choices 1) [1,64] r3423 c3423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u246
  · exact u247

def b3424 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 13 304 36 65 194 322), lower := (rows 11 98 148 13 304 36 65 128 256), losses := [] }

theorem u3424 : Upper (D 6) (R 6) [10,96,144,5,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3425 : Route 9 := (fun mask => (mask,id))

def c3425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3425 : Upper (D 6) (R 6) [10,96,144,5,288,4,2] 13 := by
  apply FastRouting.sound _ _ [10,96,144,5,288,4,2] 13 (by decide) (choices 1) [1,64] r3425 c3425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u248
  · exact u249

def b3426 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 44 274 33 65 196 324), lower := (rows 11 98 148 44 274 33 65 128 256), losses := [] }

theorem u3426 : Upper (D 6) (R 6) [10,96,144,36,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3427 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 148 44 274 33 68 193 321), lower := (rows 11 98 148 44 274 33 68 128 256), losses := [] }

theorem u3427 : Upper (D 6) (R 6) [10,96,144,36,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3428 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 44 336 33 65 134 262), lower := (rows 11 98 148 44 336 33 65 128 256), losses := [] }

theorem u3428 : Upper (D 6) (R 6) [10,96,144,36,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3429 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 67, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 98 148 44 336 33 66 133 261), lower := (rows 11 98 148 44 336 33 66 128 256), losses := [] }

theorem u3429 : Upper (D 6) (R 6) [10,96,144,36,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3430 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 98 148 44 336 33 68 131 259), lower := (rows 11 98 148 44 336 33 68 128 256), losses := [] }

theorem u3430 : Upper (D 6) (R 6) [10,96,144,36,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3431 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 198, targets := 1 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 148 265 49 36 66 196 324), lower := (rows 11 98 148 265 49 36 66 128 256), losses := [] }

theorem u3431 : Upper (D 6) (R 6) [10,96,144,257,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3432 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 148 265 49 36 68 194 322), lower := (rows 11 98 148 265 49 36 68 128 256), losses := [] }

theorem u3432 : Upper (D 6) (R 6) [10,96,144,257,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3433 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 148 265 52 34 65 196 324), lower := (rows 11 98 148 265 52 34 65 128 256), losses := [] }

theorem u3433 : Upper (D 6) (R 6) [10,96,144,257,36,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3434 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 265 52 34 68 193 321), lower := (rows 11 98 148 265 52 34 68 128 256), losses := [] }

theorem u3434 : Upper (D 6) (R 6) [10,96,144,257,36,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 268 22 33 65 224 352), lower := (rows 11 98 148 268 22 33 65 128 256), losses := [] }

theorem u3435 : Upper (D 6) (R 6) [10,96,144,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 98 148 268 22 33 96 193 321), lower := (rows 11 98 148 268 22 33 96 128 256), losses := [] }

theorem u3436 : Upper (D 6) (R 6) [10,96,144,260,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 268 52 33 65 194 322), lower := (rows 11 98 148 268 52 33 65 128 256), losses := [] }

theorem u3437 : Upper (D 6) (R 6) [10,96,144,260,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 148 268 52 33 66 193 321), lower := (rows 11 98 148 268 52 33 66 128 256), losses := [] }

theorem u3438 : Upper (D 6) (R 6) [10,96,144,260,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 68, camps := [{ cop := 8, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 21 33 66 196 324), lower := (rows 11 98 148 296 21 33 66 128 256), losses := [] }

theorem u3439 : Upper (D 6) (R 6) [10,96,144,288,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 21 33 68 194 322), lower := (rows 11 98 148 296 21 33 68 128 256), losses := [] }

theorem u3440 : Upper (D 6) (R 6) [10,96,144,288,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 296 22 33 65 196 324), lower := (rows 11 98 148 296 22 33 65 128 256), losses := [] }

theorem u3441 : Upper (D 6) (R 6) [10,96,144,288,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 22 33 68 193 321), lower := (rows 11 98 148 296 22 33 68 128 256), losses := [] }

theorem u3442 : Upper (D 6) (R 6) [10,96,144,288,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 98 148 296 81 36 65 134 262), lower := (rows 11 98 148 296 81 36 65 128 256), losses := [] }

theorem u3443 : Upper (D 6) (R 6) [10,96,144,288,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 148 296 81 36 66 133 261), lower := (rows 11 98 148 296 81 36 66 128 256), losses := [] }

theorem u3444 : Upper (D 6) (R 6) [10,96,144,288,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 98 148 296 81 36 68 131 259), lower := (rows 11 98 148 296 81 36 68 128 256), losses := [] }

theorem u3445 : Upper (D 6) (R 6) [10,96,144,288,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3446 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 148 296 84 33 65 134 262), lower := (rows 11 98 148 296 84 33 65 128 256), losses := [] }

theorem u3446 : Upper (D 6) (R 6) [10,96,144,288,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3447 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 148 296 84 33 66 133 261), lower := (rows 11 98 148 296 84 33 66 128 256), losses := [] }

theorem u3447 : Upper (D 6) (R 6) [10,96,144,288,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3448 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 84, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 11 98 148 296 84 33 68 131 259), lower := (rows 11 98 148 296 84 33 68 128 256), losses := [] }

theorem u3448 : Upper (D 6) (R 6) [10,96,144,288,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3449 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 13 84 288 65 146 274), lower := (rows 11 98 164 13 84 288 65 128 256), losses := [] }

theorem u3449 : Upper (D 6) (R 6) [10,96,160,5,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3449 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3450 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 164 13 84 288 66 145 273), lower := (rows 11 98 164 13 84 288 66 128 256), losses := [] }

theorem u3450 : Upper (D 6) (R 6) [10,96,160,5,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3450 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6)], upper := (rows 11 98 164 13 84 288 80 131 259), lower := (rows 11 98 164 13 84 288 80 128 256), losses := [] }

theorem u3451 : Upper (D 6) (R 6) [10,96,160,5,68,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3451 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3452 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 13 274 48 65 196 324), lower := (rows 11 98 164 13 274 48 65 128 256), losses := [] }

theorem u3452 : Upper (D 6) (R 6) [10,96,160,5,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3452 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(4,5)], upper := (rows 11 98 164 13 274 48 68 193 321), lower := (rows 11 98 164 13 274 48 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 76 137 265), good := (rows 475 66 196 477 274 16 68 128 256) }] }

theorem u3453 : Upper (D 6) (R 6) [10,96,160,5,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3453 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 13 276 48 65 194 322), lower := (rows 11 98 164 13 276 48 65 128 256), losses := [] }

theorem u3454 : Upper (D 6) (R 6) [10,96,160,5,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3454 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 11 98 164 13 276 48 66 193 321), lower := (rows 11 98 164 13 276 48 66 128 256), losses := [] }

theorem u3455 : Upper (D 6) (R 6) [10,96,160,5,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3455 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 98 164 25 84 288 65 134 262), lower := (rows 11 98 164 25 84 288 65 128 256), losses := [] }

theorem u3456 : Upper (D 6) (R 6) [10,96,160,17,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3456 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 420, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 98 164 25 84 288 66 133 261), lower := (rows 11 98 164 25 84 288 66 128 256), losses := [] }

theorem u3457 : Upper (D 6) (R 6) [10,96,160,17,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3457 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3458 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 98 164 25 84 288 68 131 259), lower := (rows 11 98 164 25 84 288 68 128 256), losses := [] }

theorem u3458 : Upper (D 6) (R 6) [10,96,160,17,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3458 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 25 276 34 65 196 324), lower := (rows 11 98 164 25 276 34 65 128 256), losses := [] }

theorem u3459 : Upper (D 6) (R 6) [10,96,160,17,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 164 25 276 34 68 193 321), lower := (rows 11 98 164 25 276 34 68 128 256), losses := [] }

theorem u3460 : Upper (D 6) (R 6) [10,96,160,17,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 164 28 273 33 66 196 324), lower := (rows 11 98 164 28 273 33 66 128 256), losses := [] }

theorem u3461 : Upper (D 6) (R 6) [10,96,160,20,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3462 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 11 98 164 28 273 33 68 194 322), lower := (rows 11 98 164 28 273 33 68 128 256), losses := [{ target := 2, region := (rows 1 2 0 8 17 49 64 130 258), good := (rows 443 482 160 56 305 49 64 128 256) }] }

theorem u3462 : Upper (D 6) (R 6) [10,96,160,20,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3463 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 164 28 273 34 65 196 324), lower := (rows 11 98 164 28 273 34 65 128 256), losses := [] }

theorem u3463 : Upper (D 6) (R 6) [10,96,160,20,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3464 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 98 164 28 273 34 68 193 321), lower := (rows 11 98 164 28 273 34 68 128 256), losses := [] }

theorem u3464 : Upper (D 6) (R 6) [10,96,160,20,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 164 28 274 33 65 196 324), lower := (rows 11 98 164 28 274 33 65 128 256), losses := [] }

theorem u3465 : Upper (D 6) (R 6) [10,96,160,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 98 164 28 274 33 68 193 321), lower := (rows 11 98 164 28 274 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 39 24 16 33 127 161 289), good := (rows 493 484 484 92 348 485 68 128 256) }] }

theorem u3466 : Upper (D 6) (R 6) [10,96,160,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 164 28 336 33 65 134 262), lower := (rows 11 98 164 28 336 33 65 128 256), losses := [] }

theorem u3467 : Upper (D 6) (R 6) [10,96,160,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 98 164 28 336 33 66 133 261), lower := (rows 11 98 164 28 336 33 66 128 256), losses := [] }

theorem u3468 : Upper (D 6) (R 6) [10,96,160,20,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 164, targets := 64 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(2,6),(4,5)], upper := (rows 11 98 164 28 336 33 68 131 259), lower := (rows 11 98 164 28 336 33 68 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 76 129 257), good := (rows 475 66 196 92 336 401 68 128 256) }] }

theorem u3469 : Upper (D 6) (R 6) [10,96,160,20,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 98 164 265 84 34 65 148 276), lower := (rows 11 98 164 265 84 34 65 128 256), losses := [] }

theorem u3470 : Upper (D 6) (R 6) [10,96,160,257,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 98 164 265 84 34 68 145 273), lower := (rows 11 98 164 265 84 34 68 128 256), losses := [] }

theorem u3471 : Upper (D 6) (R 6) [10,96,160,257,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3472 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 265 84 34 80 133 261), lower := (rows 11 98 164 265 84 34 80 128 256), losses := [] }

theorem u3472 : Upper (D 6) (R 6) [10,96,160,257,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3472 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3473 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 98 164 268 21 33 66 208 336), lower := (rows 11 98 164 268 21 33 66 128 256), losses := [] }

theorem u3473 : Upper (D 6) (R 6) [10,96,160,260,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3474 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 11 98 164 268 21 33 80 194 322), lower := (rows 11 98 164 268 21 33 80 128 256), losses := [] }

theorem u3474 : Upper (D 6) (R 6) [10,96,160,260,5,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3474 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3475 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 98 164 268 22 33 65 208 336), lower := (rows 11 98 164 268 22 33 65 128 256), losses := [] }

theorem u3475 : Upper (D 6) (R 6) [10,96,160,260,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 98 164 268 22 33 80 193 321), lower := (rows 11 98 164 268 22 33 80 128 256), losses := [] }

theorem u3476 : Upper (D 6) (R 6) [10,96,160,260,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3476 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 428, targets := 66 }], pairs := [(2,1),(2,6),(3,1)], upper := (rows 11 98 164 268 81 33 66 148 276), lower := (rows 11 98 164 268 81 33 66 128 256), losses := [] }

theorem u3477 : Upper (D 6) (R 6) [10,96,160,260,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3478 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 66, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,1)], upper := (rows 11 98 164 268 81 33 68 146 274), lower := (rows 11 98 164 268 81 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 76 128 256), good := (rows 121 96 228 332 113 49 68 128 256) }] }

theorem u3478 : Upper (D 6) (R 6) [10,96,160,260,65,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3479 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 11 98 164 268 81 33 80 134 262), lower := (rows 11 98 164 268 81 33 80 128 256), losses := [] }

theorem u3479 : Upper (D 6) (R 6) [10,96,160,260,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3479 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P06
