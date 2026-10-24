import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0045
import IrregularNine14P06C0046

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13440 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 133 88 276 34 97 225 353), lower := (rows 11 38 133 88 276 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 69 133 261), good := (rows 491 482 481 88 472 34 64 128 256) }] }

theorem u13440 : Upper (D 6) (R 6) [10,36,129,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13441 : Route 9 := (fun mask => (mask,id))

def c13441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13441 : Upper (D 6) (R 6) [10,36,129,80,260,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,260,64] 13 (by decide) (choices 1) [1,2,32] r13441 c13441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2739
  · exact u2740
  · exact u2741

def b13442 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 38 133 88 304 33 70 198 326), lower := (rows 11 38 133 88 304 33 64 128 256), losses := [] }

theorem u13442 : Upper (D 6) (R 6) [10,36,129,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13443 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 133 88 304 34 69 197 325), lower := (rows 11 38 133 88 304 34 64 128 256), losses := [] }

theorem u13443 : Upper (D 6) (R 6) [10,36,129,80,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13444 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 88 304 36 67 195 323), lower := (rows 11 38 133 88 304 36 64 128 256), losses := [] }

theorem u13444 : Upper (D 6) (R 6) [10,36,129,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13445 : Route 9 := (fun mask => (mask,id))

def c13445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13445 : Upper (D 6) (R 6) [10,36,129,80,288,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,80,288,64] 13 (by decide) (choices 1) [1,2,4] r13445 c13445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2742
  · exact u2743
  · exact u2744

def b13446 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 104 82 33 340 404 276), lower := (rows 11 38 133 104 82 33 64 128 256), losses := [] }

theorem u13446 : Upper (D 6) (R 6) [10,36,129,96,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13446 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13447 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 104 82 36 337 401 273), lower := (rows 11 38 133 104 82 36 64 128 256), losses := [] }

theorem u13447 : Upper (D 6) (R 6) [10,36,129,96,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13447 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13448 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 104 82 48 325 389 261), lower := (rows 11 38 133 104 82 48 64 128 256), losses := [] }

theorem u13448 : Upper (D 6) (R 6) [10,36,129,96,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13448 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13449 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 104 82 288 85 149 277), lower := (rows 11 38 133 104 82 288 64 128 256), losses := [] }

theorem u13449 : Upper (D 6) (R 6) [10,36,129,96,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13449 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13450 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 104 84 33 338 402 274), lower := (rows 11 38 133 104 84 33 64 128 256), losses := [] }

theorem u13450 : Upper (D 6) (R 6) [10,36,129,96,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13451 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 104 84 34 337 401 273), lower := (rows 11 38 133 104 84 34 64 128 256), losses := [] }

theorem u13451 : Upper (D 6) (R 6) [10,36,129,96,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13452 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 391, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 104 84 48 323 387 259), lower := (rows 11 38 133 104 84 48 64 128 256), losses := [] }

theorem u13452 : Upper (D 6) (R 6) [10,36,129,96,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13452 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13453 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 104 84 288 83 147 275), lower := (rows 11 38 133 104 84 288 64 128 256), losses := [] }

theorem u13453 : Upper (D 6) (R 6) [10,36,129,96,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13453 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13454 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 104 273 34 84 212 340), lower := (rows 11 38 133 104 273 34 64 128 256), losses := [] }

theorem u13454 : Upper (D 6) (R 6) [10,36,129,96,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13455 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 104 273 36 82 210 338), lower := (rows 11 38 133 104 273 36 64 128 256), losses := [] }

theorem u13455 : Upper (D 6) (R 6) [10,36,129,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13456 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 104 273 48 70 198 326), lower := (rows 11 38 133 104 273 48 64 128 256), losses := [] }

theorem u13456 : Upper (D 6) (R 6) [10,36,129,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13456 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13457 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 104 273 96 86 150 278), lower := (rows 11 38 133 104 273 96 64 128 256), losses := [] }

theorem u13457 : Upper (D 6) (R 6) [10,36,129,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13458 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 104 274 33 84 212 340), lower := (rows 11 38 133 104 274 33 64 128 256), losses := [] }

theorem u13458 : Upper (D 6) (R 6) [10,36,129,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13459 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 104 274 36 81 209 337), lower := (rows 11 38 133 104 274 36 64 128 256), losses := [] }

theorem u13459 : Upper (D 6) (R 6) [10,36,129,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13460 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 104 274 48 69 197 325), lower := (rows 11 38 133 104 274 48 64 128 256), losses := [] }

theorem u13460 : Upper (D 6) (R 6) [10,36,129,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13460 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13461 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 104 274 96 85 149 277), lower := (rows 11 38 133 104 274 96 64 128 256), losses := [] }

theorem u13461 : Upper (D 6) (R 6) [10,36,129,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13462 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 104 276 33 82 210 338), lower := (rows 11 38 133 104 276 33 64 128 256), losses := [] }

theorem u13462 : Upper (D 6) (R 6) [10,36,129,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13463 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 104 276 34 81 209 337), lower := (rows 11 38 133 104 276 34 64 128 256), losses := [] }

theorem u13463 : Upper (D 6) (R 6) [10,36,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13464 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 133 104 276 48 67 195 323), lower := (rows 11 38 133 104 276 48 64 128 256), losses := [] }

theorem u13464 : Upper (D 6) (R 6) [10,36,129,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13464 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13465 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 104 276 96 83 147 275), lower := (rows 11 38 133 104 276 96 64 128 256), losses := [] }

theorem u13465 : Upper (D 6) (R 6) [10,36,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13466 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 344, targets := 1 }], pairs := [(2,5),(3,0),(4,5)], upper := (rows 11 38 133 104 336 33 86 150 278), lower := (rows 11 38 133 104 336 33 64 128 256), losses := [] }

theorem u13466 : Upper (D 6) (R 6) [10,36,129,96,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13467 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 133 104 336 34 85 149 277), lower := (rows 11 38 133 104 336 34 64 128 256), losses := [] }

theorem u13467 : Upper (D 6) (R 6) [10,36,129,96,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13468 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 104 336 36 83 147 275), lower := (rows 11 38 133 104 336 36 64 128 256), losses := [] }

theorem u13468 : Upper (D 6) (R 6) [10,36,129,96,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13469 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 135, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 38 133 104 336 48 71 135 263), lower := (rows 11 38 133 104 336 48 64 128 256), losses := [] }

theorem u13469 : Upper (D 6) (R 6) [10,36,129,96,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13469 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13470 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 265 82 36 112 240 368), lower := (rows 11 38 133 265 82 36 64 128 256), losses := [] }

theorem u13470 : Upper (D 6) (R 6) [10,36,129,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13471 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 38 133 265 82 48 100 228 356), lower := (rows 11 38 133 265 82 48 64 128 256), losses := [] }

theorem u13471 : Upper (D 6) (R 6) [10,36,129,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13471 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13472 : Route 9 := (fun mask => (mask,id))

def c13472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13472 : Upper (D 6) (R 6) [10,36,129,257,66,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257,66,64] 13 (by decide) (choices 1) [4,16,32] r13472 c13472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2745
  · exact u2746
  · exact u2747

def b13473 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 265 84 34 112 240 368), lower := (rows 11 38 133 265 84 34 64 128 256), losses := [] }

theorem u13473 : Upper (D 6) (R 6) [10,36,129,257,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13474 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 133 265 84 48 98 226 354), lower := (rows 11 38 133 265 84 48 64 128 256), losses := [] }

theorem u13474 : Upper (D 6) (R 6) [10,36,129,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13474 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13475 : Route 9 := (fun mask => (mask,id))

def c13475 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13475 : Upper (D 6) (R 6) [10,36,129,257,68,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,257,68,64] 13 (by decide) (choices 1) [2,16,32] r13475 c13475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2748
  · exact u2749
  · exact u2750

def b13476 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 1, region := 80, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 133 265 112 34 84 212 340), lower := (rows 11 38 133 265 112 34 64 128 256), losses := [] }

theorem u13476 : Upper (D 6) (R 6) [10,36,129,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13477 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 265 112 36 82 210 338), lower := (rows 11 38 133 265 112 36 64 128 256), losses := [] }

theorem u13477 : Upper (D 6) (R 6) [10,36,129,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13477 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13478 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 265 112 48 70 198 326), lower := (rows 11 38 133 265 112 48 64 128 256), losses := [] }

theorem u13478 : Upper (D 6) (R 6) [10,36,129,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13478 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13479 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 265 112 96 86 150 278), lower := (rows 11 38 133 265 112 96 64 128 256), losses := [] }

theorem u13479 : Upper (D 6) (R 6) [10,36,129,257,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13480 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 133 268 49 34 80 208 336), lower := (rows 11 38 133 268 49 34 64 128 256), losses := [] }

theorem u13480 : Upper (D 6) (R 6) [10,36,129,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13481 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 268 49 48 66 194 322), lower := (rows 11 38 133 268 49 48 64 128 256), losses := [] }

theorem u13481 : Upper (D 6) (R 6) [10,36,129,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13481 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13482 : Route 9 := (fun mask => (mask,id))

def c13482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13482 : Upper (D 6) (R 6) [10,36,129,260,33,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,33,64] 13 (by decide) (choices 1) [2,16] r13482 c13482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2751
  · exact u2752

def b13483 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 268 81 34 112 240 368), lower := (rows 11 38 133 268 81 34 64 128 256), losses := [] }

theorem u13483 : Upper (D 6) (R 6) [10,36,129,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13483 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13484 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 112, targets := 4 },{ cop := 1, region := 328, targets := 1 }], pairs := [(3,0),(4,2)], upper := (rows 11 38 133 268 81 48 98 226 354), lower := (rows 11 38 133 268 81 48 64 128 256), losses := [] }

theorem u13484 : Upper (D 6) (R 6) [10,36,129,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13484 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13485 : Route 9 := (fun mask => (mask,id))

def c13485 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13485 : Upper (D 6) (R 6) [10,36,129,260,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,65,64] 13 (by decide) (choices 1) [2,16,32] r13485 c13485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2753
  · exact u2754
  · exact u2755

def b13486 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 268 82 33 112 240 368), lower := (rows 11 38 133 268 82 33 64 128 256), losses := [] }

theorem u13486 : Upper (D 6) (R 6) [10,36,129,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13486 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13487 : Route 9 := (fun mask => (mask,id))

def c13487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13487 : Upper (D 6) (R 6) [10,36,129,260,66,16] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,66,16] 13 (by decide) (choices 1) [1,32] r13487 c13487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2756
  · exact u2757

def r13488 : Route 9 := (fun mask => (mask,id))

def c13488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13488 : Upper (D 6) (R 6) [10,36,129,260,66,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,260,66,64] 13 (by decide) (choices 1) [1,16,32] r13488 c13488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2758
  · exact u2759
  · exact u2760

def b13489 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 11 38 133 268 112 33 82 210 338), lower := (rows 11 38 133 268 112 33 64 128 256), losses := [] }

theorem u13489 : Upper (D 6) (R 6) [10,36,129,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13490 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 133 268 112 34 81 209 337), lower := (rows 11 38 133 268 112 34 64 128 256), losses := [] }

theorem u13490 : Upper (D 6) (R 6) [10,36,129,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13490 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13491 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 133 268 112 48 67 195 323), lower := (rows 11 38 133 268 112 48 64 128 256), losses := [] }

theorem u13491 : Upper (D 6) (R 6) [10,36,129,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13491 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13492 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 11 38 133 268 112 96 83 147 275), lower := (rows 11 38 133 268 112 96 64 128 256), losses := [] }

theorem u13492 : Upper (D 6) (R 6) [10,36,129,260,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13492 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13493 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 34, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 38 133 280 81 34 100 228 356), lower := (rows 11 38 133 280 81 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 17 32 66 130 258), good := (rows 477 484 157 280 93 480 64 128 256) }] }

theorem u13493 : Upper (D 6) (R 6) [10,36,129,272,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13494 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 280 81 36 98 226 354), lower := (rows 11 38 133 280 81 36 64 128 256), losses := [] }

theorem u13494 : Upper (D 6) (R 6) [10,36,129,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13495 : Route 9 := (fun mask => (mask,id))

def c13495 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13495 : Upper (D 6) (R 6) [10,36,129,272,65,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,65,64] 13 (by decide) (choices 1) [2,4,32] r13495 c13495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2761
  · exact u2762
  · exact u2763

def b13496 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 38 133 280 82 33 100 228 356), lower := (rows 11 38 133 280 82 33 64 128 256), losses := [] }

theorem u13496 : Upper (D 6) (R 6) [10,36,129,272,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13496 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13497 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 133 280 82 36 97 225 353), lower := (rows 11 38 133 280 82 36 64 128 256), losses := [] }

theorem u13497 : Upper (D 6) (R 6) [10,36,129,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13498 : Route 9 := (fun mask => (mask,id))

def c13498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13498 : Upper (D 6) (R 6) [10,36,129,272,66,64] 13 := by
  apply FastRouting.sound _ _ [10,36,129,272,66,64] 13 (by decide) (choices 1) [1,4,32] r13498 c13498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2764
  · exact u2765
  · exact u2766

def b13499 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 38 133 280 84 33 98 226 354), lower := (rows 11 38 133 280 84 33 64 128 256), losses := [] }

theorem u13499 : Upper (D 6) (R 6) [10,36,129,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13499
end Delivery.IrregularNine14.P06
