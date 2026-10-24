import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0229
import IrregularNine14P06C0230

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31560 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 11 38 148 328 52 99 67 195 323), lower := (rows 11 38 148 328 52 32 64 128 256), losses := [] }

theorem u31560 : Upper (D 6) (R 6) [10,36,144,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31561 : Route 9 := (fun mask => (mask,id))

def c31561 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31561 : Upper (D 6) (R 6) [10,36,144,320,65] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,65] 13 (by decide) (choices 1) [1,2,4] r31561 c31561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13769
  · exact u13770
  · exact u13771

def r31562 : Route 9 := (fun mask => (mask,id))

def c31562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31562 : Upper (D 6) (R 6) [10,36,144,320,66] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,66] 13 (by decide) (choices 1) [1,4] r31562 c31562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13772
  · exact u13773

def r31563 : Route 9 := (fun mask => (mask,id))

def c31563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31563 : Upper (D 6) (R 6) [10,36,144,320,68] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,68] 13 (by decide) (choices 1) [1,2] r31563 c31563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13774
  · exact u13775

def r31564 : Route 9 := (fun mask => (mask,id))

def c31564 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31564 : Upper (D 6) (R 6) [10,36,144,320,96] 13 := by
  apply FastRouting.sound _ _ [10,36,144,320,96] 13 (by decide) (choices 1) [1,2,4] r31564 c31564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13776
  · exact u13777
  · exact u13778

def b31565 : PairBound 9 := { available := 356, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 25 19 356 356 484 356), lower := (rows 11 38 196 25 19 32 64 128 256), losses := [] }

theorem u31565 : Upper (D 6) (R 6) [10,36,192,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31566 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 196 25 21 354 354 482 354), lower := (rows 11 38 196 25 21 32 64 128 256), losses := [] }

theorem u31566 : Upper (D 6) (R 6) [10,36,192,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31567 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 196 25 22 353 353 481 353), lower := (rows 11 38 196 25 22 32 64 128 256), losses := [] }

theorem u31567 : Upper (D 6) (R 6) [10,36,192,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31568 : PairBound 9 := { available := 326, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 25 49 358 326 454 326), lower := (rows 11 38 196 25 49 32 64 128 256), losses := [] }

theorem u31568 : Upper (D 6) (R 6) [10,36,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31569 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 25 50 357 325 453 325), lower := (rows 11 38 196 25 50 32 64 128 256), losses := [] }

theorem u31569 : Upper (D 6) (R 6) [10,36,192,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31570 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 25 52 355 323 451 323), lower := (rows 11 38 196 25 52 32 64 128 256), losses := [] }

theorem u31570 : Upper (D 6) (R 6) [10,36,192,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31571 : PairBound 9 := { available := 294, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 196 25 81 294 358 422 294), lower := (rows 11 38 196 25 81 32 64 128 256), losses := [] }

theorem u31571 : Upper (D 6) (R 6) [10,36,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31572 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 25 82 293 357 421 293), lower := (rows 11 38 196 25 82 32 64 128 256), losses := [] }

theorem u31572 : Upper (D 6) (R 6) [10,36,192,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31573 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 25 84 291 355 419 291), lower := (rows 11 38 196 25 84 32 64 128 256), losses := [] }

theorem u31573 : Upper (D 6) (R 6) [10,36,192,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31574 : Route 9 := (fun mask => (mask,id))

def c31574 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31574 : Upper (D 6) (R 6) [10,36,192,17,96] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,96] 13 (by decide) (choices 1) [1,2,4,256] r31574 c31574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13779
  · exact u13780
  · exact u13781
  · exact u13782

def b31575 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 196 25 273 102 102 230 358), lower := (rows 11 38 196 25 273 32 64 128 256), losses := [] }

theorem u31575 : Upper (D 6) (R 6) [10,36,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31576 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 38 196 25 274 101 101 229 357), lower := (rows 11 38 196 25 274 32 64 128 256), losses := [] }

theorem u31576 : Upper (D 6) (R 6) [10,36,192,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31577 : Route 9 := (fun mask => (mask,id))

def c31577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31577 : Upper (D 6) (R 6) [10,36,192,17,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,260] 13 (by decide) (choices 1) [1,2,64] r31577 c31577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13783
  · exact u13784
  · exact u13785

def r31578 : Route 9 := (fun mask => (mask,id))

def c31578 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31578 : Upper (D 6) (R 6) [10,36,192,17,288] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,288] 13 (by decide) (choices 1) [1,2,4,64] r31578 c31578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13786
  · exact u13787
  · exact u13788
  · exact u13789

def r31579 : Route 9 := (fun mask => (mask,id))

def c31579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31579 : Upper (D 6) (R 6) [10,36,192,17,320] 13 := by
  apply FastRouting.sound _ _ [10,36,192,17,320] 13 (by decide) (choices 1) [1,2,4] r31579 c31579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13790
  · exact u13791
  · exact u13792

def b31580 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 196 28 19 353 353 481 353), lower := (rows 11 38 196 28 19 32 64 128 256), losses := [] }

theorem u31580 : Upper (D 6) (R 6) [10,36,192,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31581 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 28 49 355 323 451 323), lower := (rows 11 38 196 28 49 32 64 128 256), losses := [] }

theorem u31581 : Upper (D 6) (R 6) [10,36,192,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31582 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 28 50 353 321 449 321), lower := (rows 11 38 196 28 50 32 64 128 256), losses := [] }

theorem u31582 : Upper (D 6) (R 6) [10,36,192,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31583 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 28 81 291 355 419 291), lower := (rows 11 38 196 28 81 32 64 128 256), losses := [] }

theorem u31583 : Upper (D 6) (R 6) [10,36,192,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31584 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 484, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 11 38 196 28 82 289 353 417 289), lower := (rows 11 38 196 28 82 32 64 128 256), losses := [] }

theorem u31584 : Upper (D 6) (R 6) [10,36,192,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31585 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 291, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 28 112 291 323 387 259), lower := (rows 11 38 196 28 112 32 64 128 256), losses := [] }

theorem u31585 : Upper (D 6) (R 6) [10,36,192,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31586 : Route 9 := (fun mask => (mask,id))

def c31586 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31586 : Upper (D 6) (R 6) [10,36,192,20,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,20,257] 13 (by decide) (choices 1) [1,2,64] r31586 c31586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13793
  · exact u13794
  · exact u13795

def r31587 : Route 9 := (fun mask => (mask,id))

def c31587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31587 : Upper (D 6) (R 6) [10,36,192,20,258] 13 := by
  apply FastRouting.sound _ _ [10,36,192,20,258] 13 (by decide) (choices 1) [1,64] r31587 c31587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13796
  · exact u13797

def r31588 : Route 9 := (fun mask => (mask,id))

def c31588 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31588 : Upper (D 6) (R 6) [10,36,192,20,288] 13 := by
  apply FastRouting.sound _ _ [10,36,192,20,288] 13 (by decide) (choices 1) [1,2,64] r31588 c31588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13798
  · exact u13799
  · exact u13800

def b31589 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 368, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 28 336 35 99 163 291), lower := (rows 11 38 196 28 336 32 64 128 256), losses := [] }

theorem u31589 : Upper (D 6) (R 6) [10,36,192,20,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31590 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 196 56 19 357 325 453 325), lower := (rows 11 38 196 56 19 32 64 128 256), losses := [] }

theorem u31590 : Upper (D 6) (R 6) [10,36,192,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31590 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31591 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 56 21 355 323 451 323), lower := (rows 11 38 196 56 21 32 64 128 256), losses := [] }

theorem u31591 : Upper (D 6) (R 6) [10,36,192,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31592 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 56 22 353 321 449 321), lower := (rows 11 38 196 56 22 32 64 128 256), losses := [] }

theorem u31592 : Upper (D 6) (R 6) [10,36,192,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31593 : Route 9 := (fun mask => (mask,id))

def c31593 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31593 : Upper (D 6) (R 6) [10,36,192,48,65] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,65] 13 (by decide) (choices 1) [1,2,4,256] r31593 c31593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13801
  · exact u13802
  · exact u13803
  · exact u13804

def b31594 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 452, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 196 56 82 293 325 389 261), lower := (rows 11 38 196 56 82 32 64 128 256), losses := [] }

theorem u31594 : Upper (D 6) (R 6) [10,36,192,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31595 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 196 56 84 291 323 387 259), lower := (rows 11 38 196 56 84 32 64 128 256), losses := [] }

theorem u31595 : Upper (D 6) (R 6) [10,36,192,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31596 : Route 9 := (fun mask => (mask,id))

def c31596 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31596 : Upper (D 6) (R 6) [10,36,192,48,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,257] 13 (by decide) (choices 1) [1,2,4,64] r31596 c31596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13805
  · exact u13806
  · exact u13807
  · exact u13808

def b31597 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 11 38 196 56 274 101 69 197 325), lower := (rows 11 38 196 56 274 32 64 128 256), losses := [] }

theorem u31597 : Upper (D 6) (R 6) [10,36,192,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31598 : Route 9 := (fun mask => (mask,id))

def c31598 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31598 : Upper (D 6) (R 6) [10,36,192,48,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,260] 13 (by decide) (choices 1) [1,2,64] r31598 c31598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13809
  · exact u13810
  · exact u13811

def r31599 : Route 9 := (fun mask => (mask,id))

def c31599 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31599 : Upper (D 6) (R 6) [10,36,192,48,320] 13 := by
  apply FastRouting.sound _ _ [10,36,192,48,320] 13 (by decide) (choices 1) [1,2,4] r31599 c31599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13812
  · exact u13813
  · exact u13814

def b31600 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 196 73 19 308 372 436 308), lower := (rows 11 38 196 73 19 32 64 128 256), losses := [] }

theorem u31600 : Upper (D 6) (R 6) [10,36,192,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31601 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 290, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 73 21 306 370 434 306), lower := (rows 11 38 196 73 21 32 64 128 256), losses := [] }

theorem u31601 : Upper (D 6) (R 6) [10,36,192,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31602 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 73 22 305 369 433 305), lower := (rows 11 38 196 73 22 32 64 128 256), losses := [] }

theorem u31602 : Upper (D 6) (R 6) [10,36,192,65,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31603 : Route 9 := (fun mask => (mask,id))

def c31603 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31603 : Upper (D 6) (R 6) [10,36,192,65,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,33] 13 (by decide) (choices 1) [2,4,16,256] r31603 c31603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13815
  · exact u13816
  · exact u13817
  · exact u13818

def b31604 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 73 50 309 341 405 277), lower := (rows 11 38 196 73 50 32 64 128 256), losses := [] }

theorem u31604 : Upper (D 6) (R 6) [10,36,192,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31604 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31605 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 196 73 52 307 339 403 275), lower := (rows 11 38 196 73 52 32 64 128 256), losses := [] }

theorem u31605 : Upper (D 6) (R 6) [10,36,192,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31605 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31606 : Route 9 := (fun mask => (mask,id))

def c31606 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31606 : Upper (D 6) (R 6) [10,36,192,65,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,257] 13 (by decide) (choices 1) [2,4,16] r31606 c31606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13819
  · exact u13820
  · exact u13821

def r31607 : Route 9 := (fun mask => (mask,id))

def c31607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31607 : Upper (D 6) (R 6) [10,36,192,65,258] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,258] 13 (by decide) (choices 1) [1,4,16] r31607 c31607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13822
  · exact u13823
  · exact u13824

def r31608 : Route 9 := (fun mask => (mask,id))

def c31608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31608 : Upper (D 6) (R 6) [10,36,192,65,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,260] 13 (by decide) (choices 1) [1,2,16] r31608 c31608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13825
  · exact u13826
  · exact u13827

def r31609 : Route 9 := (fun mask => (mask,id))

def c31609 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31609 : Upper (D 6) (R 6) [10,36,192,65,288] 13 := by
  apply FastRouting.sound _ _ [10,36,192,65,288] 13 (by decide) (choices 1) [1,2,4,16] r31609 c31609
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13828
  · exact u13829
  · exact u13830
  · exact u13831

def b31610 : PairBound 9 := { available := 293, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 196 88 19 293 357 421 293), lower := (rows 11 38 196 88 19 32 64 128 256), losses := [] }

theorem u31610 : Upper (D 6) (R 6) [10,36,192,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31611 : PairBound 9 := { available := 291, camps := [{ cop := 4, region := 290, targets := 64 }], pairs := [(0,6),(1,6),(3,2)], upper := (rows 11 38 196 88 21 291 355 419 291), lower := (rows 11 38 196 88 21 32 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 33 65 129 257), good := (rows 491 34 192 88 505 32 64 128 256) },{ target := 6, region := (rows 9 18 4 8 16 57 0 153 281), good := (rows 427 38 132 443 439 32 0 128 256) }] }

theorem u31611 : Upper (D 6) (R 6) [10,36,192,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31612 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 196 88 22 289 353 417 289), lower := (rows 11 38 196 88 22 32 64 128 256), losses := [] }

theorem u31612 : Upper (D 6) (R 6) [10,36,192,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31613 : Route 9 := (fun mask => (mask,id))

def c31613 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31613 : Upper (D 6) (R 6) [10,36,192,80,33] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,33] 13 (by decide) (choices 1) [1,2,4,256] r31613 c31613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13832
  · exact u13833
  · exact u13834
  · exact u13835

def b31614 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 196 88 50 293 325 389 261), lower := (rows 11 38 196 88 50 32 64 128 256), losses := [] }

theorem u31614 : Upper (D 6) (R 6) [10,36,192,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31615 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 196 88 52 291 323 387 259), lower := (rows 11 38 196 88 52 32 64 128 256), losses := [] }

theorem u31615 : Upper (D 6) (R 6) [10,36,192,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31615 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31616 : Route 9 := (fun mask => (mask,id))

def c31616 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31616 : Upper (D 6) (R 6) [10,36,192,80,257] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,257] 13 (by decide) (choices 1) [1,2,4] r31616 c31616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13836
  · exact u13837
  · exact u13838

def r31617 : Route 9 := (fun mask => (mask,id))

def c31617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31617 : Upper (D 6) (R 6) [10,36,192,80,258] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,258] 13 (by decide) (choices 1) [1,4] r31617 c31617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13839
  · exact u13840

def r31618 : Route 9 := (fun mask => (mask,id))

def c31618 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31618 : Upper (D 6) (R 6) [10,36,192,80,260] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,260] 13 (by decide) (choices 1) [1,2] r31618 c31618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13841
  · exact u13842

def r31619 : Route 9 := (fun mask => (mask,id))

def c31619 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31619 : Upper (D 6) (R 6) [10,36,192,80,288] 13 := by
  apply FastRouting.sound _ _ [10,36,192,80,288] 13 (by decide) (choices 1) [1,2,4] r31619 c31619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13843
  · exact u13844
  · exact u13845

#print axioms u31619
end Delivery.IrregularNine14.P06
