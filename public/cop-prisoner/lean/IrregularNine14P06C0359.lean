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

def b21540 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 265 52 34 85 149 277), lower := (rows 35 74 196 265 52 34 64 128 256), losses := [] }

theorem u21540 : Upper (D 6) (R 6) [34,72,192,257,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21541 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 196 265 52 36 83 147 275), lower := (rows 35 74 196 265 52 36 64 128 256), losses := [] }

theorem u21541 : Upper (D 6) (R 6) [34,72,192,257,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21541 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21542 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 196 265 52 48 71 135 263), lower := (rows 35 74 196 265 52 48 64 128 256), losses := [] }

theorem u21542 : Upper (D 6) (R 6) [34,72,192,257,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21542 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21543 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 196 266 21 33 116 180 308), lower := (rows 35 74 196 266 21 33 64 128 256), losses := [] }

theorem u21543 : Upper (D 6) (R 6) [34,72,192,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21544 : Route 9 := (fun mask => (mask,id))

def c21544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21544 : Upper (D 6) (R 6) [34,72,192,258,5,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,258,5,4] 13 (by decide) (choices 1) [1,16,32] r21544 c21544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6332
  · exact u6333
  · exact u6334

def b21545 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 212, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 196 266 21 48 101 165 293), lower := (rows 35 74 196 266 21 48 64 128 256), losses := [] }

theorem u21545 : Upper (D 6) (R 6) [34,72,192,258,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21545 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21546 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 196 266 52 33 85 149 277), lower := (rows 35 74 196 266 52 33 64 128 256), losses := [] }

theorem u21546 : Upper (D 6) (R 6) [34,72,192,258,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21547 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 196 266 52 36 81 145 273), lower := (rows 35 74 196 266 52 36 64 128 256), losses := [] }

theorem u21547 : Upper (D 6) (R 6) [34,72,192,258,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21548 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 196 266 52 48 69 133 261), lower := (rows 35 74 196 266 52 48 64 128 256), losses := [] }

theorem u21548 : Upper (D 6) (R 6) [34,72,192,258,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21548 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21549 : Route 9 := (fun mask => (mask,id))

def c21549 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21549 : Upper (D 6) (R 6) [34,72,192,260,5,1] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260,5,1] 13 (by decide) (choices 1) [2,16,32] r21549 c21549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6335
  · exact u6336
  · exact u6337

def b21550 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 268 21 34 113 177 305), lower := (rows 35 74 196 268 21 34 64 128 256), losses := [] }

theorem u21550 : Upper (D 6) (R 6) [34,72,192,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21551 : Route 9 := (fun mask => (mask,id))

def c21551 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21551 : Upper (D 6) (R 6) [34,72,192,260,5,16] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260,5,16] 13 (by decide) (choices 1) [1,2,32] r21551 c21551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6338
  · exact u6339
  · exact u6340

def r21552 : Route 9 := (fun mask => (mask,id))

def c21552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21552 : Upper (D 6) (R 6) [34,72,192,260,36,1] 13 := by
  apply FastRouting.sound _ _ [34,72,192,260,36,1] 13 (by decide) (choices 1) [1,2,16] r21552 c21552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6341
  · exact u6342
  · exact u6343

def b21553 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 268 52 34 81 145 273), lower := (rows 35 74 196 268 52 34 64 128 256), losses := [] }

theorem u21553 : Upper (D 6) (R 6) [34,72,192,260,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21554 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 196 268 52 48 67 131 259), lower := (rows 35 74 196 268 52 48 64 128 256), losses := [] }

theorem u21554 : Upper (D 6) (R 6) [34,72,192,260,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21554 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21555 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 196 280 21 33 102 166 294), lower := (rows 35 74 196 280 21 33 64 128 256), losses := [] }

theorem u21555 : Upper (D 6) (R 6) [34,72,192,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21556 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 280 21 34 101 165 293), lower := (rows 35 74 196 280 21 34 64 128 256), losses := [] }

theorem u21556 : Upper (D 6) (R 6) [34,72,192,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21556 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21557 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(3,2),(3,6)], upper := (rows 35 74 196 280 21 36 99 163 291), lower := (rows 35 74 196 280 21 36 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 24 16 32 65 129 257), good := (rows 483 74 192 282 475 32 64 128 256) },{ target := 6, region := (rows 1 2 4 24 16 52 0 129 257), good := (rows 419 10 164 312 445 36 0 128 256) }] }

theorem u21557 : Upper (D 6) (R 6) [34,72,192,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21558 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 74 196 280 52 33 71 135 263), lower := (rows 35 74 196 280 52 33 64 128 256), losses := [] }

theorem u21558 : Upper (D 6) (R 6) [34,72,192,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21559 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 280 52 34 69 133 261), lower := (rows 35 74 196 280 52 34 64 128 256), losses := [] }

theorem u21559 : Upper (D 6) (R 6) [34,72,192,272,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21560 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 196 280 52 36 67 131 259), lower := (rows 35 74 196 280 52 36 64 128 256), losses := [] }

theorem u21560 : Upper (D 6) (R 6) [34,72,192,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21561 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 196 296 21 33 86 150 278), lower := (rows 35 74 196 296 21 33 64 128 256), losses := [] }

theorem u21561 : Upper (D 6) (R 6) [34,72,192,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21561 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21562 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 196 296 21 34 85 149 277), lower := (rows 35 74 196 296 21 34 64 128 256), losses := [] }

theorem u21562 : Upper (D 6) (R 6) [34,72,192,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21563 : Route 9 := (fun mask => (mask,id))

def c21563 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21563 : Upper (D 6) (R 6) [34,72,192,288,5,4] 13 := by
  apply FastRouting.sound _ _ [34,72,192,288,5,4] 13 (by decide) (choices 1) [1,2,16] r21563 c21563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6344
  · exact u6345
  · exact u6346

def b21564 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 196 296 21 48 71 135 263), lower := (rows 35 74 196 296 21 48 64 128 256), losses := [] }

theorem u21564 : Upper (D 6) (R 6) [34,72,192,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21564 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21565 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 388 13 22 33 112 240 368), lower := (rows 35 74 388 13 22 33 64 128 256), losses := [] }

theorem u21565 : Upper (D 6) (R 6) [34,72,384,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21566 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 388 13 22 48 97 225 353), lower := (rows 35 74 388 13 22 48 64 128 256), losses := [] }

theorem u21566 : Upper (D 6) (R 6) [34,72,384,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21566 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21567 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 13 22 96 113 177 305), lower := (rows 35 74 388 13 22 96 64 128 256), losses := [] }

theorem u21567 : Upper (D 6) (R 6) [34,72,384,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21567 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21568 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 388 13 52 33 82 210 338), lower := (rows 35 74 388 13 52 33 64 128 256), losses := [] }

theorem u21568 : Upper (D 6) (R 6) [34,72,384,5,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21569 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 13 52 34 81 209 337), lower := (rows 35 74 388 13 52 34 64 128 256), losses := [] }

theorem u21569 : Upper (D 6) (R 6) [34,72,384,5,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21569 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21570 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 388 13 52 48 67 195 323), lower := (rows 35 74 388 13 52 48 64 128 256), losses := [] }

theorem u21570 : Upper (D 6) (R 6) [34,72,384,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21570 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21571 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 13 52 96 83 147 275), lower := (rows 35 74 388 13 52 96 64 128 256), losses := [] }

theorem u21571 : Upper (D 6) (R 6) [34,72,384,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21572 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 13 81 34 116 180 308), lower := (rows 35 74 388 13 81 34 64 128 256), losses := [] }

theorem u21572 : Upper (D 6) (R 6) [34,72,384,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21573 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 74 388 13 81 36 114 178 306), lower := (rows 35 74 388 13 81 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 384 475 465 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 43 420 45 17 36 0 128 256) }] }

theorem u21573 : Upper (D 6) (R 6) [34,72,384,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21573 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21574 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 388 13 81 48 102 166 294), lower := (rows 35 74 388 13 81 48 64 128 256), losses := [] }

theorem u21574 : Upper (D 6) (R 6) [34,72,384,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21574 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21575 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 388 13 84 33 114 178 306), lower := (rows 35 74 388 13 84 33 64 128 256), losses := [] }

theorem u21575 : Upper (D 6) (R 6) [34,72,384,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21576 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 13 84 34 113 177 305), lower := (rows 35 74 388 13 84 34 64 128 256), losses := [] }

theorem u21576 : Upper (D 6) (R 6) [34,72,384,5,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21577 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 388 13 84 48 99 163 291), lower := (rows 35 74 388 13 84 48 64 128 256), losses := [] }

theorem u21577 : Upper (D 6) (R 6) [34,72,384,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21577 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21578 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 388 13 112 33 86 150 278), lower := (rows 35 74 388 13 112 33 64 128 256), losses := [] }

theorem u21578 : Upper (D 6) (R 6) [34,72,384,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21578 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21579 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 13 112 34 85 149 277), lower := (rows 35 74 388 13 112 34 64 128 256), losses := [] }

theorem u21579 : Upper (D 6) (R 6) [34,72,384,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21580 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 4 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 74 388 13 112 36 83 147 275), lower := (rows 35 74 388 13 112 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 44 64 128 256), good := (rows 50 122 420 44 112 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 18 44 64 128 256), good := (rows 49 120 420 45 112 36 64 128 256) }] }

theorem u21580 : Upper (D 6) (R 6) [34,72,384,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21581 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 388 13 112 48 71 135 263), lower := (rows 35 74 388 13 112 48 64 128 256), losses := [] }

theorem u21581 : Upper (D 6) (R 6) [34,72,384,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21581 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21582 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 388 14 21 33 112 240 368), lower := (rows 35 74 388 14 21 33 64 128 256), losses := [] }

theorem u21582 : Upper (D 6) (R 6) [34,72,384,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21583 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 74 388 14 21 48 97 225 353), lower := (rows 35 74 388 14 21 48 64 128 256), losses := [] }

theorem u21583 : Upper (D 6) (R 6) [34,72,384,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21583 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21584 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 14 21 96 113 177 305), lower := (rows 35 74 388 14 21 96 64 128 256), losses := [] }

theorem u21584 : Upper (D 6) (R 6) [34,72,384,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21585 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 388 14 52 33 81 209 337), lower := (rows 35 74 388 14 52 33 64 128 256), losses := [] }

theorem u21585 : Upper (D 6) (R 6) [34,72,384,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21586 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 388 14 52 48 65 193 321), lower := (rows 35 74 388 14 52 48 64 128 256), losses := [] }

theorem u21586 : Upper (D 6) (R 6) [34,72,384,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21586 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21587 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 14 52 96 81 145 273), lower := (rows 35 74 388 14 52 96 64 128 256), losses := [] }

theorem u21587 : Upper (D 6) (R 6) [34,72,384,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21588 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 388 14 112 33 85 149 277), lower := (rows 35 74 388 14 112 33 64 128 256), losses := [] }

theorem u21588 : Upper (D 6) (R 6) [34,72,384,6,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21589 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 388 14 112 36 81 145 273), lower := (rows 35 74 388 14 112 36 64 128 256), losses := [] }

theorem u21589 : Upper (D 6) (R 6) [34,72,384,6,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21590 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 388 14 112 48 69 133 261), lower := (rows 35 74 388 14 112 48 64 128 256), losses := [] }

theorem u21590 : Upper (D 6) (R 6) [34,72,384,6,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21590 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21591 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 74 388 25 22 33 100 228 356), lower := (rows 35 74 388 25 22 33 64 128 256), losses := [] }

theorem u21591 : Upper (D 6) (R 6) [34,72,384,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21592 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,6),(2,1),(3,6)], upper := (rows 35 74 388 25 22 36 97 225 353), lower := (rows 35 74 388 25 22 36 64 128 256), losses := [] }

theorem u21592 : Upper (D 6) (R 6) [34,72,384,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21593 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 25 22 96 101 165 293), lower := (rows 35 74 388 25 22 96 64 128 256), losses := [] }

theorem u21593 : Upper (D 6) (R 6) [34,72,384,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21594 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 74 388 25 52 33 70 198 326), lower := (rows 35 74 388 25 52 33 64 128 256), losses := [] }

theorem u21594 : Upper (D 6) (R 6) [34,72,384,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21595 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 25 52 34 69 197 325), lower := (rows 35 74 388 25 52 34 64 128 256), losses := [] }

theorem u21595 : Upper (D 6) (R 6) [34,72,384,17,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21596 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 74 388 25 52 36 67 195 323), lower := (rows 35 74 388 25 52 36 64 128 256), losses := [] }

theorem u21596 : Upper (D 6) (R 6) [34,72,384,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21597 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 388 25 52 96 71 135 263), lower := (rows 35 74 388 25 52 96 64 128 256), losses := [] }

theorem u21597 : Upper (D 6) (R 6) [34,72,384,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21598 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 388 25 84 33 102 166 294), lower := (rows 35 74 388 25 84 33 64 128 256), losses := [] }

theorem u21598 : Upper (D 6) (R 6) [34,72,384,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21599 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 388 25 84 34 101 165 293), lower := (rows 35 74 388 25 84 34 64 128 256), losses := [] }

theorem u21599 : Upper (D 6) (R 6) [34,72,384,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21599
end Delivery.IrregularNine14.P06
