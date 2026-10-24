import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0344
import IrregularNine14P07C0345

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b35520 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 28 112 232 200 200 456), lower := (rows 35 259 7 28 112 32 64 128 256), losses := [] }

theorem u35520 : Upper (D 7) (R 7) [34,257,3,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35521 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 28 208 232 232 232 488), lower := (rows 35 259 7 28 208 32 64 128 256), losses := [] }

theorem u35521 : Upper (D 7) (R 7) [34,257,3,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35521 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35522 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 7 44 88 240 208 208 464), lower := (rows 35 259 7 44 88 32 64 128 256), losses := [] }

theorem u35522 : Upper (D 7) (R 7) [34,257,3,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35522 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35523 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 7 44 208 248 216 216 472), lower := (rows 35 259 7 44 208 32 64 128 256), losses := [] }

theorem u35523 : Upper (D 7) (R 7) [34,257,3,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35523 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35524 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 56 84 232 200 200 456), lower := (rows 35 259 7 56 84 32 64 128 256), losses := [] }

theorem u35524 : Upper (D 7) (R 7) [34,257,3,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35525 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 56 88 228 196 196 452), lower := (rows 35 259 7 56 88 32 64 128 256), losses := [] }

theorem u35525 : Upper (D 7) (R 7) [34,257,3,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35525 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35526 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 56 208 236 204 204 460), lower := (rows 35 259 7 56 208 32 64 128 256), losses := [] }

theorem u35526 : Upper (D 7) (R 7) [34,257,3,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35526 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35527 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 76 112 184 216 152 408), lower := (rows 35 259 7 76 112 32 64 128 256), losses := [] }

theorem u35527 : Upper (D 7) (R 7) [34,257,3,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35528 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 76 152 240 240 240 496), lower := (rows 35 259 7 76 152 32 64 128 256), losses := [] }

theorem u35528 : Upper (D 7) (R 7) [34,257,3,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35528 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35529 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 76 176 248 216 216 472), lower := (rows 35 259 7 76 176 32 64 128 256), losses := [] }

theorem u35529 : Upper (D 7) (R 7) [34,257,3,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35529 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35530 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 76 208 184 248 184 440), lower := (rows 35 259 7 76 208 32 64 128 256), losses := [] }

theorem u35530 : Upper (D 7) (R 7) [34,257,3,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35530 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35531 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 88 152 228 228 228 484), lower := (rows 35 259 7 88 152 32 64 128 256), losses := [] }

theorem u35531 : Upper (D 7) (R 7) [34,257,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35531 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35532 : PairBound 9 := { available := 204, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 88 176 236 204 204 460), lower := (rows 35 259 7 88 176 32 64 128 256), losses := [] }

theorem u35532 : Upper (D 7) (R 7) [34,257,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35533 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 35 259 7 104 208 188 220 156 412), lower := (rows 35 259 7 104 208 32 64 128 256), losses := [] }

theorem u35533 : Upper (D 7) (R 7) [34,257,3,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35533 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35534 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 259 13 14 112 240 208 208 464), lower := (rows 35 259 13 14 112 32 64 128 256), losses := [] }

theorem u35534 : Upper (D 7) (R 7) [34,257,9,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35534 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35535 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 259 13 14 208 240 240 240 496), lower := (rows 35 259 13 14 208 32 64 128 256), losses := [] }

theorem u35535 : Upper (D 7) (R 7) [34,257,9,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35536 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 13 26 52 224 192 192 448), lower := (rows 35 259 13 26 52 32 64 128 256), losses := [] }

theorem u35536 : Upper (D 7) (R 7) [34,257,9,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35537 : Route 9 := (fun mask => (mask,id))

def c35537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35537 : Upper (D 7) (R 7) [34,257,9,18,68] 13 := by
  apply FastRouting.sound _ _ [34,257,9,18,68] 13 (by decide) (choices 1) [64,128] r35537 c35537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20671
  · exact u20672

def r35538 : Route 9 := (fun mask => (mask,id))

def c35538 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35538 : Upper (D 7) (R 7) [34,257,9,18,96] 13 := by
  apply FastRouting.sound _ _ [34,257,9,18,96] 13 (by decide) (choices 1) [4,64,128] r35538 c35538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20673
  · exact u20674
  · exact u20675

def r35539 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35539 : Upper (D 7) (R 7) [34,257,9,18,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,18,192] 13 (by decide) (choices 1) [4,64] r35539 c35539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20676
  · exact u20677

def b35540 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 13 28 50 224 192 192 448), lower := (rows 35 259 13 28 50 32 64 128 256), losses := [] }

theorem u35540 : Upper (D 7) (R 7) [34,257,9,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35540 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35541 : Route 9 := (fun mask => (mask,id))

def c35541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35541 : Upper (D 7) (R 7) [34,257,9,20,66] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,66] 13 (by decide) (choices 1) [64,128] r35541 c35541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20678
  · exact u20679

def r35542 : Route 9 := (fun mask => (mask,id))

def c35542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35542 : Upper (D 7) (R 7) [34,257,9,20,96] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,96] 13 (by decide) (choices 1) [2,64,128] r35542 c35542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20680
  · exact u20681
  · exact u20682

def r35543 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35543 : Upper (D 7) (R 7) [34,257,9,20,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,20,192] 13 (by decide) (choices 1) [2,64] r35543 c35543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20683
  · exact u20684

def b35544 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 13 42 84 240 208 208 464), lower := (rows 35 259 13 42 84 32 64 128 256), losses := [] }

theorem u35544 : Upper (D 7) (R 7) [34,257,9,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35544 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35545 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 13 42 208 244 212 212 468), lower := (rows 35 259 13 42 208 32 64 128 256), losses := [] }

theorem u35545 : Upper (D 7) (R 7) [34,257,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35545 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35546 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 259 13 44 82 240 208 208 464), lower := (rows 35 259 13 44 82 32 64 128 256), losses := [] }

theorem u35546 : Upper (D 7) (R 7) [34,257,9,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35546 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35547 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 259 13 44 208 242 210 210 466), lower := (rows 35 259 13 44 208 32 64 128 256), losses := [] }

theorem u35547 : Upper (D 7) (R 7) [34,257,9,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35547 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35548 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 259 13 56 22 224 192 192 448), lower := (rows 35 259 13 56 22 32 64 128 256), losses := [] }

theorem u35548 : Upper (D 7) (R 7) [34,257,9,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35548 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35549 : Route 9 := (fun mask => (mask,id))

def c35549 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35549 : Upper (D 7) (R 7) [34,257,9,48,66] 13 := by
  apply FastRouting.sound _ _ [34,257,9,48,66] 13 (by decide) (choices 1) [4,64,128] r35549 c35549
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20685
  · exact u20686
  · exact u20687

def b35550 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5),(3,0),(4,0),(4,5)], upper := (rows 35 259 13 56 84 226 194 194 450), lower := (rows 35 259 13 56 84 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 56 92 32 64 128 256) }] }

theorem u35550 : Upper (D 7) (R 7) [34,257,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35550 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35551 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c35551 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35551 : Upper (D 7) (R 7) [34,257,9,48,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,48,192] 13 (by decide) (choices 1) [2,4,64] r35551 c35551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20688
  · exact u20689
  · exact u20690

def r35552 : Route 9 := (fun mask => (mask,id))

def c35552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35552 : Upper (D 7) (R 7) [34,257,9,66,36] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,36] 13 (by decide) (choices 1) [16,64,128] r35552 c35552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20691
  · exact u20692
  · exact u20693

def b35553 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 13 74 84 176 240 176 432), lower := (rows 35 259 13 74 84 32 64 128 256), losses := [] }

theorem u35553 : Upper (D 7) (R 7) [34,257,9,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35553 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35554 : Route 9 := (fun mask => (mask,id))

def c35554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35554 : Upper (D 7) (R 7) [34,257,9,66,96] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,96] 13 (by decide) (choices 1) [4,16,128] r35554 c35554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20694
  · exact u20695
  · exact u20696

def r35555 : Route 9 := (fun mask => (mask,id))

def c35555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35555 : Upper (D 7) (R 7) [34,257,9,66,132] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,132] 13 (by decide) (choices 1) [16,64,128] r35555 c35555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20697
  · exact u20698
  · exact u20699

def r35556 : Route 9 := (fun mask => (mask,id))

def c35556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35556 : Upper (D 7) (R 7) [34,257,9,66,160] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,160] 13 (by decide) (choices 1) [4,16,64,128] r35556 c35556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20700
  · exact u20701
  · exact u20702
  · exact u20703

def r35557 : Route 9 := (fun mask => (mask,id))

def c35557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35557 : Upper (D 7) (R 7) [34,257,9,66,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,66,192] 13 (by decide) (choices 1) [4,16,128] r35557 c35557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20704
  · exact u20705
  · exact u20706

def b35558 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 259 13 76 50 240 208 208 464), lower := (rows 35 259 13 76 50 32 64 128 256), losses := [] }

theorem u35558 : Upper (D 7) (R 7) [34,257,9,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35558 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35559 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 259 13 76 82 176 240 176 432), lower := (rows 35 259 13 76 82 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 19 55 87 151 279), good := (rows 498 498 508 492 498 32 64 128 256) }] }

theorem u35559 : Upper (D 7) (R 7) [34,257,9,68,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35559 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35560 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 387, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 259 13 76 112 178 210 146 402), lower := (rows 35 259 13 76 112 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 92 112 32 64 128 256) }] }

theorem u35560 : Upper (D 7) (R 7) [34,257,9,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35561 : Route 9 := (fun mask => (mask,id))

def c35561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35561 : Upper (D 7) (R 7) [34,257,9,68,130] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,130] 13 (by decide) (choices 1) [16,64,128] r35561 c35561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20707
  · exact u20708
  · exact u20709

def r35562 : Route 9 := (fun mask => (mask,id))

def c35562 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35562 : Upper (D 7) (R 7) [34,257,9,68,160] 13 := by
  apply FastRouting.sound _ _ [34,257,9,68,160] 13 (by decide) (choices 1) [2,16,64,128] r35562 c35562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20710
  · exact u20711
  · exact u20712
  · exact u20713

def b35563 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 291, targets := 64 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 35 259 13 76 208 178 242 178 434), lower := (rows 35 259 13 76 208 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 35 67 131 259), good := (rows 498 498 508 92 208 32 64 128 256) }] }

theorem u35563 : Upper (D 7) (R 7) [34,257,9,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35564 : Route 9 := (fun mask => (mask,id))

def c35564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35564 : Upper (D 7) (R 7) [34,257,9,80,6] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,6] 13 (by decide) (choices 1) [64,128] r35564 c35564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u20714
  · exact u20715

def b35565 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 16, targets := 192 },{ cop := 4, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(4,6),(4,7)], upper := (rows 35 259 13 88 50 228 196 196 452), lower := (rows 35 259 13 88 50 32 64 128 256), losses := [] }

theorem u35565 : Upper (D 7) (R 7) [34,257,9,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35566 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5),(3,0),(3,5),(4,0)], upper := (rows 35 259 13 88 52 226 194 194 450), lower := (rows 35 259 13 88 52 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 35 67 131 259), good := (rows 482 482 508 88 60 32 64 128 256) },{ target := 5, region := (rows 1 7 4 24 16 0 87 151 279), good := (rows 451 451 463 472 478 0 64 128 256) }] }

theorem u35566 : Upper (D 7) (R 7) [34,257,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35566 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35567 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 13 88 82 164 228 164 420), lower := (rows 35 259 13 88 82 32 64 128 256), losses := [] }

theorem u35567 : Upper (D 7) (R 7) [34,257,9,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35567 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35568 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 13 88 84 162 226 162 418), lower := (rows 35 259 13 88 84 32 64 128 256), losses := [] }

theorem u35568 : Upper (D 7) (R 7) [34,257,9,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35568 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35569 : PairBound 9 := { available := 134, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 13 88 112 166 198 134 390), lower := (rows 35 259 13 88 112 32 64 128 256), losses := [] }

theorem u35569 : Upper (D 7) (R 7) [34,257,9,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35569 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35570 : Route 9 := (fun mask => (mask,id))

def c35570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35570 : Upper (D 7) (R 7) [34,257,9,80,130] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,130] 13 (by decide) (choices 1) [4,64,128] r35570 c35570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20716
  · exact u20717
  · exact u20718

def r35571 : Route 9 := (fun mask => (mask,id))

def c35571 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35571 : Upper (D 7) (R 7) [34,257,9,80,132] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,132] 13 (by decide) (choices 1) [2,64,128] r35571 c35571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20719
  · exact u20720
  · exact u20721

def r35572 : Route 9 := (fun mask => (mask,id))

def c35572 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u35572 : Upper (D 7) (R 7) [34,257,9,80,160] 13 := by
  apply FastRouting.sound _ _ [34,257,9,80,160] 13 (by decide) (choices 1) [2,4,64,128] r35572 c35572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20722
  · exact u20723
  · exact u20724
  · exact u20725

def b35573 : PairBound 9 := { available := 166, camps := [{ cop := 4, region := 8, targets := 163 }], pairs := [(3,0),(3,1),(3,5),(3,7)], upper := (rows 35 259 13 88 208 166 230 166 422), lower := (rows 35 259 13 88 208 32 64 128 256), losses := [] }

theorem u35573 : Upper (D 7) (R 7) [34,257,9,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35573 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35574 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 232, targets := 3 }], pairs := [(1,5),(3,0),(3,1),(4,5)], upper := (rows 35 259 13 104 22 240 208 208 464), lower := (rows 35 259 13 104 22 32 64 128 256), losses := [] }

theorem u35574 : Upper (D 7) (R 7) [34,257,9,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35574 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35575 : Route 9 := (fun mask => (mask,id))

def c35575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35575 : Upper (D 7) (R 7) [34,257,9,96,66] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,66] 13 (by decide) (choices 1) [4,16,128] r35575 c35575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u20726
  · exact u20727
  · exact u20728

def b35576 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,5),(1,6),(4,5)], upper := (rows 35 259 13 104 84 178 210 146 402), lower := (rows 35 259 13 104 84 32 64 128 256), losses := [] }

theorem u35576 : Upper (D 7) (R 7) [34,257,9,96,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35576 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r35577 : Route 9 := (fun mask => (mask,id))

def c35577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35577 : Upper (D 7) (R 7) [34,257,9,96,130] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,130] 13 (by decide) (choices 1) [4,16,64,128] r35577 c35577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20729
  · exact u20730
  · exact u20731
  · exact u20732

def r35578 : Route 9 := (fun mask => (mask,id))

def c35578 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u35578 : Upper (D 7) (R 7) [34,257,9,96,132] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,132] 13 (by decide) (choices 1) [2,16,64,128] r35578 c35578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20733
  · exact u20734
  · exact u20735
  · exact u20736

def r35579 : Route 9 := (fun mask => (mask,id))

def c35579 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u35579 : Upper (D 7) (R 7) [34,257,9,96,192] 13 := by
  apply FastRouting.sound _ _ [34,257,9,96,192] 13 (by decide) (choices 1) [2,4,16,128] r35579 c35579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u20737
  · exact u20738
  · exact u20739
  · exact u20740

#print axioms u35579
end Delivery.IrregularNine14.P07
