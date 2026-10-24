import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5580 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 65 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 38 196 74 276 33 65 162 290), lower := (rows 25 38 196 74 276 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 26 32 64 130 258), good := (rows 28 438 196 478 276 32 64 128 256) }] }

theorem u5580 : Upper (D 6) (R 6) [24,36,192,66,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5580 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5581 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 38 196 74 276 33 66 161 289), lower := (rows 25 38 196 74 276 33 66 128 256), losses := [] }

theorem u5581 : Upper (D 6) (R 6) [24,36,192,66,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5582 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 196 74 276 33 96 131 259), lower := (rows 25 38 196 74 276 33 96 128 256), losses := [] }

theorem u5582 : Upper (D 6) (R 6) [24,36,192,66,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 25 38 196 74 304 33 65 134 262), lower := (rows 25 38 196 74 304 33 65 128 256), losses := [] }

theorem u5583 : Upper (D 6) (R 6) [24,36,192,66,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5583 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 25 38 196 74 304 33 66 133 261), lower := (rows 25 38 196 74 304 33 66 128 256), losses := [] }

theorem u5584 : Upper (D 6) (R 6) [24,36,192,66,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5584 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 25 38 196 74 304 33 68 131 259), lower := (rows 25 38 196 74 304 33 68 128 256), losses := [] }

theorem u5585 : Upper (D 6) (R 6) [24,36,192,66,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5585 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 196 104 274 33 65 134 262), lower := (rows 25 38 196 104 274 33 65 128 256), losses := [] }

theorem u5586 : Upper (D 6) (R 6) [24,36,192,96,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5586 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5587 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 72, targets := 5 },{ cop := 4, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,2)], upper := (rows 25 38 196 104 274 33 66 133 261), lower := (rows 25 38 196 104 274 33 66 128 256), losses := [] }

theorem u5587 : Upper (D 6) (R 6) [24,36,192,96,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5587 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5588 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 25 38 196 104 274 33 68 131 259), lower := (rows 25 38 196 104 274 33 68 128 256), losses := [] }

theorem u5588 : Upper (D 6) (R 6) [24,36,192,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5589 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 105, targets := 6 }], pairs := [(0,1),(0,2),(3,1)], upper := (rows 25 38 196 104 276 33 65 130 258), lower := (rows 25 38 196 104 276 33 65 128 256), losses := [] }

theorem u5589 : Upper (D 6) (R 6) [24,36,192,96,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5589 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5590 : Route 9 := (fun mask => (mask,id))

def c5590 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5590 : Upper (D 6) (R 6) [24,36,192,96,260,1,2] 13 := by
  apply FastRouting.sound _ _ [24,36,192,96,260,1,2] 13 (by decide) (choices 1) [1,2] r5590 c5590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u415
  · exact u416

def b5591 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 11 84 96 65 162 290), lower := (rows 25 38 388 11 84 96 65 128 256), losses := [] }

theorem u5591 : Upper (D 6) (R 6) [24,36,384,3,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5591 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5592 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 11 84 96 66 161 289), lower := (rows 25 38 388 11 84 96 66 128 256), losses := [] }

theorem u5592 : Upper (D 6) (R 6) [24,36,384,3,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5592 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5593 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 },{ cop := 3, region := 388, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 38 388 11 84 96 96 131 259), lower := (rows 25 38 388 11 84 96 96 128 256), losses := [] }

theorem u5593 : Upper (D 6) (R 6) [24,36,384,3,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 13 82 34 65 224 352), lower := (rows 25 38 388 13 82 34 65 128 256), losses := [] }

theorem u5594 : Upper (D 6) (R 6) [24,36,384,5,66,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5594 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 397, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 25 38 388 13 82 34 96 193 321), lower := (rows 25 38 388 13 82 34 96 128 256), losses := [] }

theorem u5595 : Upper (D 6) (R 6) [24,36,384,5,66,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5595 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5596 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 13 82 96 65 162 290), lower := (rows 25 38 388 13 82 96 65 128 256), losses := [] }

theorem u5596 : Upper (D 6) (R 6) [24,36,384,5,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5597 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 13 82 96 66 161 289), lower := (rows 25 38 388 13 82 96 66 128 256), losses := [] }

theorem u5597 : Upper (D 6) (R 6) [24,36,384,5,66,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5597 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 388 13 82 96 96 131 259), lower := (rows 25 38 388 13 82 96 96 128 256), losses := [] }

theorem u5598 : Upper (D 6) (R 6) [24,36,384,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5598 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 89, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 388 13 112 34 65 194 322), lower := (rows 25 38 388 13 112 34 65 128 256), losses := [] }

theorem u5599 : Upper (D 6) (R 6) [24,36,384,5,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 397, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 25 38 388 13 112 34 66 193 321), lower := (rows 25 38 388 13 112 34 66 128 256), losses := [] }

theorem u5600 : Upper (D 6) (R 6) [24,36,384,5,96,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5600 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5601 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 390, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 388 74 84 33 65 162 290), lower := (rows 25 38 388 74 84 33 65 128 256), losses := [] }

theorem u5601 : Upper (D 6) (R 6) [24,36,384,66,68,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5601 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5602 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 25 38 388 74 84 33 66 161 289), lower := (rows 25 38 388 74 84 33 66 128 256), losses := [] }

theorem u5602 : Upper (D 6) (R 6) [24,36,384,66,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5603 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 38 388 74 84 33 96 131 259), lower := (rows 25 38 388 74 84 33 96 128 256), losses := [] }

theorem u5603 : Upper (D 6) (R 6) [24,36,384,66,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5603 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5604 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 290, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 25 98 133 14 52 288 65 194 322), lower := (rows 25 98 133 14 52 288 65 128 256), losses := [] }

theorem u5604 : Upper (D 6) (R 6) [24,96,129,6,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5604 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5605 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 25 98 133 14 52 288 66 193 321), lower := (rows 25 98 133 14 52 288 66 128 256), losses := [] }

theorem u5605 : Upper (D 6) (R 6) [24,96,129,6,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5605 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5606 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 272, targets := 5 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 25 98 133 14 274 33 68 224 352), lower := (rows 25 98 133 14 274 33 68 128 256), losses := [] }

theorem u5606 : Upper (D 6) (R 6) [24,96,129,6,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 133 14 274 33 96 196 324), lower := (rows 25 98 133 14 274 33 96 128 256), losses := [] }

theorem u5607 : Upper (D 6) (R 6) [24,96,129,6,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5607 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 133 14 274 36 96 193 321), lower := (rows 25 98 133 14 274 36 96 128 256), losses := [] }

theorem u5608 : Upper (D 6) (R 6) [24,96,129,6,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5608 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 25 98 133 14 276 33 66 224 352), lower := (rows 25 98 133 14 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 34 4 8 24 32 106 162 290), good := (rows 88 482 132 478 276 482 450 128 256) }] }

theorem u5609 : Upper (D 6) (R 6) [24,96,129,6,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5609 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 133 14 276 34 96 193 321), lower := (rows 25 98 133 14 276 34 96 128 256), losses := [] }

theorem u5610 : Upper (D 6) (R 6) [24,96,129,6,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5611 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2),(2,5)], upper := (rows 25 98 133 14 304 33 66 196 324), lower := (rows 25 98 133 14 304 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 37 10 16 0 74 139 267), good := (rows 477 462 389 462 276 389 458 128 256) }] }

theorem u5611 : Upper (D 6) (R 6) [24,96,129,6,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5611 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 25 98 133 14 304 33 68 194 322), lower := (rows 25 98 133 14 304 33 68 128 256), losses := [{ target := 2, region := (rows 9 66 0 8 90 45 64 194 322), good := (rows 57 498 161 443 304 33 498 128 256) }] }

theorem u5612 : Upper (D 6) (R 6) [24,96,129,6,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5612 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(0,2),(4,0),(4,2)], upper := (rows 25 98 133 14 304 36 65 194 322), lower := (rows 25 98 133 14 304 36 65 128 256), losses := [{ target := 2, region := (rows 9 34 0 8 50 32 77 170 298), good := (rows 473 498 193 475 434 498 65 128 256) }] }

theorem u5613 : Upper (D 6) (R 6) [24,96,129,6,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 106, targets := 1 },{ cop := 4, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 25 98 133 14 304 36 66 193 321), lower := (rows 25 98 133 14 304 36 66 128 256), losses := [] }

theorem u5614 : Upper (D 6) (R 6) [24,96,129,6,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5614 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5615 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 25 98 133 44 84 33 320 130 258), lower := (rows 25 98 133 44 84 33 320 128 256), losses := [] }

theorem u5615 : Upper (D 6) (R 6) [24,96,129,36,68,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5615 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5616 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 42, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 25 98 133 44 84 34 320 131 259), lower := (rows 25 98 133 44 84 34 320 128 256), losses := [] }

theorem u5616 : Upper (D 6) (R 6) [24,96,129,36,68,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5616 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r5617 : Route 9 := (fun mask => (mask,id))

def c5617 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5617 : Upper (D 6) (R 6) [24,96,129,36,260,2,1] 13 := by
  apply FastRouting.sound _ _ [24,96,129,36,260,2,1] 13 (by decide) (choices 1) [2,64] r5617 c5617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u417
  · exact u418

def b5618 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 25 98 133 44 276 34 66 193 321), lower := (rows 25 98 133 44 276 34 66 128 256), losses := [] }

theorem u5618 : Upper (D 6) (R 6) [24,96,129,36,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5618 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 25 98 134 11 52 288 65 196 324), lower := (rows 25 98 134 11 52 288 65 128 256), losses := [] }

theorem u5619 : Upper (D 6) (R 6) [24,96,130,3,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5619 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 196, targets := 32 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(2,5)], upper := (rows 25 98 134 11 52 288 68 193 321), lower := (rows 25 98 134 11 52 288 68 128 256), losses := [] }

theorem u5620 : Upper (D 6) (R 6) [24,96,130,3,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5620 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 11 273 36 68 224 352), lower := (rows 25 98 134 11 273 36 68 128 256), losses := [] }

theorem u5621 : Upper (D 6) (R 6) [24,96,130,3,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5621 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 134 11 273 36 96 196 324), lower := (rows 25 98 134 11 273 36 96 128 256), losses := [] }

theorem u5622 : Upper (D 6) (R 6) [24,96,130,3,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5622 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 11 276 33 68 224 352), lower := (rows 25 98 134 11 276 33 68 128 256), losses := [] }

theorem u5623 : Upper (D 6) (R 6) [24,96,130,3,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5623 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5624 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 134 11 276 36 96 193 321), lower := (rows 25 98 134 11 276 36 96 128 256), losses := [] }

theorem u5624 : Upper (D 6) (R 6) [24,96,130,3,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5624 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 25 98 134 11 304 36 65 196 324), lower := (rows 25 98 134 11 304 36 65 128 256), losses := [] }

theorem u5625 : Upper (D 6) (R 6) [24,96,130,3,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5625 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 11 304 36 68 193 321), lower := (rows 25 98 134 11 304 36 68 128 256), losses := [] }

theorem u5626 : Upper (D 6) (R 6) [24,96,130,3,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5626 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 470, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 13 274 33 68 224 352), lower := (rows 25 98 134 13 274 33 68 128 256), losses := [] }

theorem u5627 : Upper (D 6) (R 6) [24,96,130,5,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5627 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 98 134 13 274 36 96 193 321), lower := (rows 25 98 134 13 274 36 96 128 256), losses := [] }

theorem u5628 : Upper (D 6) (R 6) [24,96,130,5,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5628 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 13 304 34 65 196 324), lower := (rows 25 98 134 13 304 34 65 128 256), losses := [] }

theorem u5629 : Upper (D 6) (R 6) [24,96,130,5,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5629 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 34, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 134 13 304 34 68 193 321), lower := (rows 25 98 134 13 304 34 68 128 256), losses := [] }

theorem u5630 : Upper (D 6) (R 6) [24,96,130,5,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5630 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 13 304 36 65 194 322), lower := (rows 25 98 134 13 304 36 65 128 256), losses := [] }

theorem u5631 : Upper (D 6) (R 6) [24,96,130,5,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5631 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 134 13 304 36 66 193 321), lower := (rows 25 98 134 13 304 36 66 128 256), losses := [] }

theorem u5632 : Upper (D 6) (R 6) [24,96,130,5,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5632 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 98 134 41 84 288 65 134 262), lower := (rows 25 98 134 41 84 288 65 128 256), losses := [] }

theorem u5633 : Upper (D 6) (R 6) [24,96,130,33,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5633 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5634 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 297, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 25 98 134 41 84 288 66 133 261), lower := (rows 25 98 134 41 84 288 66 128 256), losses := [] }

theorem u5634 : Upper (D 6) (R 6) [24,96,130,33,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5634 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5635 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 25 98 134 41 84 288 68 131 259), lower := (rows 25 98 134 41 84 288 68 128 256), losses := [] }

theorem u5635 : Upper (D 6) (R 6) [24,96,130,33,68,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5635 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5636 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 41 274 36 65 196 324), lower := (rows 25 98 134 41 274 36 65 128 256), losses := [] }

theorem u5636 : Upper (D 6) (R 6) [24,96,130,33,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5636 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5637 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 25 98 134 41 274 36 68 193 321), lower := (rows 25 98 134 41 274 36 68 128 256), losses := [] }

theorem u5637 : Upper (D 6) (R 6) [24,96,130,33,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5637 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5638 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 98 134 41 336 36 65 134 262), lower := (rows 25 98 134 41 336 36 65 128 256), losses := [] }

theorem u5638 : Upper (D 6) (R 6) [24,96,130,33,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5638 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b5639 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 25 98 134 41 336 36 66 133 261), lower := (rows 25 98 134 41 336 36 66 128 256), losses := [] }

theorem u5639 : Upper (D 6) (R 6) [24,96,130,33,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b5639 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P06
