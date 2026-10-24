import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5580 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 13 76 176 288 80 131 259), lower := (rows 35 194 13 76 176 288 80 128 256), losses := [] }

theorem u5580 : Upper (D 7) (R 7) [34,192,9,68,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5580 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5581 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 13 88 145 288 66 164 292), lower := (rows 35 194 13 88 145 288 66 128 256), losses := [] }

theorem u5581 : Upper (D 7) (R 7) [34,192,9,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5581 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5582 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 194 13 88 145 288 68 162 290), lower := (rows 35 194 13 88 145 288 68 128 256), losses := [] }

theorem u5582 : Upper (D 7) (R 7) [34,192,9,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5582 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,1),(3,0)], upper := (rows 35 194 13 88 145 288 96 134 262), lower := (rows 35 194 13 88 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 22 4 24 16 292 357 132 260), good := (rows 98 194 494 90 218 352 96 128 352) },{ target := 1, region := (rows 1 0 20 24 16 288 353 128 256), good := (rows 97 192 77 92 221 352 96 128 352) }] }

theorem u5583 : Upper (D 7) (R 7) [34,192,9,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5583 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 386, targets := 33 },{ cop := 0, region := 400, targets := 1 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 88 176 36 65 386 258), lower := (rows 35 194 13 88 176 36 65 128 256), losses := [] }

theorem u5584 : Upper (D 7) (R 7) [34,192,9,80,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5584 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 13 88 176 36 66 385 257), lower := (rows 35 194 13 88 176 36 66 128 256), losses := [] }

theorem u5585 : Upper (D 7) (R 7) [34,192,9,80,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5585 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,5),(4,6)], upper := (rows 35 194 13 88 176 36 320 131 259), lower := (rows 35 194 13 88 176 36 320 128 256), losses := [] }

theorem u5586 : Upper (D 7) (R 7) [34,192,9,80,160,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5586 [(5,2),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5587 : Route 9 := (fun mask => (mask,id))

def c5587 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5587 : Upper (D 7) (R 7) [34,192,9,80,160,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160,256,1] 13 (by decide) (choices 1) [2,4] r5587 c5587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u420
  · exact u421

def b5588 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 13 88 176 288 66 133 261), lower := (rows 35 194 13 88 176 288 66 128 256), losses := [] }

theorem u5588 : Upper (D 7) (R 7) [34,192,9,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5588 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5589 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 13 88 176 288 68 131 259), lower := (rows 35 194 13 88 176 288 68 128 256), losses := [] }

theorem u5589 : Upper (D 7) (R 7) [34,192,9,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5589 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 88 274 36 65 160 416), lower := (rows 35 194 13 88 274 36 65 128 256), losses := [] }

theorem u5590 : Upper (D 7) (R 7) [34,192,9,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5590 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5591 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 88 274 36 96 129 385), lower := (rows 35 194 13 88 274 36 96 128 256), losses := [] }

theorem u5591 : Upper (D 7) (R 7) [34,192,9,80,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5591 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5592 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 88 274 36 192 161 289), lower := (rows 35 194 13 88 274 36 192 128 256), losses := [] }

theorem u5592 : Upper (D 7) (R 7) [34,192,9,80,258,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5592 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5593 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 130, targets := 33 },{ cop := 0, region := 400, targets := 1 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 88 304 36 65 130 386), lower := (rows 35 194 13 88 304 36 65 128 256), losses := [] }

theorem u5593 : Upper (D 7) (R 7) [34,192,9,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5593 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 35 194 13 88 304 36 66 129 385), lower := (rows 35 194 13 88 304 36 66 128 256), losses := [] }

theorem u5594 : Upper (D 7) (R 7) [34,192,9,80,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5594 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5595 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 88 304 36 192 131 259), lower := (rows 35 194 13 88 304 36 192 128 256), losses := [] }

theorem u5595 : Upper (D 7) (R 7) [34,192,9,80,288,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5595 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5596 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 88 400 33 66 164 292), lower := (rows 35 194 13 88 400 33 66 128 256), losses := [] }

theorem u5596 : Upper (D 7) (R 7) [34,192,9,80,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5597 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,6),(4,0),(4,6)], upper := (rows 35 194 13 88 400 33 68 162 290), lower := (rows 35 194 13 88 400 33 68 128 256), losses := [] }

theorem u5597 : Upper (D 7) (R 7) [34,192,9,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5597 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 88 400 33 96 134 262), lower := (rows 35 194 13 88 400 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 132 260), good := (rows 98 194 478 88 400 96 96 128 256) }] }

theorem u5598 : Upper (D 7) (R 7) [34,192,9,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5599 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 35 194 13 88 400 36 65 162 290), lower := (rows 35 194 13 88 400 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 74 85 36 64 129 257), good := (rows 442 218 444 90 400 52 474 128 256) }] }

theorem u5599 : Upper (D 7) (R 7) [34,192,9,80,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5599 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5600 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 13 88 400 36 66 161 289), lower := (rows 35 194 13 88 400 36 66 128 256), losses := [] }

theorem u5600 : Upper (D 7) (R 7) [34,192,9,80,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5600 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5601 : Route 9 := (fun mask => (mask,id))

def c5601 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5601 : Upper (D 7) (R 7) [34,192,9,80,384,4,32] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,4,32] 13 (by decide) (choices 1) [1,2] r5601 c5601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u422
  · exact u423

def b5602 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(2,7),(3,7),(4,1)], upper := (rows 35 194 13 104 145 288 66 148 276), lower := (rows 35 194 13 104 145 288 66 128 256), losses := [] }

theorem u5602 : Upper (D 7) (R 7) [34,192,9,96,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5602 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5603 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 194 13 104 145 288 68 146 274), lower := (rows 35 194 13 104 145 288 68 128 256), losses := [] }

theorem u5603 : Upper (D 7) (R 7) [34,192,9,96,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5603 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5604 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 13 104 145 288 80 134 262), lower := (rows 35 194 13 104 145 288 80 128 256), losses := [] }

theorem u5604 : Upper (D 7) (R 7) [34,192,9,96,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5604 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5605 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 194 13 104 148 288 65 146 274), lower := (rows 35 194 13 104 148 288 65 128 256), losses := [] }

theorem u5605 : Upper (D 7) (R 7) [34,192,9,96,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5605 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5606 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 2, region := 144, targets := 2 }], pairs := [(2,7),(3,7),(4,1)], upper := (rows 35 194 13 104 148 288 66 145 273), lower := (rows 35 194 13 104 148 288 66 128 256), losses := [] }

theorem u5606 : Upper (D 7) (R 7) [34,192,9,96,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5606 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 13 104 148 288 80 131 259), lower := (rows 35 194 13 104 148 288 80 128 256), losses := [] }

theorem u5607 : Upper (D 7) (R 7) [34,192,9,96,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5607 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 13 280 112 36 65 130 386), lower := (rows 35 194 13 280 112 36 65 128 256), losses := [] }

theorem u5608 : Upper (D 7) (R 7) [34,192,9,272,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5608 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 129, camps := [{ cop := 7, region := 66, targets := 33 },{ cop := 0, region := 80, targets := 1 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 280 112 36 66 129 385), lower := (rows 35 194 13 280 112 36 66 128 256), losses := [] }

theorem u5609 : Upper (D 7) (R 7) [34,192,9,272,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5609 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5610 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 280 112 36 192 131 259), lower := (rows 35 194 13 280 112 36 192 128 256), losses := [] }

theorem u5610 : Upper (D 7) (R 7) [34,192,9,272,96,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5610 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5611 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0)], upper := (rows 35 194 13 328 22 33 80 160 416), lower := (rows 35 194 13 328 22 33 80 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 84 161 289), good := (rows 418 194 478 328 94 416 80 128 256) }] }

theorem u5611 : Upper (D 7) (R 7) [34,192,9,320,6,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5611 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 328 22 33 96 144 400), lower := (rows 35 194 13 328 22 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 148 276), good := (rows 98 194 478 328 414 96 96 128 256) }] }

theorem u5612 : Upper (D 7) (R 7) [34,192,9,320,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 22 33 192 176 304), lower := (rows 35 194 13 328 22 33 192 128 256), losses := [] }

theorem u5613 : Upper (D 7) (R 7) [34,192,9,320,6,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5613 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 35 194 13 328 145 36 66 176 304), lower := (rows 35 194 13 328 145 36 66 128 256), losses := [] }

theorem u5614 : Upper (D 7) (R 7) [34,192,9,320,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5614 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5615 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 13 328 145 36 80 162 290), lower := (rows 35 194 13 328 145 36 80 128 256), losses := [] }

theorem u5615 : Upper (D 7) (R 7) [34,192,9,320,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5615 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5616 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 144, targets := 96 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 35 194 13 328 145 36 96 146 274), lower := (rows 35 194 13 328 145 36 96 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 36 101 144 272), good := (rows 98 194 108 328 474 100 96 128 256) }] }

theorem u5616 : Upper (D 7) (R 7) [34,192,9,320,129,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5616 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 176, targets := 66 },{ cop := 4, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 35 194 13 328 148 33 66 176 304), lower := (rows 35 194 13 328 148 33 66 128 256), losses := [] }

theorem u5617 : Upper (D 7) (R 7) [34,192,9,320,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 328 148 33 80 162 290), lower := (rows 35 194 13 328 148 33 80 128 256), losses := [] }

theorem u5618 : Upper (D 7) (R 7) [34,192,9,320,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5618 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5619 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 328 148 33 96 146 274), lower := (rows 35 194 13 328 148 33 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 20 32 97 148 276), good := (rows 98 194 478 328 414 96 96 128 256) }] }

theorem u5619 : Upper (D 7) (R 7) [34,192,9,320,132,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5619 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5620 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 13 328 176 33 66 148 276), lower := (rows 35 194 13 328 176 33 66 128 256), losses := [] }

theorem u5620 : Upper (D 7) (R 7) [34,192,9,320,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 0, region := 144, targets := 1 }], pairs := [(0,6),(4,0),(4,6)], upper := (rows 35 194 13 328 176 33 68 146 274), lower := (rows 35 194 13 328 176 33 68 128 256), losses := [] }

theorem u5621 : Upper (D 7) (R 7) [34,192,9,320,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5621 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 328 176 33 80 134 262), lower := (rows 35 194 13 328 176 33 80 128 256), losses := [] }

theorem u5622 : Upper (D 7) (R 7) [34,192,9,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5622 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5623 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 144, targets := 1 },{ cop := 0, region := 144, targets := 64 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 35 194 13 328 176 36 65 146 274), lower := (rows 35 194 13 328 176 36 65 128 256), losses := [{ target := 0, region := (rows 0 74 4 74 53 36 64 197 325), good := (rows 442 458 446 458 176 436 474 128 256) }] }

theorem u5623 : Upper (D 7) (R 7) [34,192,9,320,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5623 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5624 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 35 194 13 328 176 36 66 145 273), lower := (rows 35 194 13 328 176 36 66 128 256), losses := [] }

theorem u5624 : Upper (D 7) (R 7) [34,192,9,320,160,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5624 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 13 328 176 36 80 131 259), lower := (rows 35 194 13 328 176 36 80 128 256), losses := [] }

theorem u5625 : Upper (D 7) (R 7) [34,192,9,320,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5625 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5626 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 194 14 28 81 288 65 160 416), lower := (rows 35 194 14 28 81 288 65 128 256), losses := [] }

theorem u5626 : Upper (D 7) (R 7) [34,192,10,20,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5626 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5627 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 194 14 28 81 288 96 129 385), lower := (rows 35 194 14 28 81 288 96 128 256), losses := [] }

theorem u5627 : Upper (D 7) (R 7) [34,192,10,20,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5627 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5628 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 28 81 288 192 161 289), lower := (rows 35 194 14 28 81 288 192 128 256), losses := [] }

theorem u5628 : Upper (D 7) (R 7) [34,192,10,20,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5628 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5629 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 194 14 28 336 33 65 160 416), lower := (rows 35 194 14 28 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 87 90 80 32 64 161 289), good := (rows 430 222 14 28 350 420 478 128 256) }] }

theorem u5629 : Upper (D 7) (R 7) [34,192,10,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 464, targets := 2 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 194 14 28 336 33 96 129 385), lower := (rows 35 194 14 28 336 33 96 128 256), losses := [{ target := 5, region := (rows 1 66 87 90 80 0 64 161 289), good := (rows 399 222 14 28 350 389 478 128 256) }] }

theorem u5630 : Upper (D 7) (R 7) [34,192,10,20,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 28 336 33 192 161 289), lower := (rows 35 194 14 28 336 33 192 128 256), losses := [] }

theorem u5631 : Upper (D 7) (R 7) [34,192,10,20,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5632 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 81 288 65 132 388), lower := (rows 35 194 14 56 81 288 65 128 256), losses := [] }

theorem u5632 : Upper (D 7) (R 7) [34,192,10,48,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5632 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5633 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 14 56 81 288 68 129 385), lower := (rows 35 194 14 56 81 288 68 128 256), losses := [] }

theorem u5633 : Upper (D 7) (R 7) [34,192,10,48,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5633 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5634 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 56 81 288 192 133 261), lower := (rows 35 194 14 56 81 288 192 128 256), losses := [] }

theorem u5634 : Upper (D 7) (R 7) [34,192,10,48,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5634 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5635 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(2,0)], upper := (rows 35 194 14 56 336 33 65 132 388), lower := (rows 35 194 14 56 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 77 9 82 32 64 255 383), good := (rows 446 470 414 446 470 428 478 128 256) }] }

theorem u5635 : Upper (D 7) (R 7) [34,192,10,48,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5636 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,5)], upper := (rows 35 194 14 56 336 33 68 129 385), lower := (rows 35 194 14 56 336 33 68 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 76 161 289), good := (rows 387 194 94 478 336 385 68 128 256) }] }

theorem u5636 : Upper (D 7) (R 7) [34,192,10,48,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5636 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5637 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 336 33 192 133 261), lower := (rows 35 194 14 56 336 33 192 128 256), losses := [] }

theorem u5637 : Upper (D 7) (R 7) [34,192,10,48,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5638 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 194 14 73 52 288 65 144 400), lower := (rows 35 194 14 73 52 288 65 128 256), losses := [] }

theorem u5638 : Upper (D 7) (R 7) [34,192,10,65,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5638 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5639 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 14 73 52 288 80 129 385), lower := (rows 35 194 14 73 52 288 80 128 256), losses := [] }

theorem u5639 : Upper (D 7) (R 7) [34,192,10,65,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5639 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5639
end Delivery.IrregularNine14.P07
