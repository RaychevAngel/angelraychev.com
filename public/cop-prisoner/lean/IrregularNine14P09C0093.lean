import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0036

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m5580_8 : Upper (D 9) (R 9) [96,5,130,144,257,256,8] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257,8,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2166

theorem m5580_32 : Upper (D 9) (R 9) [96,5,130,144,257,256,32] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2167

def r5580 : Route 9 := (fun mask => (mask,id))

def c5580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5580 : Upper (D 9) (R 9) [96,5,130,144,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,144,257,256] 13 (by decide) (choices 1) [8,32] r5580 c5580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5580_8
  · exact m5580_32

def b5581 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,7),(3,0),(4,0),(4,7)], upper := (rows 97 7 134 152 280 33 352 480 352), lower := (rows 97 7 134 152 280 33 64 128 256), losses := [] }

theorem u5581 : Upper (D 9) (R 9) [96,5,130,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5581 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5582 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 152 280 96 353 417 289), lower := (rows 97 7 134 152 280 96 64 128 256), losses := [] }

theorem u5582 : Upper (D 9) (R 9) [96,5,130,144,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5582 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5583 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,8)], upper := (rows 97 7 134 152 280 288 97 225 353), lower := (rows 97 7 134 152 280 288 64 128 256), losses := [] }

theorem u5583 : Upper (D 9) (R 9) [96,5,130,144,264,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5583 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5584 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 3, region := 369, targets := 128 },{ cop := 4, region := 200, targets := 32 }], pairs := [(0,7),(3,0),(3,5),(4,0),(4,7)], upper := (rows 97 7 134 152 304 33 328 456 328), lower := (rows 97 7 134 152 304 33 64 128 256), losses := [] }

theorem u5584 : Upper (D 9) (R 9) [96,5,130,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5584 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5585 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 369, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,7)], upper := (rows 97 7 134 152 304 40 321 449 321), lower := (rows 97 7 134 152 304 40 64 128 256), losses := [] }

theorem u5585 : Upper (D 9) (R 9) [96,5,130,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5585 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5586 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 152 304 96 329 393 265), lower := (rows 97 7 134 152 304 96 64 128 256), losses := [] }

theorem u5586 : Upper (D 9) (R 9) [96,5,130,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5586 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5587 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 134 152 304 288 73 201 329), lower := (rows 97 7 134 152 304 288 64 128 256), losses := [] }

theorem u5587 : Upper (D 9) (R 9) [96,5,130,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5587 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5588 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 134 168 273 40 336 464 336), lower := (rows 97 7 134 168 273 40 64 128 256), losses := [] }

theorem u5588 : Upper (D 9) (R 9) [96,5,130,160,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5588 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5589 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 337, targets := 128 },{ cop := 0, region := 392, targets := 1 }], pairs := [(0,7),(2,0),(3,0),(4,7)], upper := (rows 97 7 134 168 273 48 328 456 328), lower := (rows 97 7 134 168 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 57 16 48 123 187 315), good := (rows 488 462 454 488 504 504 64 128 256) }] }

theorem u5589 : Upper (D 9) (R 9) [96,5,130,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5589 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5590 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 168 273 96 344 408 280), lower := (rows 97 7 134 168 273 96 64 128 256), losses := [] }

theorem u5590 : Upper (D 9) (R 9) [96,5,130,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5590 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5591 : Route 9 := (fun mask => (mask,id))

def c5591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5591 : Upper (D 9) (R 9) [96,5,130,160,257,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,257,256] 13 (by decide) (choices 1) [8,16] r5591 c5591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2168
  · exact u2169

def b5592 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 3, region := 337, targets := 128 },{ cop := 3, region := 336, targets := 32 }], pairs := [(0,7),(3,0),(4,0),(4,5),(4,7)], upper := (rows 97 7 134 168 280 33 336 464 336), lower := (rows 97 7 134 168 280 33 64 128 256), losses := [] }

theorem u5592 : Upper (D 9) (R 9) [96,5,130,160,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5592 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5593 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,7)], upper := (rows 97 7 134 168 280 48 321 449 321), lower := (rows 97 7 134 168 280 48 64 128 256), losses := [] }

theorem u5593 : Upper (D 9) (R 9) [96,5,130,160,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5593 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5594 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 168 280 96 337 401 273), lower := (rows 97 7 134 168 280 96 64 128 256), losses := [] }

theorem u5594 : Upper (D 9) (R 9) [96,5,130,160,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5594 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5595 : Route 9 := (fun mask => (mask,id))

def c5595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5595 : Upper (D 9) (R 9) [96,5,130,160,264,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,264,256] 13 (by decide) (choices 1) [1,16] r5595 c5595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2170
  · exact u2171

def b5596 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 3, region := 337, targets := 128 },{ cop := 3, region := 336, targets := 32 }], pairs := [(0,7),(3,0),(4,0),(4,5),(4,7)], upper := (rows 97 7 134 168 336 33 344 408 280), lower := (rows 97 7 134 168 336 33 64 128 256), losses := [] }

theorem u5596 : Upper (D 9) (R 9) [96,5,130,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5596 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5597 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 2, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 134 168 336 40 337 401 273), lower := (rows 97 7 134 168 336 40 64 128 256), losses := [] }

theorem u5597 : Upper (D 9) (R 9) [96,5,130,160,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5597 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5598 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 134 168 336 48 329 393 265), lower := (rows 97 7 134 168 336 48 64 128 256), losses := [] }

theorem u5598 : Upper (D 9) (R 9) [96,5,130,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5598 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5599 : Route 9 := (fun mask => (mask,id))

def c5599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5599 : Upper (D 9) (R 9) [96,5,130,160,320,256] 13 := by
  apply FastRouting.sound _ _ [96,5,130,160,320,256] 13 (by decide) (choices 1) [1,8,16] r5599 c5599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2172
  · exact u2173
  · exact u2174

def b5600 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 199, targets := 256 },{ cop := 3, region := 48, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(4,6)], upper := (rows 97 7 134 265 304 40 208 208 464), lower := (rows 97 7 134 265 304 40 64 128 256), losses := [] }

theorem u5600 : Upper (D 9) (R 9) [96,5,130,257,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5600 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5601 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 134 265 304 48 200 200 456), lower := (rows 97 7 134 265 304 48 64 128 256), losses := [] }

theorem u5601 : Upper (D 9) (R 9) [96,5,130,257,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5601 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5602 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 265 304 96 216 152 408), lower := (rows 97 7 134 265 304 96 64 128 256), losses := [] }

theorem u5602 : Upper (D 9) (R 9) [96,5,130,257,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5602 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5603 : Route 9 := (fun mask => (mask,id))

def c5603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5603 : Upper (D 9) (R 9) [96,5,130,257,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257,288,128] 13 (by decide) (choices 1) [8,16] r5603 c5603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2175
  · exact u2176

def b5604 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 105, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 134 265 400 40 112 240 368), lower := (rows 97 7 134 265 400 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 59 40 105 169 297), good := (rows 496 470 150 504 400 504 64 128 256) }] }

theorem u5604 : Upper (D 9) (R 9) [96,5,130,257,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5604 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5605_8 : Upper (D 9) (R 9) [96,5,130,257,384,16,8] 13 :=
  permutation_upper _ _ _ [96,5,130,257,384,8,16] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2177

def r5605 : Route 9 := (fun mask => (mask,id))

def c5605 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5605 : Upper (D 9) (R 9) [96,5,130,257,384,16] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257,384,16] 13 (by decide) (choices 1) [8,32] r5605 c5605
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5605_8
  · exact u2178

def b5606 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 265 400 96 120 184 312), lower := (rows 97 7 134 265 400 96 64 128 256), losses := [] }

theorem u5606 : Upper (D 9) (R 9) [96,5,130,257,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5606 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5607 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 41, targets := 128 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,7),(3,0),(3,7),(4,0),(4,5)], upper := (rows 97 7 134 296 336 33 216 152 408), lower := (rows 97 7 134 296 336 33 64 128 256), losses := [] }

theorem u5607 : Upper (D 9) (R 9) [96,5,130,288,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5607 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5608 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 8, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 134 296 336 40 209 145 401), lower := (rows 97 7 134 296 336 40 64 128 256), losses := [] }

theorem u5608 : Upper (D 9) (R 9) [96,5,130,288,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5608 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5609 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 193, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 7 134 296 336 48 201 137 393), lower := (rows 97 7 134 296 336 48 64 128 256), losses := [] }

theorem u5609 : Upper (D 9) (R 9) [96,5,130,288,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5609 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5610_1 : Upper (D 9) (R 9) [96,5,130,288,320,128,1] 13 :=
  permutation_upper _ _ _ [96,5,130,288,320,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2179

theorem m5610_8 : Upper (D 9) (R 9) [96,5,130,288,320,128,8] 13 :=
  permutation_upper _ _ _ [96,5,130,288,320,16,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2181

theorem m5610_16 : Upper (D 9) (R 9) [96,5,130,288,320,128,16] 13 :=
  permutation_upper _ _ _ [96,5,130,288,320,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2180

def r5610 : Route 9 := (fun mask => (mask,id))

def c5610 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5610 : Upper (D 9) (R 9) [96,5,130,288,320,128] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288,320,128] 13 (by decide) (choices 1) [1,8,16] r5610 c5610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m5610_1
  · exact m5610_8
  · exact m5610_16

def b5611 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 105, targets := 128 },{ cop := 3, region := 208, targets := 32 }], pairs := [(0,7),(3,0),(3,7),(4,0),(4,5)], upper := (rows 97 7 134 296 400 33 88 216 344), lower := (rows 97 7 134 296 400 33 64 128 256), losses := [] }

theorem u5611 : Upper (D 9) (R 9) [96,5,130,288,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5611 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5612 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 8, region := 40, targets := 1 }], pairs := [(1,5),(2,5),(3,0),(4,5)], upper := (rows 97 7 134 296 400 40 81 209 337), lower := (rows 97 7 134 296 400 40 64 128 256), losses := [] }

theorem u5612 : Upper (D 9) (R 9) [96,5,130,288,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5612 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5613 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 199, targets := 256 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 97 7 134 296 400 48 73 201 329), lower := (rows 97 7 134 296 400 48 64 128 256), losses := [] }

theorem u5613 : Upper (D 9) (R 9) [96,5,130,288,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5613 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5614 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 296 400 96 89 153 281), lower := (rows 97 7 134 296 400 96 64 128 256), losses := [] }

theorem u5614 : Upper (D 9) (R 9) [96,5,130,288,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5614 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5615 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 25 274 96 480 416 416), lower := (rows 97 7 140 25 274 96 64 128 256), losses := [] }

theorem u5615 : Upper (D 9) (R 9) [96,5,136,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5615 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5616 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 496, targets := 1 },{ cop := 3, region := 484, targets := 1 },{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7),(2,0),(3,7),(4,0),(4,7)], upper := (rows 97 7 140 25 274 160 352 480 352), lower := (rows 97 7 140 25 274 160 64 128 256), losses := [{ target := 7, region := (rows 33 2 4 10 18 32 97 0 289), good := (rows 353 351 12 345 282 353 64 0 256) }] }

theorem u5616 : Upper (D 9) (R 9) [96,5,136,17,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5616 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5617 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 0, region := 400, targets := 1 },{ cop := 3, region := 452, targets := 1 }], pairs := [(1,5),(2,0),(2,5),(4,0)], upper := (rows 97 7 140 25 304 34 448 448 448), lower := (rows 97 7 140 25 304 34 64 128 256), losses := [] }

theorem u5617 : Upper (D 9) (R 9) [96,5,136,17,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5617 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5618 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 3, region := 390, targets := 32 }], pairs := [(1,5),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 25 304 96 450 386 386), lower := (rows 97 7 140 25 304 96 64 128 256), losses := [] }

theorem u5618 : Upper (D 9) (R 9) [96,5,136,17,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5618 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5619 : Route 9 := (fun mask => (mask,id))

def c5619 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5619 : Upper (D 9) (R 9) [96,5,136,17,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,288,128] 13 (by decide) (choices 1) [2,256] r5619 c5619
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2182
  · exact u2183

def b5620 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 140 25 304 288 194 194 450), lower := (rows 97 7 140 25 304 288 64 128 256), losses := [] }

theorem u5620 : Upper (D 9) (R 9) [96,5,136,17,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5620 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5621 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,0)], upper := (rows 97 7 140 25 400 34 352 480 352), lower := (rows 97 7 140 25 400 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 59 34 99 163 291), good := (rows 496 502 156 476 400 498 64 128 256) }] }

theorem u5621 : Upper (D 9) (R 9) [96,5,136,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5621 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5622 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 25 400 96 354 418 290), lower := (rows 97 7 140 25 400 96 64 128 256), losses := [] }

theorem u5622 : Upper (D 9) (R 9) [96,5,136,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5622 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5623_2 : Upper (D 9) (R 9) [96,5,136,17,384,256,2] 13 :=
  permutation_upper _ _ _ [96,5,136,17,384,2,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2184

theorem m5623_32 : Upper (D 9) (R 9) [96,5,136,17,384,256,32] 13 :=
  permutation_upper _ _ _ [96,5,136,17,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2185

def r5623 : Route 9 := (fun mask => (mask,id))

def c5623 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5623 : Upper (D 9) (R 9) [96,5,136,17,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17,384,256] 13 (by decide) (choices 1) [2,32] r5623 c5623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5623_2
  · exact m5623_32

def b5624 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 452, targets := 33 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,5),(4,0)], upper := (rows 97 7 140 26 176 33 320 448 320), lower := (rows 97 7 140 26 176 33 64 128 256), losses := [] }

theorem u5624 : Upper (D 9) (R 9) [96,5,136,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5624 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5625 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 176 96 321 385 257), lower := (rows 97 7 140 26 176 96 64 128 256), losses := [] }

theorem u5625 : Upper (D 9) (R 9) [96,5,136,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5625 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5626 : Route 9 := (fun mask => (mask,id))

def c5626 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5626 : Upper (D 9) (R 9) [96,5,136,18,160,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,160,256] 13 (by decide) (choices 1) [1,256] r5626 c5626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2186
  · exact u2187

def b5627 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 273 96 480 416 416), lower := (rows 97 7 140 26 273 96 64 128 256), losses := [] }

theorem u5627 : Upper (D 9) (R 9) [96,5,136,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5627 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5628_32 : Upper (D 9) (R 9) [96,5,136,18,257,128,32] 13 :=
  permutation_upper _ _ _ [96,5,136,18,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2188

def r5628 : Route 9 := (fun mask => (mask,id))

def c5628 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u5628 : Upper (D 9) (R 9) [96,5,136,18,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,257,128] 13 (by decide) (choices 1) [32,256] r5628 c5628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5628_32
  · exact u2189

def b5629 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 },{ cop := 5, region := 193, targets := 256 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 97 7 140 26 273 288 224 224 480), lower := (rows 97 7 140 26 273 288 64 128 256), losses := [{ target := 8, region := (rows 33 18 20 24 16 32 97 161 0), good := (rows 225 199 140 30 223 225 64 128 0) }] }

theorem u5629 : Upper (D 9) (R 9) [96,5,136,18,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5629 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5630 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 452, targets := 33 },{ cop := 6, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,5),(4,0)], upper := (rows 97 7 140 26 304 33 448 448 448), lower := (rows 97 7 140 26 304 33 64 128 256), losses := [] }

theorem u5630 : Upper (D 9) (R 9) [96,5,136,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5630 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5631 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 304 96 449 385 385), lower := (rows 97 7 140 26 304 96 64 128 256), losses := [] }

theorem u5631 : Upper (D 9) (R 9) [96,5,136,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5631 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5632 : Route 9 := (fun mask => (mask,id))

def c5632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5632 : Upper (D 9) (R 9) [96,5,136,18,288,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,288,128] 13 (by decide) (choices 1) [1,256] r5632 c5632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2190
  · exact u2191

def b5633 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 140 26 304 288 193 193 449), lower := (rows 97 7 140 26 304 288 64 128 256), losses := [] }

theorem u5633 : Upper (D 9) (R 9) [96,5,136,18,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5633 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5634 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 400, targets := 1 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(4,0)], upper := (rows 97 7 140 26 400 33 352 480 352), lower := (rows 97 7 140 26 400 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 51 32 97 161 289), good := (rows 496 478 140 30 400 496 64 128 256) }] }

theorem u5634 : Upper (D 9) (R 9) [96,5,136,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5634 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5635 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 26 400 96 353 417 289), lower := (rows 97 7 140 26 400 96 64 128 256), losses := [] }

theorem u5635 : Upper (D 9) (R 9) [96,5,136,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m5636_1 : Upper (D 9) (R 9) [96,5,136,18,384,256,1] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384,1,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2192

theorem m5636_32 : Upper (D 9) (R 9) [96,5,136,18,384,256,32] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2193

def r5636 : Route 9 := (fun mask => (mask,id))

def c5636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5636 : Upper (D 9) (R 9) [96,5,136,18,384,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18,384,256] 13 (by decide) (choices 1) [1,32] r5636 c5636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m5636_1
  · exact m5636_32

def b5637 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 46, targets := 320 }], pairs := [(1,6),(1,8),(2,6),(2,8)], upper := (rows 97 7 140 42 145 48 320 448 320), lower := (rows 97 7 140 42 145 48 64 128 256), losses := [] }

theorem u5637 : Upper (D 9) (R 9) [96,5,136,34,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5637 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5638 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 42 145 96 336 400 272), lower := (rows 97 7 140 42 145 96 64 128 256), losses := [] }

theorem u5638 : Upper (D 9) (R 9) [96,5,136,34,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5638 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r5639 : Route 9 := (fun mask => (mask,id))

def c5639 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u5639 : Upper (D 9) (R 9) [96,5,136,34,129,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,34,129,256] 13 (by decide) (choices 1) [16,256] r5639 c5639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2194
  · exact u2195

#print axioms u5639
end Delivery.IrregularNine14.P09
