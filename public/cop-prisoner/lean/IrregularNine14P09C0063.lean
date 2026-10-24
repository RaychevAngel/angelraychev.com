import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0013
import IrregularNine14P09C0014

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3780 : Route 9 := (fun mask => (mask,id))

def c3780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3780 : Upper (D 9) (R 9) [34,12,65,129,320,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,129,320,256] 13 (by decide) (choices 1) [16,32,128] r3780 c3780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u823
  · exact u824
  · exact u825

def b3781 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 384 },{ cop := 2, region := 48, targets := 128 }], pairs := [(0,7),(0,8),(3,0),(4,0),(4,7)], upper := (rows 35 14 69 152 112 33 448 384 384), lower := (rows 35 14 69 152 112 33 64 128 256), losses := [] }

theorem u3781 : Upper (D 9) (R 9) [34,12,65,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 324, targets := 32 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(2,5),(2,7),(4,7)], upper := (rows 35 14 69 152 112 160 321 385 257), lower := (rows 35 14 69 152 112 160 64 128 256), losses := [{ target := 8, region := (rows 3 2 4 8 16 168 64 128 0), good := (rows 35 47 69 184 112 160 64 160 0) }] }

theorem u3782 : Upper (D 9) (R 9) [34,12,65,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3783 : Route 9 := (fun mask => (mask,id))

def c3783 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3783 : Upper (D 9) (R 9) [34,12,65,144,96,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,96,256] 13 (by decide) (choices 1) [1,128,256] r3783 c3783
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u826
  · exact u827
  · exact u828

def b3784 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,7),(1,6),(3,0),(3,6),(4,6)], upper := (rows 35 14 69 152 273 96 480 416 416), lower := (rows 35 14 69 152 273 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 29 21 32 0 161 289), good := (rows 443 30 415 152 409 416 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 47 101 24 273 96 96 0 256) }] }

theorem u3784 : Upper (D 9) (R 9) [34,12,65,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,6),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 69 152 273 160 352 480 352), lower := (rows 35 14 69 152 273 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 168 0 128 256), good := (rows 35 47 5 184 273 160 0 160 256) },{ target := 7, region := (rows 1 10 21 8 21 32 97 0 289), good := (rows 375 30 341 30 341 352 64 0 256) }] }

theorem u3785 : Upper (D 9) (R 9) [34,12,65,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3786 : Route 9 := (fun mask => (mask,id))

def c3786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3786 : Upper (D 9) (R 9) [34,12,65,144,257,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,257,256] 13 (by decide) (choices 1) [32,128] r3786 c3786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u829
  · exact u830

def b3787 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 152 304 33 448 448 448), lower := (rows 35 14 69 152 304 33 64 128 256), losses := [] }

theorem u3787 : Upper (D 9) (R 9) [34,12,65,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3787 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(0,7),(1,6),(2,5),(3,6),(4,6)], upper := (rows 35 14 69 152 304 96 449 385 385), lower := (rows 35 14 69 152 304 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 13 17 32 0 133 261), good := (rows 443 398 415 152 304 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 47 101 24 304 96 96 0 256) }] }

theorem u3788 : Upper (D 9) (R 9) [34,12,65,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3788 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(0,8),(2,5),(2,7),(4,7)], upper := (rows 35 14 69 152 304 160 321 449 321), lower := (rows 35 14 69 152 304 160 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 168 0 128 256), good := (rows 35 47 5 184 304 160 0 160 256) },{ target := 8, region := (rows 3 2 4 8 16 168 64 128 0), good := (rows 35 47 69 184 48 160 64 160 0) }] }

theorem u3789 : Upper (D 9) (R 9) [34,12,65,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3789 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3790 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 69 152 304 288 193 193 449), lower := (rows 35 14 69 152 304 288 64 128 256), losses := [] }

theorem u3790 : Upper (D 9) (R 9) [34,12,65,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3790 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 472, targets := 1 },{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 152 336 33 480 416 416), lower := (rows 35 14 69 152 336 33 64 128 256), losses := [] }

theorem u3791 : Upper (D 9) (R 9) [34,12,65,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3791 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3792 : Route 9 := (fun mask => (mask,id))

def c3792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3792 : Upper (D 9) (R 9) [34,12,65,144,320,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,320,128] 13 (by decide) (choices 1) [1,32,256] r3792 c3792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u831
  · exact u832
  · exact u833

def r3793 : Route 9 := (fun mask => (mask,id))

def c3793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3793 : Upper (D 9) (R 9) [34,12,65,144,320,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,320,256] 13 (by decide) (choices 1) [1,32,128] r3793 c3793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u834
  · exact u835
  · exact u836

def b3794 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(2,7)], upper := (rows 35 14 69 168 145 48 320 448 320), lower := (rows 35 14 69 168 145 48 64 128 256), losses := [] }

theorem u3794 : Upper (D 9) (R 9) [34,12,65,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3794 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3795 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 360, targets := 1 }], pairs := [(2,5),(3,0),(3,6),(4,5),(4,6)], upper := (rows 35 14 69 168 145 96 336 400 272), lower := (rows 35 14 69 168 145 96 64 128 256), losses := [] }

theorem u3795 : Upper (D 9) (R 9) [34,12,65,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3795 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3796 : Route 9 := (fun mask => (mask,id))

def c3796 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3796 : Upper (D 9) (R 9) [34,12,65,160,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,129,256] 13 (by decide) (choices 1) [16,256] r3796 c3796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u837
  · exact u838

def b3797 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,8)], upper := (rows 35 14 69 168 208 33 336 400 272), lower := (rows 35 14 69 168 208 33 64 128 256), losses := [] }

theorem u3797 : Upper (D 9) (R 9) [34,12,65,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3797 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3798 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 168 208 48 321 385 257), lower := (rows 35 14 69 168 208 48 64 128 256), losses := [] }

theorem u3798 : Upper (D 9) (R 9) [34,12,65,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3798 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3799 : Route 9 := (fun mask => (mask,id))

def c3799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3799 : Upper (D 9) (R 9) [34,12,65,160,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,192,256] 13 (by decide) (choices 1) [1,16,256] r3799 c3799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u839
  · exact u840
  · exact u841

def b3800 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 456, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(4,5)], upper := (rows 35 14 69 168 273 48 448 448 448), lower := (rows 35 14 69 168 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 57 16 48 511 511 511), good := (rows 490 462 462 488 504 504 448 448 448) }] }

theorem u3800 : Upper (D 9) (R 9) [34,12,65,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3800 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 232, targets := 1 }], pairs := [(2,5),(3,0),(3,6),(4,5),(4,6)], upper := (rows 35 14 69 168 273 96 464 400 400), lower := (rows 35 14 69 168 273 96 64 128 256), losses := [] }

theorem u3801 : Upper (D 9) (R 9) [34,12,65,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 69 168 273 160 336 464 336), lower := (rows 35 14 69 168 273 160 64 128 256), losses := [] }

theorem u3802 : Upper (D 9) (R 9) [34,12,65,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3802 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3803 : Route 9 := (fun mask => (mask,id))

def c3803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3803 : Upper (D 9) (R 9) [34,12,65,160,257,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,257,256] 13 (by decide) (choices 1) [16,128] r3803 c3803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u842
  · exact u843

def b3804 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 168 336 33 464 400 400), lower := (rows 35 14 69 168 336 33 64 128 256), losses := [] }

theorem u3804 : Upper (D 9) (R 9) [34,12,65,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3804 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3805 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5)], upper := (rows 35 14 69 168 336 48 449 385 385), lower := (rows 35 14 69 168 336 48 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 9 16 48 0 133 261), good := (rows 427 398 399 168 304 48 0 128 256) }] }

theorem u3805 : Upper (D 9) (R 9) [34,12,65,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3805 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3806 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 69 168 336 160 337 401 273), lower := (rows 35 14 69 168 336 160 64 128 256), losses := [] }

theorem u3806 : Upper (D 9) (R 9) [34,12,65,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3806 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3807 : Route 9 := (fun mask => (mask,id))

def c3807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3807 : Upper (D 9) (R 9) [34,12,65,160,320,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,320,256] 13 (by decide) (choices 1) [1,16,128] r3807 c3807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u844
  · exact u845
  · exact u846

def b3808 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 168 400 33 336 464 336), lower := (rows 35 14 69 168 400 33 64 128 256), losses := [] }

theorem u3808 : Upper (D 9) (R 9) [34,12,65,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3808 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 14 69 168 400 48 321 449 321), lower := (rows 35 14 69 168 400 48 64 128 256), losses := [] }

theorem u3809 : Upper (D 9) (R 9) [34,12,65,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3809 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 408, targets := 64 }], pairs := [(1,6),(2,5),(3,6),(4,5),(4,6)], upper := (rows 35 14 69 168 400 96 337 401 273), lower := (rows 35 14 69 168 400 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 9 23 32 0 133 261), good := (rows 443 414 415 168 400 32 0 128 256) }] }

theorem u3810 : Upper (D 9) (R 9) [34,12,65,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3810 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3811 : Route 9 := (fun mask => (mask,id))

def c3811 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3811 : Upper (D 9) (R 9) [34,12,65,160,384,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,160,384,256] 13 (by decide) (choices 1) [1,16] r3811 c3811
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u847
  · exact u848

def b3812 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 200 145 48 352 416 288), lower := (rows 35 14 69 200 145 48 64 128 256), losses := [] }

theorem u3812 : Upper (D 9) (R 9) [34,12,65,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3812 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3813 : Route 9 := (fun mask => (mask,id))

def c3813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u3813 : Upper (D 9) (R 9) [34,12,65,192,129,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,129,256] 13 (by decide) (choices 1) [16,32,256] r3813 c3813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u849
  · exact u850
  · exact u851

def b3814 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 3, region := 39, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 200 176 33 336 400 272), lower := (rows 35 14 69 200 176 33 64 128 256), losses := [] }

theorem u3814 : Upper (D 9) (R 9) [34,12,65,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 55, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 200 176 48 321 385 257), lower := (rows 35 14 69 200 176 48 64 128 256), losses := [] }

theorem u3815 : Upper (D 9) (R 9) [34,12,65,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3815 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3816 : Route 9 := (fun mask => (mask,id))

def c3816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3816 : Upper (D 9) (R 9) [34,12,65,192,160,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,160,256] 13 (by decide) (choices 1) [1,16,256] r3816 c3816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u852
  · exact u853
  · exact u854

def b3817 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 14 69 200 273 48 480 416 416), lower := (rows 35 14 69 200 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 61 16 48 113 177 305), good := (rows 490 14 462 200 504 504 64 128 256) }] }

theorem u3817 : Upper (D 9) (R 9) [34,12,65,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3817 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(2,8),(4,7)], upper := (rows 35 14 69 200 273 160 368 432 304), lower := (rows 35 14 69 200 273 160 64 128 256), losses := [] }

theorem u3818 : Upper (D 9) (R 9) [34,12,65,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3818 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3819 : Route 9 := (fun mask => (mask,id))

def c3819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3819 : Upper (D 9) (R 9) [34,12,65,192,257,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,257,256] 13 (by decide) (choices 1) [16,32,128] r3819 c3819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u855
  · exact u856
  · exact u857

def b3820 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 200 304 33 464 400 400), lower := (rows 35 14 69 200 304 33 64 128 256), losses := [] }

theorem u3820 : Upper (D 9) (R 9) [34,12,65,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3820 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 8, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 14 69 200 304 48 449 385 385), lower := (rows 35 14 69 200 304 48 64 128 256), losses := [] }

theorem u3821 : Upper (D 9) (R 9) [34,12,65,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3821 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 39, targets := 256 },{ cop := 0, region := 340, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(2,8),(4,7)], upper := (rows 35 14 69 200 304 160 337 401 273), lower := (rows 35 14 69 200 304 160 64 128 256), losses := [] }

theorem u3822 : Upper (D 9) (R 9) [34,12,65,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3822 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 69 200 304 288 209 145 401), lower := (rows 35 14 69 200 304 288 64 128 256), losses := [] }

theorem u3823 : Upper (D 9) (R 9) [34,12,65,192,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3823 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 39, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 200 400 33 368 432 304), lower := (rows 35 14 69 200 400 33 64 128 256), losses := [] }

theorem u3824 : Upper (D 9) (R 9) [34,12,65,192,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3824 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3825 : Route 9 := (fun mask => (mask,id))

def c3825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3825 : Upper (D 9) (R 9) [34,12,65,192,384,16] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,384,16] 13 (by decide) (choices 1) [1,32,256] r3825 c3825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u858
  · exact u859
  · exact u860

def r3826 : Route 9 := (fun mask => (mask,id))

def c3826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3826 : Upper (D 9) (R 9) [34,12,65,192,384,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,192,384,256] 13 (by decide) (choices 1) [1,16,32] r3826 c3826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u861
  · exact u862
  · exact u863

def b3827 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 392 112 33 464 400 400), lower := (rows 35 14 69 392 112 33 64 128 256), losses := [] }

theorem u3827 : Upper (D 9) (R 9) [34,12,65,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3827 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3828 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 2, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 14 69 392 112 48 449 385 385), lower := (rows 35 14 69 392 112 48 64 128 256), losses := [] }

theorem u3828 : Upper (D 9) (R 9) [34,12,65,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3828 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3829 : Route 9 := (fun mask => (mask,id))

def c3829 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3829 : Upper (D 9) (R 9) [34,12,65,384,96,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,96,128] 13 (by decide) (choices 1) [1,16,256] r3829 c3829
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u864
  · exact u865
  · exact u866

def r3830 : Route 9 := (fun mask => (mask,id))

def c3830 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3830 : Upper (D 9) (R 9) [34,12,65,384,129,16] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,129,16] 13 (by decide) (choices 1) [32,256] r3830 c3830
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u867
  · exact u868

def b3831 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 4, region := 360, targets := 1 },{ cop := 4, region := 356, targets := 128 }], pairs := [(1,6),(2,7),(3,0),(3,6),(4,6)], upper := (rows 35 14 69 392 145 96 368 432 304), lower := (rows 35 14 69 392 145 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 29 21 32 0 129 257), good := (rows 443 30 415 392 409 32 0 128 256) }] }

theorem u3831 : Upper (D 9) (R 9) [34,12,65,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3831 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 4, region := 360, targets := 1 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(2,7),(2,8),(3,0),(4,8)], upper := (rows 35 14 69 392 145 288 112 240 368), lower := (rows 35 14 69 392 145 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 296 0 128 256), good := (rows 35 47 5 424 145 288 0 128 288) }] }

theorem u3832 : Upper (D 9) (R 9) [34,12,65,384,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 392 176 33 336 464 336), lower := (rows 35 14 69 392 176 33 64 128 256), losses := [] }

theorem u3833 : Upper (D 9) (R 9) [34,12,65,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3833 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3834 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 462, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 35 14 69 392 176 48 321 449 321), lower := (rows 35 14 69 392 176 48 64 128 256), losses := [] }

theorem u3834 : Upper (D 9) (R 9) [34,12,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3834 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3835 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(0,7),(0,8),(1,6),(3,6),(4,6)], upper := (rows 35 14 69 392 176 96 337 401 273), lower := (rows 35 14 69 392 176 96 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 15 17 32 0 133 261), good := (rows 443 398 415 392 176 32 0 128 256) },{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 47 101 264 48 96 96 0 256) },{ target := 8, region := (rows 3 2 4 8 16 100 64 128 0), good := (rows 35 47 101 136 176 96 96 128 0) }] }

theorem u3835 : Upper (D 9) (R 9) [34,12,65,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3835 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3836 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 256 },{ cop := 3, region := 48, targets := 65 }], pairs := [(0,6),(2,8),(4,0),(4,6),(4,8)], upper := (rows 35 14 69 392 176 288 81 209 337), lower := (rows 35 14 69 392 176 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 24 296 0 128 256), good := (rows 35 63 5 440 176 288 0 128 288) }] }

theorem u3836 : Upper (D 9) (R 9) [34,12,65,384,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3836 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3837 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 0, region := 472, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0),(4,0)], upper := (rows 35 14 69 392 208 33 368 432 304), lower := (rows 35 14 69 392 208 33 64 128 256), losses := [] }

theorem u3837 : Upper (D 9) (R 9) [34,12,65,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3837 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3838 : Route 9 := (fun mask => (mask,id))

def c3838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3838 : Upper (D 9) (R 9) [34,12,65,384,192,16] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,192,16] 13 (by decide) (choices 1) [1,32,256] r3838 c3838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u869
  · exact u870
  · exact u871

def r3839 : Route 9 := (fun mask => (mask,id))

def c3839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3839 : Upper (D 9) (R 9) [34,12,65,384,192,256] 13 := by
  apply FastRouting.sound _ _ [34,12,65,384,192,256] 13 (by decide) (choices 1) [1,16,32] r3839 c3839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u872
  · exact u873
  · exact u874

#print axioms u3839
end Delivery.IrregularNine14.P09
