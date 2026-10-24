import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0004

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3780 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 146 288 65 208 336), lower := (rows 13 98 7 168 146 288 65 128 256), losses := [] }

theorem u3780 : Upper (D 7) (R 7) [12,96,3,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3780 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3781 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 13 98 7 168 146 288 80 193 321), lower := (rows 13 98 7 168 146 288 80 128 256), losses := [] }

theorem u3781 : Upper (D 7) (R 7) [12,96,3,160,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3781 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 208 288 65 146 274), lower := (rows 13 98 7 168 208 288 65 128 256), losses := [] }

theorem u3782 : Upper (D 7) (R 7) [12,96,3,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3782 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 208 288 66 145 273), lower := (rows 13 98 7 168 208 288 66 128 256), losses := [] }

theorem u3783 : Upper (D 7) (R 7) [12,96,3,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3783 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 13 98 7 168 208 288 80 131 259), lower := (rows 13 98 7 168 208 288 80 128 256), losses := [] }

theorem u3784 : Upper (D 7) (R 7) [12,96,3,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3784 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 168 274 48 65 192 448), lower := (rows 13 98 7 168 274 48 65 128 256), losses := [] }

theorem u3785 : Upper (D 7) (R 7) [12,96,3,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3785 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3786 : Route 9 := (fun mask => (mask,id))

def c3786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3786 : Upper (D 7) (R 7) [12,96,3,160,258,16,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,160,258,16,128] 13 (by decide) (choices 1) [1,64] r3786 c3786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u248
  · exact u249

def b3787 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 7 265 146 48 192 224 352), lower := (rows 13 98 7 265 146 48 192 128 256), losses := [] }

theorem u3787 : Upper (D 7) (R 7) [12,96,3,257,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3787 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 265 146 96 192 176 304), lower := (rows 13 98 7 265 146 96 192 128 256), losses := [] }

theorem u3788 : Upper (D 7) (R 7) [12,96,3,257,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3788 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 4, region := 70, targets := 128 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 98 7 280 49 160 66 192 448), lower := (rows 13 98 7 280 49 160 66 128 256), losses := [] }

theorem u3789 : Upper (D 7) (R 7) [12,96,3,272,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3789 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3790 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 280 49 160 192 194 322), lower := (rows 13 98 7 280 49 160 192 128 256), losses := [] }

theorem u3790 : Upper (D 7) (R 7) [12,96,3,272,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3790 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3791 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(0,1),(1,0),(1,7),(3,0)], upper := (rows 13 98 7 280 145 34 192 224 352), lower := (rows 13 98 7 280 145 34 192 128 256), losses := [{ target := 1, region := (rows 5 0 4 12 20 32 246 162 290), good := (rows 93 480 477 344 209 480 192 192 256) }] }

theorem u3791 : Upper (D 7) (R 7) [12,96,3,272,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3791 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 145 96 192 162 290), lower := (rows 13 98 7 280 145 96 192 128 256), losses := [] }

theorem u3792 : Upper (D 7) (R 7) [12,96,3,272,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3792 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 13 98 7 280 146 33 192 224 352), lower := (rows 13 98 7 280 146 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 37 247 167 295), good := (rows 493 480 485 344 472 481 192 192 256) }] }

theorem u3793 : Upper (D 7) (R 7) [12,96,3,272,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3793 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3794 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 7 280 146 96 192 161 289), lower := (rows 13 98 7 280 146 96 192 128 256), losses := [] }

theorem u3794 : Upper (D 7) (R 7) [12,96,3,272,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3795 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 280 176 33 66 192 448), lower := (rows 13 98 7 280 176 33 66 128 256), losses := [] }

theorem u3795 : Upper (D 7) (R 7) [12,96,3,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3796 : Route 9 := (fun mask => (mask,id))

def c3796 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3796 : Upper (D 7) (R 7) [12,96,3,272,160,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,160,1,128] 13 (by decide) (choices 1) [2,64] r3796 c3796
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u250
  · exact u251

def b3797 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 280 176 34 65 192 448), lower := (rows 13 98 7 280 176 34 65 128 256), losses := [] }

theorem u3797 : Upper (D 7) (R 7) [12,96,3,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3798 : Route 9 := (fun mask => (mask,id))

def c3798 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3798 : Upper (D 7) (R 7) [12,96,3,272,160,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,3,272,160,2,128] 13 (by decide) (choices 1) [1,64] r3798 c3798
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u252
  · exact u253

def b3799 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 13 98 7 296 81 160 66 144 400), lower := (rows 13 98 7 296 81 160 66 128 256), losses := [] }

theorem u3799 : Upper (D 7) (R 7) [12,96,3,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3800 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 296 81 160 80 130 386), lower := (rows 13 98 7 296 81 160 80 128 256), losses := [] }

theorem u3800 : Upper (D 7) (R 7) [12,96,3,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3800 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 7 296 81 160 192 146 274), lower := (rows 13 98 7 296 81 160 192 128 256), losses := [] }

theorem u3801 : Upper (D 7) (R 7) [12,96,3,288,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 296 145 160 66 208 336), lower := (rows 13 98 7 296 145 160 66 128 256), losses := [] }

theorem u3802 : Upper (D 7) (R 7) [12,96,3,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3803 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 7 296 145 160 80 194 322), lower := (rows 13 98 7 296 145 160 80 128 256), losses := [] }

theorem u3803 : Upper (D 7) (R 7) [12,96,3,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3803 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 13 98 7 296 146 48 65 192 448), lower := (rows 13 98 7 296 146 48 65 128 256), losses := [] }

theorem u3804 : Upper (D 7) (R 7) [12,96,3,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3804 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3805 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 7 296 146 48 192 193 321), lower := (rows 13 98 7 296 146 48 192 128 256), losses := [] }

theorem u3805 : Upper (D 7) (R 7) [12,96,3,288,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3805 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3806 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 296 146 160 65 208 336), lower := (rows 13 98 7 296 146 160 65 128 256), losses := [] }

theorem u3806 : Upper (D 7) (R 7) [12,96,3,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 13 98 7 296 146 160 80 193 321), lower := (rows 13 98 7 296 146 160 80 128 256), losses := [] }

theorem u3807 : Upper (D 7) (R 7) [12,96,3,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3807 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 296 208 160 65 146 274), lower := (rows 13 98 7 296 208 160 65 128 256), losses := [] }

theorem u3808 : Upper (D 7) (R 7) [12,96,3,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 296 208 160 66 145 273), lower := (rows 13 98 7 296 208 160 66 128 256), losses := [] }

theorem u3809 : Upper (D 7) (R 7) [12,96,3,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3809 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 7 296 208 160 80 131 259), lower := (rows 13 98 7 296 208 160 80 128 256), losses := [] }

theorem u3810 : Upper (D 7) (R 7) [12,96,3,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3810 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3811 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 7 392 146 33 80 224 352), lower := (rows 13 98 7 392 146 33 80 128 256), losses := [] }

theorem u3811 : Upper (D 7) (R 7) [12,96,3,384,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3811 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3812 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 7 392 146 33 96 208 336), lower := (rows 13 98 7 392 146 33 96 128 256), losses := [] }

theorem u3812 : Upper (D 7) (R 7) [12,96,3,384,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 392 146 48 96 193 321), lower := (rows 13 98 7 392 146 48 96 128 256), losses := [] }

theorem u3813 : Upper (D 7) (R 7) [12,96,3,384,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3813 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3814 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 13 98 7 392 176 34 65 208 336), lower := (rows 13 98 7 392 176 34 65 128 256), losses := [] }

theorem u3814 : Upper (D 7) (R 7) [12,96,3,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 7 392 176 34 80 193 321), lower := (rows 13 98 7 392 176 34 80 128 256), losses := [] }

theorem u3815 : Upper (D 7) (R 7) [12,96,3,384,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3815 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 21 41 274 160 66 192 448), lower := (rows 13 98 21 41 274 160 66 128 256), losses := [] }

theorem u3816 : Upper (D 7) (R 7) [12,96,17,33,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3817 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 21 41 274 160 192 194 322), lower := (rows 13 98 21 41 274 160 192 128 256), losses := [] }

theorem u3817 : Upper (D 7) (R 7) [12,96,17,33,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3817 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 498, targets := 1 },{ cop := 1, region := 400, targets := 32 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 21 41 336 160 66 130 386), lower := (rows 13 98 21 41 336 160 66 128 256), losses := [] }

theorem u3818 : Upper (D 7) (R 7) [12,96,17,33,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3819 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 13 98 21 41 336 160 192 130 258), lower := (rows 13 98 21 41 336 160 192 128 256), losses := [] }

theorem u3819 : Upper (D 7) (R 7) [12,96,17,33,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3819 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3820 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 21 138 176 288 65 194 322), lower := (rows 13 98 21 138 176 288 65 128 256), losses := [] }

theorem u3820 : Upper (D 7) (R 7) [12,96,17,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3820 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 1 },{ cop := 0, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 21 138 176 288 66 193 321), lower := (rows 13 98 21 138 176 288 66 128 256), losses := [] }

theorem u3821 : Upper (D 7) (R 7) [12,96,17,130,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3821 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 21 138 274 33 96 192 448), lower := (rows 13 98 21 138 274 33 96 128 256), losses := [] }

theorem u3822 : Upper (D 7) (R 7) [12,96,17,130,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3822 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 272, targets := 128 }], pairs := [(1,0),(3,0),(4,0),(4,7)], upper := (rows 13 98 21 138 274 33 192 224 352), lower := (rows 13 98 21 138 274 33 192 128 256), losses := [] }

theorem u3823 : Upper (D 7) (R 7) [12,96,17,130,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 21 138 274 96 192 161 289), lower := (rows 13 98 21 138 274 96 192 128 256), losses := [] }

theorem u3824 : Upper (D 7) (R 7) [12,96,17,130,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3825 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 138 304 34 65 192 448), lower := (rows 13 98 21 138 304 34 65 128 256), losses := [] }

theorem u3825 : Upper (D 7) (R 7) [12,96,17,130,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3825 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3826 : Route 9 := (fun mask => (mask,id))

def c3826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3826 : Upper (D 7) (R 7) [12,96,17,130,288,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,288,2,128] 13 (by decide) (choices 1) [1,64] r3826 c3826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u254
  · exact u255

def b3827 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 13 98 21 138 304 160 65 194 322), lower := (rows 13 98 21 138 304 160 65 128 256), losses := [] }

theorem u3827 : Upper (D 7) (R 7) [12,96,17,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3827 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3828 : Route 9 := (fun mask => (mask,id))

def c3828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3828 : Upper (D 7) (R 7) [12,96,17,130,288,128,2] 13 := by
  apply FastRouting.sound _ _ [12,96,17,130,288,128,2] 13 (by decide) (choices 1) [1,64] r3828 c3828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u256
  · exact u257

def b3829 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 138 400 33 66 224 352), lower := (rows 13 98 21 138 400 33 66 128 256), losses := [] }

theorem u3829 : Upper (D 7) (R 7) [12,96,17,130,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3830 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 21 138 400 34 96 193 321), lower := (rows 13 98 21 138 400 34 96 128 256), losses := [] }

theorem u3830 : Upper (D 7) (R 7) [12,96,17,130,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 21 168 146 288 65 194 322), lower := (rows 13 98 21 168 146 288 65 128 256), losses := [] }

theorem u3831 : Upper (D 7) (R 7) [12,96,17,160,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3831 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 82, targets := 1 },{ cop := 0, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 21 168 146 288 66 193 321), lower := (rows 13 98 21 168 146 288 66 128 256), losses := [] }

theorem u3832 : Upper (D 7) (R 7) [12,96,17,160,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3832 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5),(2,1),(2,5)], upper := (rows 13 98 21 168 208 34 65 386 258), lower := (rows 13 98 21 168 208 34 65 128 256), losses := [] }

theorem u3833 : Upper (D 7) (R 7) [12,96,17,160,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3834 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 21 168 208 34 66 385 257), lower := (rows 13 98 21 168 208 34 66 128 256), losses := [] }

theorem u3834 : Upper (D 7) (R 7) [12,96,17,160,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3835 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 42, targets := 1 },{ cop := 0, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 13 98 21 168 208 34 320 131 259), lower := (rows 13 98 21 168 208 34 320 128 256), losses := [] }

theorem u3835 : Upper (D 7) (R 7) [12,96,17,160,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3835 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3836 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 98 21 168 208 288 65 130 258), lower := (rows 13 98 21 168 208 288 65 128 256), losses := [] }

theorem u3836 : Upper (D 7) (R 7) [12,96,17,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3836 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3837 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 82, targets := 1 },{ cop := 0, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 13 98 21 168 208 288 66 131 259), lower := (rows 13 98 21 168 208 288 66 128 256), losses := [] }

theorem u3837 : Upper (D 7) (R 7) [12,96,17,160,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3837 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3838 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 21 168 274 34 65 192 448), lower := (rows 13 98 21 168 274 34 65 128 256), losses := [] }

theorem u3838 : Upper (D 7) (R 7) [12,96,17,160,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r3839 : Route 9 := (fun mask => (mask,id))

def c3839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3839 : Upper (D 7) (R 7) [12,96,17,160,258,2,128] 13 := by
  apply FastRouting.sound _ _ [12,96,17,160,258,2,128] 13 (by decide) (choices 1) [1,64] r3839 c3839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u258
  · exact u259

#print axioms u3839
end Delivery.IrregularNine14.P07
