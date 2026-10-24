import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0008

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3780 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 44 392 84 48 97 161 289), lower := (rows 67 162 44 392 84 48 64 128 256), losses := [] }

theorem u3780 : Upper (D 8) (R 8) [66,160,40,384,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3780 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3781 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 48, targets := 128 }], pairs := [(4,7)], upper := (rows 67 162 44 392 112 33 85 149 277), lower := (rows 67 162 44 392 112 33 64 128 256), losses := [] }

theorem u3781 : Upper (D 8) (R 8) [66,160,40,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3782 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 162 44 392 112 36 81 145 273), lower := (rows 67 162 44 392 112 36 64 128 256), losses := [] }

theorem u3782 : Upper (D 8) (R 8) [66,160,40,384,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3782 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3783 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 162 44 392 112 48 69 133 261), lower := (rows 67 162 44 392 112 48 64 128 256), losses := [] }

theorem u3783 : Upper (D 8) (R 8) [66,160,40,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3783 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3784 : PairBound 9 := { available := 36, camps := [], pairs := [(1,6)], upper := (rows 67 162 76 152 273 33 100 164 292), lower := (rows 67 162 76 152 273 33 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 16 49 0 128 256), good := (rows 35 162 14 186 305 33 0 128 256) }] }

theorem u3784 : Upper (D 8) (R 8) [66,160,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3785 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 152 273 36 97 161 289), lower := (rows 67 162 76 152 273 36 64 128 256), losses := [] }

theorem u3785 : Upper (D 8) (R 8) [66,160,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3785 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3786 : Route 9 := (fun mask => (mask,id))

def c3786 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3786 : Upper (D 8) (R 8) [66,160,72,144,288,1] 13 := by
  apply FastRouting.sound _ _ [66,160,72,144,288,1] 13 (by decide) (choices 1) [1,4,32] r3786 c3786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u518
  · exact u519
  · exact u520

def b3787 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 152 304 36 97 161 289), lower := (rows 67 162 76 152 304 36 64 128 256), losses := [] }

theorem u3787 : Upper (D 8) (R 8) [66,160,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3787 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3788 : PairBound 9 := { available := 48, camps := [], pairs := [(1,6)], upper := (rows 67 162 76 265 148 33 112 176 304), lower := (rows 67 162 76 265 148 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 20 41 0 132 260), good := (rows 35 162 446 297 406 33 0 128 256) }] }

theorem u3788 : Upper (D 8) (R 8) [66,160,72,257,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3789 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 265 148 48 97 161 289), lower := (rows 67 162 76 265 148 48 64 128 256), losses := [] }

theorem u3789 : Upper (D 8) (R 8) [66,160,72,257,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3789 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r3790 : Route 9 := (fun mask => (mask,id))

def c3790 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3790 : Upper (D 8) (R 8) [66,160,72,288,132,1] 13 := by
  apply FastRouting.sound _ _ [66,160,72,288,132,1] 13 (by decide) (choices 1) [1,16,32] r3790 c3790
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u521
  · exact u522
  · exact u523

def b3791 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 76 296 148 48 97 161 289), lower := (rows 67 162 76 296 148 48 64 128 256), losses := [] }

theorem u3791 : Upper (D 8) (R 8) [66,160,72,288,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3791 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3792 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 140 273 33 120 184 312), lower := (rows 67 162 100 140 273 33 64 128 256), losses := [] }

theorem u3792 : Upper (D 8) (R 8) [66,160,96,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3793 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 100 140 273 40 113 177 305), lower := (rows 67 162 100 140 273 40 64 128 256), losses := [] }

theorem u3793 : Upper (D 8) (R 8) [66,160,96,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3793 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3794 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 100 140 273 48 105 169 297), lower := (rows 67 162 100 140 273 48 64 128 256), losses := [] }

theorem u3794 : Upper (D 8) (R 8) [66,160,96,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3794 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3795 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 140 280 33 113 177 305), lower := (rows 67 162 100 140 280 33 64 128 256), losses := [] }

theorem u3795 : Upper (D 8) (R 8) [66,160,96,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3796 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 100 140 280 48 97 161 289), lower := (rows 67 162 100 140 280 48 64 128 256), losses := [] }

theorem u3796 : Upper (D 8) (R 8) [66,160,96,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3796 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3797 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 140 304 33 89 153 281), lower := (rows 67 162 100 140 304 33 64 128 256), losses := [] }

theorem u3797 : Upper (D 8) (R 8) [66,160,96,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3798 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 162 100 140 304 40 81 145 273), lower := (rows 67 162 100 140 304 40 64 128 256), losses := [] }

theorem u3798 : Upper (D 8) (R 8) [66,160,96,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3798 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3799 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 162 100 140 304 48 73 137 265), lower := (rows 67 162 100 140 304 48 64 128 256), losses := [] }

theorem u3799 : Upper (D 8) (R 8) [66,160,96,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3799 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3800 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 152 273 33 108 172 300), lower := (rows 67 162 100 152 273 33 64 128 256), losses := [] }

theorem u3800 : Upper (D 8) (R 8) [66,160,96,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3801 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 100 152 273 36 105 169 297), lower := (rows 67 162 100 152 273 36 64 128 256), losses := [] }

theorem u3801 : Upper (D 8) (R 8) [66,160,96,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3801 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3802 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 100 152 273 40 101 165 293), lower := (rows 67 162 100 152 273 40 64 128 256), losses := [] }

theorem u3802 : Upper (D 8) (R 8) [66,160,96,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3802 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3803 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 152 276 33 105 169 297), lower := (rows 67 162 100 152 276 33 64 128 256), losses := [] }

theorem u3803 : Upper (D 8) (R 8) [66,160,96,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3804 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 162 100 152 276 40 97 161 289), lower := (rows 67 162 100 152 276 40 64 128 256), losses := [] }

theorem u3804 : Upper (D 8) (R 8) [66,160,96,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3804 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3805 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 100 152 304 33 77 141 269), lower := (rows 67 162 100 152 304 33 64 128 256), losses := [] }

theorem u3805 : Upper (D 8) (R 8) [66,160,96,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3806 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 162 100 152 304 36 73 137 265), lower := (rows 67 162 100 152 304 36 64 128 256), losses := [] }

theorem u3806 : Upper (D 8) (R 8) [66,160,96,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3806 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3807 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 67 162 100 152 304 40 69 133 261), lower := (rows 67 162 100 152 304 40 64 128 256), losses := [] }

theorem u3807 : Upper (D 8) (R 8) [66,160,96,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3807 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3808 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 28 104 176 33 228 164 420), lower := (rows 67 259 28 104 176 33 64 128 256), losses := [] }

theorem u3808 : Upper (D 8) (R 8) [66,257,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3809 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 259 28 104 176 36 225 161 417), lower := (rows 67 259 28 104 176 36 64 128 256), losses := [] }

theorem u3809 : Upper (D 8) (R 8) [66,257,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3809 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3810 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 28 104 176 160 101 165 293), lower := (rows 67 259 28 104 176 160 64 128 256), losses := [] }

theorem u3810 : Upper (D 8) (R 8) [66,257,24,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3811 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 88 176 33 228 164 420), lower := (rows 67 259 44 88 176 33 64 128 256), losses := [] }

theorem u3811 : Upper (D 8) (R 8) [66,257,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3812 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 259 44 88 176 36 225 161 417), lower := (rows 67 259 44 88 176 36 64 128 256), losses := [] }

theorem u3812 : Upper (D 8) (R 8) [66,257,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3812 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3813 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 88 176 160 101 165 293), lower := (rows 67 259 44 88 176 160 64 128 256), losses := [] }

theorem u3813 : Upper (D 8) (R 8) [66,257,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3814 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 140 112 33 240 176 432), lower := (rows 67 259 44 140 112 33 64 128 256), losses := [] }

theorem u3814 : Upper (D 8) (R 8) [66,257,40,132,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3815 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 259 44 140 112 48 225 161 417), lower := (rows 67 259 44 140 112 48 64 128 256), losses := [] }

theorem u3815 : Upper (D 8) (R 8) [66,257,40,132,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3815 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3816 : PairBound 9 := { available := 49, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 140 112 160 113 177 305), lower := (rows 67 259 44 140 112 160 64 128 256), losses := [] }

theorem u3816 : Upper (D 8) (R 8) [66,257,40,132,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3817 : PairBound 9 := { available := 164, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 152 112 33 228 164 420), lower := (rows 67 259 44 152 112 33 64 128 256), losses := [] }

theorem u3817 : Upper (D 8) (R 8) [66,257,40,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3818 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 259 44 152 112 36 225 161 417), lower := (rows 67 259 44 152 112 36 64 128 256), losses := [] }

theorem u3818 : Upper (D 8) (R 8) [66,257,40,144,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3818 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3819 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 67 259 44 152 112 160 101 165 293), lower := (rows 67 259 44 152 112 160 64 128 256), losses := [] }

theorem u3819 : Upper (D 8) (R 8) [66,257,40,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3820 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 44 200 176 33 116 180 308), lower := (rows 67 259 44 200 176 33 64 128 256), losses := [] }

theorem u3820 : Upper (D 8) (R 8) [66,257,40,192,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3821 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 259 44 200 176 36 113 177 305), lower := (rows 67 259 44 200 176 36 64 128 256), losses := [] }

theorem u3821 : Upper (D 8) (R 8) [66,257,40,192,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3821 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3822 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 259 44 200 176 48 101 165 293), lower := (rows 67 259 44 200 176 48 64 128 256), losses := [] }

theorem u3822 : Upper (D 8) (R 8) [66,257,40,192,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3822 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3823 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 220, targets := 1 }], pairs := [(2,0)], upper := (rows 67 259 100 140 176 33 120 184 312), lower := (rows 67 259 100 140 176 33 64 128 256), losses := [] }

theorem u3823 : Upper (D 8) (R 8) [66,257,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3824 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 259 100 140 176 40 113 177 305), lower := (rows 67 259 100 140 176 40 64 128 256), losses := [] }

theorem u3824 : Upper (D 8) (R 8) [66,257,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3824 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3825 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 259 100 140 176 48 105 169 297), lower := (rows 67 259 100 140 176 48 64 128 256), losses := [] }

theorem u3825 : Upper (D 8) (R 8) [66,257,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3825 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3826 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 168 112 33 240 176 432), lower := (rows 67 262 13 168 112 33 64 128 256), losses := [] }

theorem u3826 : Upper (D 8) (R 8) [66,260,9,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3827 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 13 168 112 48 225 161 417), lower := (rows 67 262 13 168 112 48 64 128 256), losses := [] }

theorem u3827 : Upper (D 8) (R 8) [66,260,9,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3827 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3828 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 13 168 112 160 113 177 305), lower := (rows 67 262 13 168 112 160 64 128 256), losses := [] }

theorem u3828 : Upper (D 8) (R 8) [66,260,9,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3829 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 13 168 208 33 112 176 304), lower := (rows 67 262 13 168 208 33 64 128 256), losses := [] }

theorem u3829 : Upper (D 8) (R 8) [66,260,9,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3830 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 262 13 168 208 48 97 161 289), lower := (rows 67 262 13 168 208 48 64 128 256), losses := [] }

theorem u3830 : Upper (D 8) (R 8) [66,260,9,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3830 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3831 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 28 41 176 33 224 224 480), lower := (rows 67 262 28 41 176 33 64 128 256), losses := [] }

theorem u3831 : Upper (D 8) (R 8) [66,260,24,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3832 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 28 41 176 96 225 161 417), lower := (rows 67 262 28 41 176 96 64 128 256), losses := [] }

theorem u3832 : Upper (D 8) (R 8) [66,260,24,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3833 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 28 41 176 160 97 225 353), lower := (rows 67 262 28 41 176 160 64 128 256), losses := [] }

theorem u3833 : Upper (D 8) (R 8) [66,260,24,33,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3834 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 56 152 33 224 224 480), lower := (rows 67 262 37 56 152 33 64 128 256), losses := [] }

theorem u3834 : Upper (D 8) (R 8) [66,260,33,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3835 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 37 56 152 96 225 161 417), lower := (rows 67 262 37 56 152 96 64 128 256), losses := [] }

theorem u3835 : Upper (D 8) (R 8) [66,260,33,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3836 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 67 262 37 56 152 160 97 225 353), lower := (rows 67 262 37 56 152 160 64 128 256), losses := [] }

theorem u3836 : Upper (D 8) (R 8) [66,260,33,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3837 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 262 37 56 208 33 232 168 424), lower := (rows 67 262 37 56 208 33 64 128 256), losses := [] }

theorem u3837 : Upper (D 8) (R 8) [66,260,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3838 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 262 37 56 208 40 225 161 417), lower := (rows 67 262 37 56 208 40 64 128 256), losses := [] }

theorem u3838 : Upper (D 8) (R 8) [66,260,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3838 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3839 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 67 262 37 56 208 160 105 169 297), lower := (rows 67 262 37 56 208 160 64 128 256), losses := [] }

theorem u3839 : Upper (D 8) (R 8) [66,260,33,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3839
end Delivery.IrregularNine14.P08
