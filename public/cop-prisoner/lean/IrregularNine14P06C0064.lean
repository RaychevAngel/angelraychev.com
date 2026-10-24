import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0004

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 163, targets := 4 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 131 292 88 22 96 68 161 289), lower := (rows 11 131 292 88 22 96 68 128 256), losses := [] }

theorem u3840 : Upper (D 6) (R 6) [10,129,288,80,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3840 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 105, targets := 4 }], pairs := [(0,2),(3,0),(3,1)], upper := (rows 11 131 292 88 22 96 96 133 261), lower := (rows 11 131 292 88 22 96 96 128 256), losses := [] }

theorem u3841 : Upper (D 6) (R 6) [10,129,288,80,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3841 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3842 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 260, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 131 292 104 21 48 66 196 324), lower := (rows 11 131 292 104 21 48 66 128 256), losses := [] }

theorem u3842 : Upper (D 6) (R 6) [10,129,288,96,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3842 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3843 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 131 292 104 21 48 68 194 322), lower := (rows 11 131 292 104 21 48 68 128 256), losses := [] }

theorem u3843 : Upper (D 6) (R 6) [10,129,288,96,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3843 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 260, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 131 292 104 22 48 65 196 324), lower := (rows 11 131 292 104 22 48 65 128 256), losses := [] }

theorem u3844 : Upper (D 6) (R 6) [10,129,288,96,6,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3844 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3845 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 131 292 104 22 48 68 193 321), lower := (rows 11 131 292 104 22 48 68 128 256), losses := [] }

theorem u3845 : Upper (D 6) (R 6) [10,129,288,96,6,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3845 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 104 84 33 66 148 276), lower := (rows 11 131 292 104 84 33 66 128 256), losses := [] }

theorem u3846 : Upper (D 6) (R 6) [10,129,288,96,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3846 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3847 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 104 84 33 68 146 274), lower := (rows 11 131 292 104 84 33 68 128 256), losses := [] }

theorem u3847 : Upper (D 6) (R 6) [10,129,288,96,68,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3847 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3848 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 292 104 84 33 80 134 262), lower := (rows 11 131 292 104 84 33 80 128 256), losses := [] }

theorem u3848 : Upper (D 6) (R 6) [10,129,288,96,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3848 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3849 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 276, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 131 292 104 84 34 65 148 276), lower := (rows 11 131 292 104 84 34 65 128 256), losses := [] }

theorem u3849 : Upper (D 6) (R 6) [10,129,288,96,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3849 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3850 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 131 292 104 84 34 68 145 273), lower := (rows 11 131 292 104 84 34 68 128 256), losses := [] }

theorem u3850 : Upper (D 6) (R 6) [10,129,288,96,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3850 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 88, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 131 292 104 84 34 80 133 261), lower := (rows 11 131 292 104 84 34 80 128 256), losses := [] }

theorem u3851 : Upper (D 6) (R 6) [10,129,288,96,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3851 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 466, targets := 1 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 134 37 25 276 96 66 224 352), lower := (rows 11 134 37 25 276 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 96 64 224 352), good := (rows 9 156 445 25 284 480 480 128 256) }] }

theorem u3852 : Upper (D 6) (R 6) [10,132,33,17,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3852 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3853 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 466, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 134 37 25 276 96 96 194 322), lower := (rows 11 134 37 25 276 96 96 128 256), losses := [] }

theorem u3853 : Upper (D 6) (R 6) [10,132,33,17,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3853 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3854 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,1),(4,2)], upper := (rows 11 134 37 28 273 96 66 224 352), lower := (rows 11 134 37 28 273 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 14 20 96 64 224 352), good := (rows 9 156 445 28 273 480 488 128 256) }] }

theorem u3854 : Upper (D 6) (R 6) [10,132,33,20,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3854 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 37 28 273 96 96 194 322), lower := (rows 11 134 37 28 273 96 96 128 256), losses := [] }

theorem u3855 : Upper (D 6) (R 6) [10,132,33,20,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3855 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3856 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 11 134 37 28 274 96 65 224 352), lower := (rows 11 134 37 28 274 96 65 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 20 96 64 224 352), good := (rows 10 158 446 30 282 480 480 128 256) }] }

theorem u3856 : Upper (D 6) (R 6) [10,132,33,20,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3856 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3857 : Route 9 := (fun mask => (mask,id))

def c3857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3857 : Upper (D 6) (R 6) [10,132,33,20,258,64,32] 13 := by
  apply FastRouting.sound _ _ [10,132,33,20,258,64,32] 13 (by decide) (choices 1) [1,64] r3857 c3857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u270
  · exact u271

def b3858 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 37 76 50 288 65 208 336), lower := (rows 11 134 37 76 50 288 65 128 256), losses := [] }

theorem u3858 : Upper (D 6) (R 6) [10,132,33,68,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3858 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3859 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 131, targets := 32 }], pairs := [(0,5)], upper := (rows 11 134 37 76 50 288 80 193 321), lower := (rows 11 134 37 76 50 288 80 128 256), losses := [] }

theorem u3859 : Upper (D 6) (R 6) [10,132,33,68,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3859 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3860 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 37 76 82 288 65 176 304), lower := (rows 11 134 37 76 82 288 65 128 256), losses := [] }

theorem u3860 : Upper (D 6) (R 6) [10,132,33,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3860 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3861 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 89, targets := 32 }], pairs := [(0,5)], upper := (rows 11 134 37 76 82 288 80 161 289), lower := (rows 11 134 37 76 82 288 80 128 256), losses := [] }

theorem u3861 : Upper (D 6) (R 6) [10,132,33,68,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3861 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 76 82 288 96 145 273), lower := (rows 11 134 37 76 82 288 96 128 256), losses := [] }

theorem u3862 : Upper (D 6) (R 6) [10,132,33,68,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3862 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 37 76 112 288 65 146 274), lower := (rows 11 134 37 76 112 288 65 128 256), losses := [] }

theorem u3863 : Upper (D 6) (R 6) [10,132,33,68,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3863 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 134 37 76 112 288 66 145 273), lower := (rows 11 134 37 76 112 288 66 128 256), losses := [] }

theorem u3864 : Upper (D 6) (R 6) [10,132,33,68,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3864 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 11 134 37 76 112 288 80 131 259), lower := (rows 11 134 37 76 112 288 80 128 256), losses := [] }

theorem u3865 : Upper (D 6) (R 6) [10,132,33,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3865 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3866 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 134 37 265 50 96 68 208 336), lower := (rows 11 134 37 265 50 96 68 128 256), losses := [] }

theorem u3866 : Upper (D 6) (R 6) [10,132,33,257,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3867 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 210, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 11 134 37 265 50 96 80 196 324), lower := (rows 11 134 37 265 50 96 80 128 256), losses := [] }

theorem u3867 : Upper (D 6) (R 6) [10,132,33,257,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3867 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 11 134 37 265 82 96 68 176 304), lower := (rows 11 134 37 265 82 96 68 128 256), losses := [] }

theorem u3868 : Upper (D 6) (R 6) [10,132,33,257,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 265 82 96 80 164 292), lower := (rows 11 134 37 265 82 96 80 128 256), losses := [] }

theorem u3869 : Upper (D 6) (R 6) [10,132,33,257,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3869 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 134 37 265 82 96 96 148 276), lower := (rows 11 134 37 265 82 96 96 128 256), losses := [] }

theorem u3870 : Upper (D 6) (R 6) [10,132,33,257,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 210, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 11 134 37 265 84 96 66 176 304), lower := (rows 11 134 37 265 84 96 66 128 256), losses := [] }

theorem u3871 : Upper (D 6) (R 6) [10,132,33,257,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 265 84 96 80 162 290), lower := (rows 11 134 37 265 84 96 80 128 256), losses := [] }

theorem u3872 : Upper (D 6) (R 6) [10,132,33,257,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3872 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 134 37 265 84 96 96 146 274), lower := (rows 11 134 37 265 84 96 96 128 256), losses := [] }

theorem u3873 : Upper (D 6) (R 6) [10,132,33,257,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r3874 : Route 9 := (fun mask => (mask,id))

def c3874 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3874 : Upper (D 6) (R 6) [10,132,33,260,34,64,1] 13 := by
  apply FastRouting.sound _ _ [10,132,33,260,34,64,1] 13 (by decide) (choices 1) [16,64] r3874 c3874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u272
  · exact u273

def b3875 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 134 37 268 50 96 80 193 321), lower := (rows 11 134 37 268 50 96 80 128 256), losses := [] }

theorem u3875 : Upper (D 6) (R 6) [10,132,33,260,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3875 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 300, targets := 2 },{ cop := 0, region := 80, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 134 37 268 81 96 66 176 304), lower := (rows 11 134 37 268 81 96 66 128 256), losses := [] }

theorem u3876 : Upper (D 6) (R 6) [10,132,33,260,65,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 268 81 96 80 162 290), lower := (rows 11 134 37 268 81 96 80 128 256), losses := [] }

theorem u3877 : Upper (D 6) (R 6) [10,132,33,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3877 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 0, region := 112, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 11 134 37 268 81 96 96 146 274), lower := (rows 11 134 37 268 81 96 96 128 256), losses := [] }

theorem u3878 : Upper (D 6) (R 6) [10,132,33,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3879 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 80, targets := 4 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 134 37 268 82 96 65 176 304), lower := (rows 11 134 37 268 82 96 65 128 256), losses := [] }

theorem u3879 : Upper (D 6) (R 6) [10,132,33,260,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3880 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 268 82 96 80 161 289), lower := (rows 11 134 37 268 82 96 80 128 256), losses := [] }

theorem u3880 : Upper (D 6) (R 6) [10,132,33,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3880 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3881 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(4,0),(4,2)], upper := (rows 11 134 37 268 82 96 96 145 273), lower := (rows 11 134 37 268 82 96 96 128 256), losses := [] }

theorem u3881 : Upper (D 6) (R 6) [10,132,33,260,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 112, targets := 4 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(4,2)], upper := (rows 11 134 37 280 50 96 65 196 324), lower := (rows 11 134 37 280 50 96 65 128 256), losses := [] }

theorem u3882 : Upper (D 6) (R 6) [10,132,33,272,34,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 1, region := 112, targets := 1 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(4,0)], upper := (rows 11 134 37 280 50 96 68 193 321), lower := (rows 11 134 37 280 50 96 68 128 256), losses := [] }

theorem u3883 : Upper (D 6) (R 6) [10,132,33,272,34,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 134 37 280 82 96 65 164 292), lower := (rows 11 134 37 280 82 96 65 128 256), losses := [] }

theorem u3884 : Upper (D 6) (R 6) [10,132,33,272,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 297, targets := 4 },{ cop := 0, region := 100, targets := 2 }], pairs := [(0,2),(2,1),(3,2)], upper := (rows 11 134 37 280 82 96 68 161 289), lower := (rows 11 134 37 280 82 96 68 128 256), losses := [] }

theorem u3885 : Upper (D 6) (R 6) [10,132,33,272,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 2, region := 130, targets := 32 }], pairs := [(1,5),(4,0),(4,2)], upper := (rows 11 134 37 280 82 96 96 133 261), lower := (rows 11 134 37 280 82 96 96 128 256), losses := [] }

theorem u3886 : Upper (D 6) (R 6) [10,132,33,272,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3887 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 134 37 296 82 96 65 148 276), lower := (rows 11 134 37 296 82 96 65 128 256), losses := [] }

theorem u3887 : Upper (D 6) (R 6) [10,132,33,288,66,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3888 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 4, region := 297, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 11 134 37 296 82 96 68 145 273), lower := (rows 11 134 37 296 82 96 68 128 256), losses := [] }

theorem u3888 : Upper (D 6) (R 6) [10,132,33,288,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3889 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 296 82 96 80 133 261), lower := (rows 11 134 37 296 82 96 80 128 256), losses := [] }

theorem u3889 : Upper (D 6) (R 6) [10,132,33,288,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3889 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3890 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 134 37 296 84 96 65 146 274), lower := (rows 11 134 37 296 84 96 65 128 256), losses := [] }

theorem u3890 : Upper (D 6) (R 6) [10,132,33,288,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3891 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(1,5),(4,0),(4,5)], upper := (rows 11 134 37 296 84 96 66 145 273), lower := (rows 11 134 37 296 84 96 66 128 256), losses := [] }

theorem u3891 : Upper (D 6) (R 6) [10,132,33,288,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3892 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 296 84 96 80 131 259), lower := (rows 11 134 37 296 84 96 80 128 256), losses := [] }

theorem u3892 : Upper (D 6) (R 6) [10,132,33,288,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3892 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3893 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 0, region := 36, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 11 134 37 328 82 36 65 176 304), lower := (rows 11 134 37 328 82 36 65 128 256), losses := [] }

theorem u3893 : Upper (D 6) (R 6) [10,132,33,320,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3894 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 134 37 328 82 36 80 161 289), lower := (rows 11 134 37 328 82 36 80 128 256), losses := [] }

theorem u3894 : Upper (D 6) (R 6) [10,132,33,320,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3894 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3895 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 265, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 134 37 328 82 36 96 145 273), lower := (rows 11 134 37 328 82 36 96 128 256), losses := [] }

theorem u3895 : Upper (D 6) (R 6) [10,132,33,320,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3896 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 11 134 37 328 84 48 65 162 290), lower := (rows 11 134 37 328 84 48 65 128 256), losses := [] }

theorem u3896 : Upper (D 6) (R 6) [10,132,33,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3896 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3897 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 80, targets := 1 },{ cop := 1, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 11 134 37 328 84 48 66 161 289), lower := (rows 11 134 37 328 84 48 66 128 256), losses := [] }

theorem u3897 : Upper (D 6) (R 6) [10,132,33,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3897 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3898 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 395, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 134 37 328 84 48 96 131 259), lower := (rows 11 134 37 328 84 48 96 128 256), losses := [] }

theorem u3898 : Upper (D 6) (R 6) [10,132,33,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3898 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b3899 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 11 134 37 328 112 36 65 146 274), lower := (rows 11 134 37 328 112 36 65 128 256), losses := [] }

theorem u3899 : Upper (D 6) (R 6) [10,132,33,320,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b3899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u3899
end Delivery.IrregularNine14.P06
