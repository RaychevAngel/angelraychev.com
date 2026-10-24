import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0020

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3840 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 67, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 19 67 140 296 52 40 71 135 263), lower := (rows 19 67 140 296 52 40 64 128 256), losses := [] }

theorem u3840 : Upper (D 5) (R 5) [18,65,136,288,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3841 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 330, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 42 148 33 328 392 264), lower := (rows 19 70 37 42 148 33 64 128 256), losses := [] }

theorem u3841 : Upper (D 5) (R 5) [18,68,33,34,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3841
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3842 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 37 42 148 40 329 393 265), lower := (rows 19 70 37 42 148 40 64 128 256), losses := [] }

theorem u3842 : Upper (D 5) (R 5) [18,68,33,34,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3842
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3843 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 19 70 37 42 148 288 73 137 265), lower := (rows 19 70 37 42 148 288 64 128 256), losses := [] }

theorem u3843 : Upper (D 5) (R 5) [18,68,33,34,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3844 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 330, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 42 152 33 332 396 268), lower := (rows 19 70 37 42 152 33 64 128 256), losses := [] }

theorem u3844 : Upper (D 5) (R 5) [18,68,33,34,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3845 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 401, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 37 42 152 36 329 393 265), lower := (rows 19 70 37 42 152 36 64 128 256), losses := [] }

theorem u3845 : Upper (D 5) (R 5) [18,68,33,34,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3846 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 37 42 152 40 325 389 261), lower := (rows 19 70 37 42 152 40 64 128 256), losses := [] }

theorem u3846 : Upper (D 5) (R 5) [18,68,33,34,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3847 : Route 9 := (fun mask => (mask,id))

def c3847 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3847 : Upper (D 5) (R 5) [18,68,33,34,136,256] 13 := by
  apply FastRouting.sound _ _ [18,68,33,34,136,256] 13 (by decide) (choices 1) [1,4,8] r3847 c3847
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1211
  · exact u1212
  · exact u1213

def b3848 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 74, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 42 400 33 76 140 268), lower := (rows 19 70 37 42 400 33 64 128 256), losses := [] }

theorem u3848 : Upper (D 5) (R 5) [18,68,33,34,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3848
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3849 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 401, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 19 70 37 42 400 36 73 137 265), lower := (rows 19 70 37 42 400 36 64 128 256), losses := [] }

theorem u3849 : Upper (D 5) (R 5) [18,68,33,34,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3850 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 19 70 37 42 400 40 77 141 269), lower := (rows 19 70 37 42 400 40 64 128 256), losses := [] }

theorem u3850 : Upper (D 5) (R 5) [18,68,33,34,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3850
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3851 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 137 276 34 104 168 296), lower := (rows 19 70 37 137 276 34 64 128 256), losses := [] }

theorem u3851 : Upper (D 5) (R 5) [18,68,33,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3851
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3852 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 168, targets := 4 },{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1),(3,2)], upper := (rows 19 70 37 137 276 40 106 170 298), lower := (rows 19 70 37 137 276 40 64 128 256), losses := [] }

theorem u3852 : Upper (D 5) (R 5) [18,68,33,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3853 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 137 280 34 108 172 300), lower := (rows 19 70 37 137 280 34 64 128 256), losses := [] }

theorem u3853 : Upper (D 5) (R 5) [18,68,33,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3854 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 37 137 280 36 106 170 298), lower := (rows 19 70 37 137 280 36 64 128 256), losses := [] }

theorem u3854 : Upper (D 5) (R 5) [18,68,33,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3855 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 66, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 37 137 280 40 102 166 294), lower := (rows 19 70 37 137 280 40 64 128 256), losses := [] }

theorem u3855 : Upper (D 5) (R 5) [18,68,33,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3856 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 138 28 33 360 424 296), lower := (rows 19 70 37 138 28 33 64 128 256), losses := [] }

theorem u3856 : Upper (D 5) (R 5) [18,68,33,130,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3857 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 2, region := 322, targets := 8 }], pairs := [(1,3),(3,2)], upper := (rows 19 70 37 138 28 40 353 417 289), lower := (rows 19 70 37 138 28 40 64 128 256), losses := [] }

theorem u3857 : Upper (D 5) (R 5) [18,68,33,130,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3858 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(3,2)], upper := (rows 19 70 37 138 28 288 105 169 297), lower := (rows 19 70 37 138 28 288 64 128 256), losses := [] }

theorem u3858 : Upper (D 5) (R 5) [18,68,33,130,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3859 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 138 276 33 104 168 296), lower := (rows 19 70 37 138 276 33 64 128 256), losses := [] }

theorem u3859 : Upper (D 5) (R 5) [18,68,33,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3859
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3860 : Route 9 := (fun mask => (mask,id))

def c3860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3860 : Upper (D 5) (R 5) [18,68,33,130,260,8] 13 := by
  apply FastRouting.sound _ _ [18,68,33,130,260,8] 13 (by decide) (choices 1) [1,8,32] r3860 c3860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1214
  · exact u1215
  · exact u1216

def b3861 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 138 280 33 108 172 300), lower := (rows 19 70 37 138 280 33 64 128 256), losses := [] }

theorem u3861 : Upper (D 5) (R 5) [18,68,33,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3861
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3862 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 37 138 280 36 105 169 297), lower := (rows 19 70 37 138 280 36 64 128 256), losses := [] }

theorem u3862 : Upper (D 5) (R 5) [18,68,33,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3862
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3863 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 70 37 138 280 40 101 165 293), lower := (rows 19 70 37 138 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 69 133 261), good := (rows 501 452 485 168 312 40 64 128 256) }] }

theorem u3863 : Upper (D 5) (R 5) [18,68,33,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3863
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3864 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 140 280 33 106 170 298), lower := (rows 19 70 37 140 280 33 64 128 256), losses := [] }

theorem u3864 : Upper (D 5) (R 5) [18,68,33,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3864
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3865 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 140 280 34 105 169 297), lower := (rows 19 70 37 140 280 34 64 128 256), losses := [] }

theorem u3865 : Upper (D 5) (R 5) [18,68,33,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3865
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3866 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(2,1)], upper := (rows 19 70 37 140 280 40 99 163 291), lower := (rows 19 70 37 140 280 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 16 56 64 128 256), good := (rows 53 68 37 172 312 40 64 128 256) }] }

theorem u3866 : Upper (D 5) (R 5) [18,68,33,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3866
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3867 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 168 276 33 74 138 266), lower := (rows 19 70 37 168 276 33 64 128 256), losses := [] }

theorem u3867 : Upper (D 5) (R 5) [18,68,33,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3867
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3868 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 168 276 34 73 137 265), lower := (rows 19 70 37 168 276 34 64 128 256), losses := [] }

theorem u3868 : Upper (D 5) (R 5) [18,68,33,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3868
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3869 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 37 168 276 40 75 139 267), lower := (rows 19 70 37 168 276 40 64 128 256), losses := [] }

theorem u3869 : Upper (D 5) (R 5) [18,68,33,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3869
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3870 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 202, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 168 280 33 78 142 270), lower := (rows 19 70 37 168 280 33 64 128 256), losses := [] }

theorem u3870 : Upper (D 5) (R 5) [18,68,33,160,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3870
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3871 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 168 280 34 77 141 269), lower := (rows 19 70 37 168 280 34 64 128 256), losses := [] }

theorem u3871 : Upper (D 5) (R 5) [18,68,33,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3871
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3872 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 36, targets := 10 }], pairs := [(2,1),(2,3)], upper := (rows 19 70 37 168 280 36 75 139 267), lower := (rows 19 70 37 168 280 36 64 128 256), losses := [] }

theorem u3872 : Upper (D 5) (R 5) [18,68,33,160,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3872
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3873 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 19 70 37 168 280 40 71 135 263), lower := (rows 19 70 37 168 280 40 64 128 256), losses := [] }

theorem u3873 : Upper (D 5) (R 5) [18,68,33,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3873
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3874 : PairBound 9 := { available := 42, camps := [{ cop := 2, region := 458, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 19 70 37 392 28 33 106 170 298), lower := (rows 19 70 37 392 28 33 64 128 256), losses := [] }

theorem u3874 : Upper (D 5) (R 5) [18,68,33,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3874
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3875 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 408, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 19 70 37 392 28 34 105 169 297), lower := (rows 19 70 37 392 28 34 64 128 256), losses := [] }

theorem u3875 : Upper (D 5) (R 5) [18,68,33,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3875
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3876 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 424, targets := 4 },{ cop := 2, region := 66, targets := 8 }], pairs := [(1,3),(3,2)], upper := (rows 19 70 37 392 28 40 99 163 291), lower := (rows 19 70 37 392 28 40 64 128 256), losses := [] }

theorem u3876 : Upper (D 5) (R 5) [18,68,33,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3876
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3877 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 326, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 41 152 33 332 396 268), lower := (rows 19 70 38 41 152 33 64 128 256), losses := [] }

theorem u3877 : Upper (D 5) (R 5) [18,68,34,33,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3877
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3878 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 41 152 36 329 393 265), lower := (rows 19 70 38 41 152 36 64 128 256), losses := [] }

theorem u3878 : Upper (D 5) (R 5) [18,68,34,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3878
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3879 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 41 152 40 325 389 261), lower := (rows 19 70 38 41 152 40 64 128 256), losses := [] }

theorem u3879 : Upper (D 5) (R 5) [18,68,34,33,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3879
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3880 : Route 9 := (fun mask => (mask,id))

def c3880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3880 : Upper (D 5) (R 5) [18,68,34,33,136,256] 13 := by
  apply FastRouting.sound _ _ [18,68,34,33,136,256] 13 (by decide) (choices 1) [1,4,8] r3880 c3880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1217
  · exact u1218
  · exact u1219

def b3881 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 41 400 33 76 140 268), lower := (rows 19 70 38 41 400 33 64 128 256), losses := [] }

theorem u3881 : Upper (D 5) (R 5) [18,68,34,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3881
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3882 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 41 400 36 73 137 265), lower := (rows 19 70 38 41 400 36 64 128 256), losses := [] }

theorem u3882 : Upper (D 5) (R 5) [18,68,34,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3882
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3883 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 19 70 38 41 400 40 77 141 269), lower := (rows 19 70 38 41 400 40 64 128 256), losses := [] }

theorem u3883 : Upper (D 5) (R 5) [18,68,34,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3883
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3884 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 19 70 38 137 56 33 332 396 268), lower := (rows 19 70 38 137 56 33 64 128 256), losses := [] }

theorem u3884 : Upper (D 5) (R 5) [18,68,34,129,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3884
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3885 : PairBound 9 := { available := 265, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 137 56 36 329 393 265), lower := (rows 19 70 38 137 56 36 64 128 256), losses := [] }

theorem u3885 : Upper (D 5) (R 5) [18,68,34,129,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3885
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b3886 : PairBound 9 := { available := 261, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 38 137 56 40 325 389 261), lower := (rows 19 70 38 137 56 40 64 128 256), losses := [] }

theorem u3886 : Upper (D 5) (R 5) [18,68,34,129,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3886
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3887 : Route 9 := (fun mask => (mask,id))

def c3887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3887 : Upper (D 5) (R 5) [18,68,34,129,40,256] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,40,256] 13 (by decide) (choices 1) [1,4,8] r3887 c3887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1220
  · exact u1221
  · exact u1222

def r3888 : Route 9 := (fun mask => (mask,id))

def c3888 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3888 : Upper (D 5) (R 5) [18,68,34,129,264,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,264,1] 13 (by decide) (choices 1) [4,8,32] r3888 c3888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1223
  · exact u1224
  · exact u1225

def b3889 : PairBound 9 := { available := 41, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 137 280 36 105 169 297), lower := (rows 19 70 38 137 280 36 64 128 256), losses := [] }

theorem u3889 : Upper (D 5) (R 5) [18,68,34,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3889
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3890 : Route 9 := (fun mask => (mask,id))

def c3890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3890 : Upper (D 5) (R 5) [18,68,34,129,264,8] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,264,8] 13 (by decide) (choices 1) [1,4,32] r3890 c3890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1226
  · exact u1227
  · exact u1228

def r3891 : Route 9 := (fun mask => (mask,id))

def c3891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3891 : Upper (D 5) (R 5) [18,68,34,129,288,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,288,1] 13 (by decide) (choices 1) [4,8] r3891 c3891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1229
  · exact u1230

def b3892 : PairBound 9 := { available := 9, camps := [{ cop := 6, region := 38, targets := 9 }], pairs := [(1,0),(1,3)], upper := (rows 19 70 38 137 304 36 73 137 265), lower := (rows 19 70 38 137 304 36 64 128 256), losses := [] }

theorem u3892 : Upper (D 5) (R 5) [18,68,34,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3892
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3893 : Route 9 := (fun mask => (mask,id))

def c3893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3893 : Upper (D 5) (R 5) [18,68,34,129,288,8] 13 := by
  apply FastRouting.sound _ _ [18,68,34,129,288,8] 13 (by decide) (choices 1) [1,4,8] r3893 c3893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1231
  · exact u1232
  · exact u1233

def b3894 : PairBound 9 := { available := 296, camps := [{ cop := 5, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 19 70 38 140 25 33 360 424 296), lower := (rows 19 70 38 140 25 33 64 128 256), losses := [] }

theorem u3894 : Upper (D 5) (R 5) [18,68,34,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3894
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3895 : Route 9 := (fun mask => (mask,id))

def c3895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3895 : Upper (D 5) (R 5) [18,68,34,132,9,8] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,9,8] 13 (by decide) (choices 1) [1,32,256] r3895 c3895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1234
  · exact u1235
  · exact u1236

def r3896 : Route 9 := (fun mask => (mask,id))

def c3896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3896 : Upper (D 5) (R 5) [18,68,34,132,9,256] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,9,256] 13 (by decide) (choices 1) [1,8,32] r3896 c3896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1237
  · exact u1238
  · exact u1239

def r3897 : Route 9 := (fun mask => (mask,id))

def c3897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3897 : Upper (D 5) (R 5) [18,68,34,132,40,1] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,40,1] 13 (by decide) (choices 1) [1,8,256] r3897 c3897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1240
  · exact u1241
  · exact u1242

def b3898 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 19 70 38 140 56 40 321 385 257), lower := (rows 19 70 38 140 56 40 64 128 256), losses := [] }

theorem u3898 : Upper (D 5) (R 5) [18,68,34,132,40,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b3898
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r3899 : Route 9 := (fun mask => (mask,id))

def c3899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3899 : Upper (D 5) (R 5) [18,68,34,132,40,256] 13 := by
  apply FastRouting.sound _ _ [18,68,34,132,40,256] 13 (by decide) (choices 1) [1,8] r3899 c3899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1243
  · exact u1244

#print axioms u3899
end Delivery.IrregularNine14.P05
