import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0018
import IrregularNine14P06C0019

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9840 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 80, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 140 296 82 36 81 209 337), lower := (rows 7 35 140 296 82 36 64 128 256), losses := [] }

theorem u9840 : Upper (D 6) (R 6) [6,33,136,288,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9840
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9841 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 296 82 48 69 197 325), lower := (rows 7 35 140 296 82 48 64 128 256), losses := [] }

theorem u9841 : Upper (D 6) (R 6) [6,33,136,288,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9842 : Route 9 := (fun mask => (mask,id))

def c9842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9842 : Upper (D 6) (R 6) [6,33,136,288,66,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,66,64] 13 (by decide) (choices 1) [1,4,16] r9842 c9842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1139
  · exact u1140
  · exact u1141

def b9843 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 296 84 33 82 210 338), lower := (rows 7 35 140 296 84 33 64 128 256), losses := [] }

theorem u9843 : Upper (D 6) (R 6) [6,33,136,288,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9843
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9844 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 296 84 34 81 209 337), lower := (rows 7 35 140 296 84 34 64 128 256), losses := [] }

theorem u9844 : Upper (D 6) (R 6) [6,33,136,288,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9844
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9845 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 296 84 48 67 195 323), lower := (rows 7 35 140 296 84 48 64 128 256), losses := [] }

theorem u9845 : Upper (D 6) (R 6) [6,33,136,288,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9845
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9846 : Route 9 := (fun mask => (mask,id))

def c9846 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9846 : Upper (D 6) (R 6) [6,33,136,288,68,64] 13 := by
  apply FastRouting.sound _ _ [6,33,136,288,68,64] 13 (by decide) (choices 1) [1,2,16] r9846 c9846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1142
  · exact u1143
  · exact u1144

def b9847 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 328 52 33 82 210 338), lower := (rows 7 35 140 328 52 33 64 128 256), losses := [] }

theorem u9847 : Upper (D 6) (R 6) [6,33,136,320,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9847
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9848 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 328 52 34 81 209 337), lower := (rows 7 35 140 328 52 34 64 128 256), losses := [] }

theorem u9848 : Upper (D 6) (R 6) [6,33,136,320,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9848
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9849 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 328 52 48 67 195 323), lower := (rows 7 35 140 328 52 48 64 128 256), losses := [] }

theorem u9849 : Upper (D 6) (R 6) [6,33,136,320,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9849
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9850 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 3, targets := 64 }], pairs := [(0,6),(1,6),(4,0)], upper := (rows 7 35 140 328 52 96 83 147 275), lower := (rows 7 35 140 328 52 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 104 64 128 256), good := (rows 22 34 188 360 52 96 96 128 256) }] }

theorem u9850 : Upper (D 6) (R 6) [6,33,136,320,36,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9851 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 328 81 34 116 180 308), lower := (rows 7 35 140 328 81 34 64 128 256), losses := [] }

theorem u9851 : Upper (D 6) (R 6) [6,33,136,320,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9851
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9852 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 328 81 36 114 178 306), lower := (rows 7 35 140 328 81 36 64 128 256), losses := [] }

theorem u9852 : Upper (D 6) (R 6) [6,33,136,320,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9852
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9853 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 140 328 81 48 102 166 294), lower := (rows 7 35 140 328 81 48 64 128 256), losses := [] }

theorem u9853 : Upper (D 6) (R 6) [6,33,136,320,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9853
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9854 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 328 82 33 116 180 308), lower := (rows 7 35 140 328 82 33 64 128 256), losses := [] }

theorem u9854 : Upper (D 6) (R 6) [6,33,136,320,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9854
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9855 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 328 82 36 113 177 305), lower := (rows 7 35 140 328 82 36 64 128 256), losses := [] }

theorem u9855 : Upper (D 6) (R 6) [6,33,136,320,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9855
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9856 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 140 328 82 48 101 165 293), lower := (rows 7 35 140 328 82 48 64 128 256), losses := [] }

theorem u9856 : Upper (D 6) (R 6) [6,33,136,320,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9856
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9857 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 328 84 33 114 178 306), lower := (rows 7 35 140 328 84 33 64 128 256), losses := [] }

theorem u9857 : Upper (D 6) (R 6) [6,33,136,320,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9858 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 328 84 34 113 177 305), lower := (rows 7 35 140 328 84 34 64 128 256), losses := [] }

theorem u9858 : Upper (D 6) (R 6) [6,33,136,320,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9858
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9859 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 140 328 84 48 99 163 291), lower := (rows 7 35 140 328 84 48 64 128 256), losses := [] }

theorem u9859 : Upper (D 6) (R 6) [6,33,136,320,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9859
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9860 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 140 328 112 33 86 150 278), lower := (rows 7 35 140 328 112 33 64 128 256), losses := [] }

theorem u9860 : Upper (D 6) (R 6) [6,33,136,320,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9860
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9861 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 140 328 112 34 85 149 277), lower := (rows 7 35 140 328 112 34 64 128 256), losses := [] }

theorem u9861 : Upper (D 6) (R 6) [6,33,136,320,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9861
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9862 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 140 328 112 36 83 147 275), lower := (rows 7 35 140 328 112 36 64 128 256), losses := [] }

theorem u9862 : Upper (D 6) (R 6) [6,33,136,320,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9862
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9863 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 140 328 112 48 71 135 263), lower := (rows 7 35 140 328 112 48 64 128 256), losses := [] }

theorem u9863 : Upper (D 6) (R 6) [6,33,136,320,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9864 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 25 82 36 360 424 296), lower := (rows 7 35 196 25 82 36 64 128 256), losses := [] }

theorem u9864 : Upper (D 6) (R 6) [6,33,192,17,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9864
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9865 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 25 82 40 356 420 292), lower := (rows 7 35 196 25 82 40 64 128 256), losses := [] }

theorem u9865 : Upper (D 6) (R 6) [6,33,192,17,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9865
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9866 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 25 82 288 108 172 300), lower := (rows 7 35 196 25 82 288 64 128 256), losses := [] }

theorem u9866 : Upper (D 6) (R 6) [6,33,192,17,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9866
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9867 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 25 112 34 332 396 268), lower := (rows 7 35 196 25 112 34 64 128 256), losses := [] }

theorem u9867 : Upper (D 6) (R 6) [6,33,192,17,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9867
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9868 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 196 25 112 36 330 394 266), lower := (rows 7 35 196 25 112 36 64 128 256), losses := [] }

theorem u9868 : Upper (D 6) (R 6) [6,33,192,17,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9869 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 25 112 40 326 390 262), lower := (rows 7 35 196 25 112 40 64 128 256), losses := [] }

theorem u9869 : Upper (D 6) (R 6) [6,33,192,17,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9870 : Route 9 := (fun mask => (mask,id))

def c9870 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9870 : Upper (D 6) (R 6) [6,33,192,17,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,96,256] 13 (by decide) (choices 1) [2,4,8] r9870 c9870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1145
  · exact u1146
  · exact u1147

def b9871 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 25 274 36 104 232 360), lower := (rows 7 35 196 25 274 36 64 128 256), losses := [] }

theorem u9871 : Upper (D 6) (R 6) [6,33,192,17,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9871
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9872 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 25 274 40 100 228 356), lower := (rows 7 35 196 25 274 40 64 128 256), losses := [] }

theorem u9872 : Upper (D 6) (R 6) [6,33,192,17,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9872
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9873 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 196 25 274 96 108 172 300), lower := (rows 7 35 196 25 274 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 27 274 96 96 128 256) }] }

theorem u9873 : Upper (D 6) (R 6) [6,33,192,17,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9873
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9874 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 25 276 34 104 232 360), lower := (rows 7 35 196 25 276 34 64 128 256), losses := [] }

theorem u9874 : Upper (D 6) (R 6) [6,33,192,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9874
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9875 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 25 276 40 98 226 354), lower := (rows 7 35 196 25 276 40 64 128 256), losses := [] }

theorem u9875 : Upper (D 6) (R 6) [6,33,192,17,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9875
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9876 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 98, targets := 4 }], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 25 276 96 106 170 298), lower := (rows 7 35 196 25 276 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 11 17 32 0 130 258), good := (rows 415 443 132 25 276 32 0 128 256) }] }

theorem u9876 : Upper (D 6) (R 6) [6,33,192,17,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9876
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9877 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 25 280 34 100 228 356), lower := (rows 7 35 196 25 280 34 64 128 256), losses := [] }

theorem u9877 : Upper (D 6) (R 6) [6,33,192,17,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9878 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 25 280 36 98 226 354), lower := (rows 7 35 196 25 280 36 64 128 256), losses := [] }

theorem u9878 : Upper (D 6) (R 6) [6,33,192,17,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9879 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 228, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 196 25 280 96 102 166 294), lower := (rows 7 35 196 25 280 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 111 67 131 259), good := (rows 486 486 228 508 316 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 27 280 96 96 128 256) }] }

theorem u9879 : Upper (D 6) (R 6) [6,33,192,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9879
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9880 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 25 304 34 76 204 332), lower := (rows 7 35 196 25 304 34 64 128 256), losses := [] }

theorem u9880 : Upper (D 6) (R 6) [6,33,192,17,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9880
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9881 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 25 304 36 74 202 330), lower := (rows 7 35 196 25 304 36 64 128 256), losses := [] }

theorem u9881 : Upper (D 6) (R 6) [6,33,192,17,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9881
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9882 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 25 304 40 70 198 326), lower := (rows 7 35 196 25 304 40 64 128 256), losses := [] }

theorem u9882 : Upper (D 6) (R 6) [6,33,192,17,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9882
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9883 : PairBound 9 := { available := 14, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 25 304 96 78 142 270), lower := (rows 7 35 196 25 304 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 27 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 11 18 32 0 129 257), good := (rows 415 443 132 409 304 32 0 128 256) }] }

theorem u9883 : Upper (D 6) (R 6) [6,33,192,17,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9884 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 196 25 336 34 108 172 300), lower := (rows 7 35 196 25 336 34 64 128 256), losses := [] }

theorem u9884 : Upper (D 6) (R 6) [6,33,192,17,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9885 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 25 336 36 106 170 298), lower := (rows 7 35 196 25 336 36 64 128 256), losses := [] }

theorem u9885 : Upper (D 6) (R 6) [6,33,192,17,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9886 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 196 25 336 40 102 166 294), lower := (rows 7 35 196 25 336 40 64 128 256), losses := [] }

theorem u9886 : Upper (D 6) (R 6) [6,33,192,17,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9886
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9887 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 26 81 36 360 424 296), lower := (rows 7 35 196 26 81 36 64 128 256), losses := [] }

theorem u9887 : Upper (D 6) (R 6) [6,33,192,18,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9887
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9888 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 26 81 40 356 420 292), lower := (rows 7 35 196 26 81 40 64 128 256), losses := [] }

theorem u9888 : Upper (D 6) (R 6) [6,33,192,18,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9889 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 484, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 26 81 288 108 172 300), lower := (rows 7 35 196 26 81 288 64 128 256), losses := [] }

theorem u9889 : Upper (D 6) (R 6) [6,33,192,18,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9890 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 26 112 33 332 396 268), lower := (rows 7 35 196 26 112 33 64 128 256), losses := [] }

theorem u9890 : Upper (D 6) (R 6) [6,33,192,18,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9890
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9891 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 196 26 112 36 329 393 265), lower := (rows 7 35 196 26 112 36 64 128 256), losses := [] }

theorem u9891 : Upper (D 6) (R 6) [6,33,192,18,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9891
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9892 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 35 196 26 112 40 325 389 261), lower := (rows 7 35 196 26 112 40 64 128 256), losses := [] }

theorem u9892 : Upper (D 6) (R 6) [6,33,192,18,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9892
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9893 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 196 26 112 288 77 141 269), lower := (rows 7 35 196 26 112 288 64 128 256), losses := [] }

theorem u9893 : Upper (D 6) (R 6) [6,33,192,18,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9893
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9894 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 344, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 196 26 273 36 104 232 360), lower := (rows 7 35 196 26 273 36 64 128 256), losses := [] }

theorem u9894 : Upper (D 6) (R 6) [6,33,192,18,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9894
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9895 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 42, targets := 68 }], pairs := [(1,2),(1,6)], upper := (rows 7 35 196 26 273 40 100 228 356), lower := (rows 7 35 196 26 273 40 64 128 256), losses := [] }

theorem u9895 : Upper (D 6) (R 6) [6,33,192,18,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9895
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9896 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 228, targets := 3 }], pairs := [(1,2),(2,0),(2,1)], upper := (rows 7 35 196 26 273 96 108 172 300), lower := (rows 7 35 196 26 273 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 24 16 100 64 128 256), good := (rows 35 35 224 26 283 96 96 128 256) }] }

theorem u9896 : Upper (D 6) (R 6) [6,33,192,18,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9896
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9897 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 26 276 33 104 232 360), lower := (rows 7 35 196 26 276 33 64 128 256), losses := [] }

theorem u9897 : Upper (D 6) (R 6) [6,33,192,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9897
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9898 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 26 276 40 97 225 353), lower := (rows 7 35 196 26 276 40 64 128 256), losses := [] }

theorem u9898 : Upper (D 6) (R 6) [6,33,192,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9898
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9899 : PairBound 9 := { available := 41, camps := [], pairs := [(1,2),(3,6),(4,6)], upper := (rows 7 35 196 26 276 96 105 169 297), lower := (rows 7 35 196 26 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 224 26 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 11 17 32 0 130 258), good := (rows 415 443 132 410 276 32 0 128 256) }] }

theorem u9899 : Upper (D 6) (R 6) [6,33,192,18,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9899
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9899
end Delivery.IrregularNine14.P06
