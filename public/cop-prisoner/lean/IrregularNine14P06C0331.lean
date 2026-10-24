import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0099

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19860 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 14 276 40 81 209 337), lower := (rows 35 67 164 14 276 40 64 128 256), losses := [] }

theorem u19860 : Upper (D 6) (R 6) [34,65,160,6,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19860 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19861 : Route 9 := (fun mask => (mask,id))

def c19861 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19861 : Upper (D 6) (R 6) [34,65,160,6,260,16] 13 := by
  apply FastRouting.sound _ _ [34,65,160,6,260,16] 13 (by decide) (choices 1) [1,8] r19861 c19861
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5956
  · exact u5957

def b19862 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 14 276 96 89 153 281), lower := (rows 35 67 164 14 276 96 64 128 256), losses := [] }

theorem u19862 : Upper (D 6) (R 6) [34,65,160,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19863 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 14 280 33 84 212 340), lower := (rows 35 67 164 14 280 33 64 128 256), losses := [] }

theorem u19863 : Upper (D 6) (R 6) [34,65,160,6,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19864 : PairBound 9 := { available := 81, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 14 280 36 81 209 337), lower := (rows 35 67 164 14 280 36 64 128 256), losses := [] }

theorem u19864 : Upper (D 6) (R 6) [34,65,160,6,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19865 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 14 280 48 69 197 325), lower := (rows 35 67 164 14 280 48 64 128 256), losses := [{ target := 1, region := (rows 1 0 13 8 24 56 67 131 259), good := (rows 485 453 164 508 316 48 64 128 256) }] }

theorem u19865 : Upper (D 6) (R 6) [34,65,160,6,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19865 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19866 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 14 280 96 85 149 277), lower := (rows 35 67 164 14 280 96 64 128 256), losses := [] }

theorem u19866 : Upper (D 6) (R 6) [34,65,160,6,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19867 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 14 336 33 92 156 284), lower := (rows 35 67 164 14 336 33 64 128 256), losses := [] }

theorem u19867 : Upper (D 6) (R 6) [34,65,160,6,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19868 : PairBound 9 := { available := 25, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 14 336 36 89 153 281), lower := (rows 35 67 164 14 336 36 64 128 256), losses := [] }

theorem u19868 : Upper (D 6) (R 6) [34,65,160,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19869 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 14 336 40 85 149 277), lower := (rows 35 67 164 14 336 40 64 128 256), losses := [] }

theorem u19869 : Upper (D 6) (R 6) [34,65,160,6,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19869 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19870 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 164 14 336 48 77 141 269), lower := (rows 35 67 164 14 336 48 64 128 256), losses := [] }

theorem u19870 : Upper (D 6) (R 6) [34,65,160,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19870 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19871 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 25 84 34 332 396 268), lower := (rows 35 67 164 25 84 34 64 128 256), losses := [] }

theorem u19871 : Upper (D 6) (R 6) [34,65,160,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19872 : PairBound 9 := { available := 266, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 25 84 36 330 394 266), lower := (rows 35 67 164 25 84 36 64 128 256), losses := [] }

theorem u19872 : Upper (D 6) (R 6) [34,65,160,17,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19873 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 164 25 84 40 326 390 262), lower := (rows 35 67 164 25 84 40 64 128 256), losses := [] }

theorem u19873 : Upper (D 6) (R 6) [34,65,160,17,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19873 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19874 : Route 9 := (fun mask => (mask,id))

def c19874 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19874 : Upper (D 6) (R 6) [34,65,160,17,68,256] 13 := by
  apply FastRouting.sound _ _ [34,65,160,17,68,256] 13 (by decide) (choices 1) [2,4,8] r19874 c19874
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5958
  · exact u5959
  · exact u5960

def b19875 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 25 274 36 76 204 332), lower := (rows 35 67 164 25 274 36 64 128 256), losses := [] }

theorem u19875 : Upper (D 6) (R 6) [34,65,160,17,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19876 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 67 164 25 274 40 68 196 324), lower := (rows 35 67 164 25 274 40 64 128 256), losses := [] }

theorem u19876 : Upper (D 6) (R 6) [34,65,160,17,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19876 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19877 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 25 274 96 76 140 268), lower := (rows 35 67 164 25 274 96 64 128 256), losses := [] }

theorem u19877 : Upper (D 6) (R 6) [34,65,160,17,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19878 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 25 276 34 76 204 332), lower := (rows 35 67 164 25 276 34 64 128 256), losses := [] }

theorem u19878 : Upper (D 6) (R 6) [34,65,160,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19879 : PairBound 9 := { available := 74, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 25 276 36 74 202 330), lower := (rows 35 67 164 25 276 36 64 128 256), losses := [] }

theorem u19879 : Upper (D 6) (R 6) [34,65,160,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19880 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 67 164 25 276 40 70 198 326), lower := (rows 35 67 164 25 276 40 64 128 256), losses := [] }

theorem u19880 : Upper (D 6) (R 6) [34,65,160,17,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19880 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19881 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 25 276 96 78 142 270), lower := (rows 35 67 164 25 276 96 64 128 256), losses := [] }

theorem u19881 : Upper (D 6) (R 6) [34,65,160,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19882 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 25 280 34 68 196 324), lower := (rows 35 67 164 25 280 34 64 128 256), losses := [] }

theorem u19882 : Upper (D 6) (R 6) [34,65,160,17,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19883 : PairBound 9 := { available := 70, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 25 280 36 70 198 326), lower := (rows 35 67 164 25 280 36 64 128 256), losses := [] }

theorem u19883 : Upper (D 6) (R 6) [34,65,160,17,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19884 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 25 280 96 70 134 262), lower := (rows 35 67 164 25 280 96 64 128 256), losses := [] }

theorem u19884 : Upper (D 6) (R 6) [34,65,160,17,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19884 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19885 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 25 336 34 76 140 268), lower := (rows 35 67 164 25 336 34 64 128 256), losses := [] }

theorem u19885 : Upper (D 6) (R 6) [34,65,160,17,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19886 : PairBound 9 := { available := 14, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 25 336 36 78 142 270), lower := (rows 35 67 164 25 336 36 64 128 256), losses := [] }

theorem u19886 : Upper (D 6) (R 6) [34,65,160,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19887 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 164 25 336 40 70 134 262), lower := (rows 35 67 164 25 336 40 64 128 256), losses := [] }

theorem u19887 : Upper (D 6) (R 6) [34,65,160,17,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19887 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19888 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 26 28 33 324 452 324), lower := (rows 35 67 164 26 28 33 64 128 256), losses := [] }

theorem u19888 : Upper (D 6) (R 6) [34,65,160,18,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19889 : PairBound 9 := { available := 321, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 28 36 321 449 321), lower := (rows 35 67 164 26 28 36 64 128 256), losses := [] }

theorem u19889 : Upper (D 6) (R 6) [34,65,160,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19890 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 26 28 96 325 389 261), lower := (rows 35 67 164 26 28 96 64 128 256), losses := [] }

theorem u19890 : Upper (D 6) (R 6) [34,65,160,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19891 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 26 28 288 69 197 325), lower := (rows 35 67 164 26 28 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 15 8 24 299 67 131 259), good := (rows 485 485 164 508 60 288 64 128 288) }] }

theorem u19891 : Upper (D 6) (R 6) [34,65,160,18,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19891 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19892 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 26 84 33 332 396 268), lower := (rows 35 67 164 26 84 33 64 128 256), losses := [] }

theorem u19892 : Upper (D 6) (R 6) [34,65,160,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19893 : PairBound 9 := { available := 265, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 84 36 329 393 265), lower := (rows 35 67 164 26 84 36 64 128 256), losses := [] }

theorem u19893 : Upper (D 6) (R 6) [34,65,160,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19894 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 164 26 84 40 325 389 261), lower := (rows 35 67 164 26 84 40 64 128 256), losses := [] }

theorem u19894 : Upper (D 6) (R 6) [34,65,160,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19894 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19895 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 164 26 84 288 77 141 269), lower := (rows 35 67 164 26 84 288 64 128 256), losses := [] }

theorem u19895 : Upper (D 6) (R 6) [34,65,160,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19895 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19896 : PairBound 9 := { available := 76, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 273 36 76 204 332), lower := (rows 35 67 164 26 273 36 64 128 256), losses := [] }

theorem u19896 : Upper (D 6) (R 6) [34,65,160,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19897 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 26 273 40 68 196 324), lower := (rows 35 67 164 26 273 40 64 128 256), losses := [] }

theorem u19897 : Upper (D 6) (R 6) [34,65,160,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19897 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19898 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 26 273 96 76 140 268), lower := (rows 35 67 164 26 273 96 64 128 256), losses := [] }

theorem u19898 : Upper (D 6) (R 6) [34,65,160,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19899 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 26 276 33 76 204 332), lower := (rows 35 67 164 26 276 33 64 128 256), losses := [] }

theorem u19899 : Upper (D 6) (R 6) [34,65,160,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19900 : PairBound 9 := { available := 73, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 276 36 73 201 329), lower := (rows 35 67 164 26 276 36 64 128 256), losses := [] }

theorem u19900 : Upper (D 6) (R 6) [34,65,160,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19901 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 164 26 276 40 69 197 325), lower := (rows 35 67 164 26 276 40 64 128 256), losses := [] }

theorem u19901 : Upper (D 6) (R 6) [34,65,160,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19901 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19902 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 26 276 96 77 141 269), lower := (rows 35 67 164 26 276 96 64 128 256), losses := [] }

theorem u19902 : Upper (D 6) (R 6) [34,65,160,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19903 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 26 280 33 68 196 324), lower := (rows 35 67 164 26 280 33 64 128 256), losses := [] }

theorem u19903 : Upper (D 6) (R 6) [34,65,160,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19904 : PairBound 9 := { available := 69, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 280 36 69 197 325), lower := (rows 35 67 164 26 280 36 64 128 256), losses := [] }

theorem u19904 : Upper (D 6) (R 6) [34,65,160,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19905 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 26 280 96 69 133 261), lower := (rows 35 67 164 26 280 96 64 128 256), losses := [] }

theorem u19905 : Upper (D 6) (R 6) [34,65,160,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19906 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 26 336 33 76 140 268), lower := (rows 35 67 164 26 336 33 64 128 256), losses := [] }

theorem u19906 : Upper (D 6) (R 6) [34,65,160,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19907 : PairBound 9 := { available := 13, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 26 336 36 77 141 269), lower := (rows 35 67 164 26 336 36 64 128 256), losses := [] }

theorem u19907 : Upper (D 6) (R 6) [34,65,160,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19908 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 164 26 336 40 69 133 261), lower := (rows 35 67 164 26 336 40 64 128 256), losses := [] }

theorem u19908 : Upper (D 6) (R 6) [34,65,160,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19908 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19909 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 28 88 33 326 390 262), lower := (rows 35 67 164 28 88 33 64 128 256), losses := [] }

theorem u19909 : Upper (D 6) (R 6) [34,65,160,20,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19910 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 28 88 34 325 389 261), lower := (rows 35 67 164 28 88 34 64 128 256), losses := [] }

theorem u19910 : Upper (D 6) (R 6) [34,65,160,20,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19911 : PairBound 9 := { available := 259, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 28 88 36 323 387 259), lower := (rows 35 67 164 28 88 36 64 128 256), losses := [] }

theorem u19911 : Upper (D 6) (R 6) [34,65,160,20,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19912 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 164 28 88 288 71 135 263), lower := (rows 35 67 164 28 88 288 64 128 256), losses := [] }

theorem u19912 : Upper (D 6) (R 6) [34,65,160,20,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19912 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19913 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 164 28 273 34 76 204 332), lower := (rows 35 67 164 28 273 34 64 128 256), losses := [] }

theorem u19913 : Upper (D 6) (R 6) [34,65,160,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19914 : PairBound 9 := { available := 74, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 28 273 36 74 202 330), lower := (rows 35 67 164 28 273 36 64 128 256), losses := [] }

theorem u19914 : Upper (D 6) (R 6) [34,65,160,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19915 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 196, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 164 28 273 40 70 198 326), lower := (rows 35 67 164 28 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 21 24 16 56 67 131 259), good := (rows 486 454 164 60 508 40 64 128 256) }] }

theorem u19915 : Upper (D 6) (R 6) [34,65,160,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19915 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19916 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 164 28 273 96 78 142 270), lower := (rows 35 67 164 28 273 96 64 128 256), losses := [] }

theorem u19916 : Upper (D 6) (R 6) [34,65,160,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19917 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 164 28 274 33 76 204 332), lower := (rows 35 67 164 28 274 33 64 128 256), losses := [] }

theorem u19917 : Upper (D 6) (R 6) [34,65,160,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19918 : PairBound 9 := { available := 73, camps := [{ cop := 7, region := 36, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 35 67 164 28 274 36 73 201 329), lower := (rows 35 67 164 28 274 36 64 128 256), losses := [] }

theorem u19918 : Upper (D 6) (R 6) [34,65,160,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19919 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 164 28 274 40 69 197 325), lower := (rows 35 67 164 28 274 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 21 24 16 56 67 131 259), good := (rows 485 453 164 60 508 40 64 128 256) }] }

theorem u19919 : Upper (D 6) (R 6) [34,65,160,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19919 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19919
end Delivery.IrregularNine14.P06
