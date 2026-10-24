import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0116

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22860 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 25 336 36 67 195 323), lower := (rows 35 134 44 25 336 36 64 128 256), losses := [] }

theorem u22860 : Upper (D 6) (R 6) [34,132,40,17,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22861 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 134 44 25 336 96 71 135 263), lower := (rows 35 134 44 25 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 134 44 60 368 96 96 128 256) }] }

theorem u22861 : Upper (D 6) (R 6) [34,132,40,17,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22862 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 450, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 44 26 81 33 324 452 324), lower := (rows 35 134 44 26 81 33 64 128 256), losses := [] }

theorem u22862 : Upper (D 6) (R 6) [34,132,40,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22863 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 26 81 36 321 449 321), lower := (rows 35 134 44 26 81 36 64 128 256), losses := [] }

theorem u22863 : Upper (D 6) (R 6) [34,132,40,18,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22864 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 134 44 26 81 96 325 389 261), lower := (rows 35 134 44 26 81 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 134 44 62 112 96 96 128 256) }] }

theorem u22864 : Upper (D 6) (R 6) [34,132,40,18,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22865 : Route 9 := (fun mask => (mask,id))

def c22865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22865 : Upper (D 6) (R 6) [34,132,40,18,65,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,65,256] 13 (by decide) (choices 1) [1,4] r22865 c22865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7004
  · exact u7005

def b22866 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 26 84 33 321 449 321), lower := (rows 35 134 44 26 84 33 64 128 256), losses := [] }

theorem u22866 : Upper (D 6) (R 6) [34,132,40,18,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22867 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 387, targets := 64 },{ cop := 1, region := 353, targets := 4 }], pairs := [(0,2),(0,6),(1,6)], upper := (rows 35 134 44 26 84 96 321 385 257), lower := (rows 35 134 44 26 84 96 64 128 256), losses := [] }

theorem u22867 : Upper (D 6) (R 6) [34,132,40,18,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22868 : Route 9 := (fun mask => (mask,id))

def c22868 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22868 : Upper (D 6) (R 6) [34,132,40,18,68,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,68,256] 13 (by decide) (choices 1) [1] r22868 c22868
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7006

def b22869 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 2, region := 194, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 134 44 26 273 33 68 196 324), lower := (rows 35 134 44 26 273 33 64 128 256), losses := [] }

theorem u22869 : Upper (D 6) (R 6) [34,132,40,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22870 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 26 273 36 65 193 321), lower := (rows 35 134 44 26 273 36 64 128 256), losses := [] }

theorem u22870 : Upper (D 6) (R 6) [34,132,40,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22871 : Route 9 := (fun mask => (mask,id))

def c22871 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22871 : Upper (D 6) (R 6) [34,132,40,18,257,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,257,64] 13 (by decide) (choices 1) [1,4] r22871 c22871
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7007
  · exact u7008

def b22872 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 37, targets := 64 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 26 276 33 65 193 321), lower := (rows 35 134 44 26 276 33 64 128 256), losses := [] }

theorem u22872 : Upper (D 6) (R 6) [34,132,40,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22873 : Route 9 := (fun mask => (mask,id))

def c22873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22873 : Upper (D 6) (R 6) [34,132,40,18,260,64] 13 := by
  apply FastRouting.sound _ _ [34,132,40,18,260,64] 13 (by decide) (choices 1) [1] r22873 c22873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u7009

def b22874 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 26 336 33 69 197 325), lower := (rows 35 134 44 26 336 33 64 128 256), losses := [] }

theorem u22874 : Upper (D 6) (R 6) [34,132,40,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22875 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 26 336 36 65 193 321), lower := (rows 35 134 44 26 336 36 64 128 256), losses := [] }

theorem u22875 : Upper (D 6) (R 6) [34,132,40,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22876 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 134 44 26 336 96 69 133 261), lower := (rows 35 134 44 26 336 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 112 64 128 256), good := (rows 34 134 44 62 368 96 96 128 256) }] }

theorem u22876 : Upper (D 6) (R 6) [34,132,40,18,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22877 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 73 82 33 340 404 276), lower := (rows 35 134 44 73 82 33 64 128 256), losses := [] }

theorem u22877 : Upper (D 6) (R 6) [34,132,40,65,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22878 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 73 82 36 337 401 273), lower := (rows 35 134 44 73 82 36 64 128 256), losses := [] }

theorem u22878 : Upper (D 6) (R 6) [34,132,40,65,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22879 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 73 82 48 325 389 261), lower := (rows 35 134 44 73 82 48 64 128 256), losses := [] }

theorem u22879 : Upper (D 6) (R 6) [34,132,40,65,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22879 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22880 : Route 9 := (fun mask => (mask,id))

def c22880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22880 : Upper (D 6) (R 6) [34,132,40,65,66,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,65,66,256] 13 (by decide) (choices 1) [1,4,16] r22880 c22880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7010
  · exact u7011
  · exact u7012

def b22881 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 73 84 33 338 402 274), lower := (rows 35 134 44 73 84 33 64 128 256), losses := [] }

theorem u22881 : Upper (D 6) (R 6) [34,132,40,65,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22881 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22882 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 73 84 34 337 401 273), lower := (rows 35 134 44 73 84 34 64 128 256), losses := [] }

theorem u22882 : Upper (D 6) (R 6) [34,132,40,65,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22883 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 44 73 84 48 323 387 259), lower := (rows 35 134 44 73 84 48 64 128 256), losses := [] }

theorem u22883 : Upper (D 6) (R 6) [34,132,40,65,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22883 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22884 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 73 84 288 83 147 275), lower := (rows 35 134 44 73 84 288 64 128 256), losses := [] }

theorem u22884 : Upper (D 6) (R 6) [34,132,40,65,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22884 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22885 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 73 273 34 84 212 340), lower := (rows 35 134 44 73 273 34 64 128 256), losses := [] }

theorem u22885 : Upper (D 6) (R 6) [34,132,40,65,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22886 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 73 273 36 82 210 338), lower := (rows 35 134 44 73 273 36 64 128 256), losses := [] }

theorem u22886 : Upper (D 6) (R 6) [34,132,40,65,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22887 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 194, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 134 44 73 273 48 70 198 326), lower := (rows 35 134 44 73 273 48 64 128 256), losses := [] }

theorem u22887 : Upper (D 6) (R 6) [34,132,40,65,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22887 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22888 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 73 273 96 86 150 278), lower := (rows 35 134 44 73 273 96 64 128 256), losses := [] }

theorem u22888 : Upper (D 6) (R 6) [34,132,40,65,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22889 : PairBound 9 := { available := 84, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 73 274 33 84 212 340), lower := (rows 35 134 44 73 274 33 64 128 256), losses := [] }

theorem u22889 : Upper (D 6) (R 6) [34,132,40,65,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22890 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 73 274 36 81 209 337), lower := (rows 35 134 44 73 274 36 64 128 256), losses := [] }

theorem u22890 : Upper (D 6) (R 6) [34,132,40,65,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22891 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 134 44 73 274 48 69 197 325), lower := (rows 35 134 44 73 274 48 64 128 256), losses := [] }

theorem u22891 : Upper (D 6) (R 6) [34,132,40,65,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22891 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22892 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 73 274 96 85 149 277), lower := (rows 35 134 44 73 274 96 64 128 256), losses := [] }

theorem u22892 : Upper (D 6) (R 6) [34,132,40,65,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22893 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 73 276 33 82 210 338), lower := (rows 35 134 44 73 276 33 64 128 256), losses := [] }

theorem u22893 : Upper (D 6) (R 6) [34,132,40,65,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22894 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 73 276 34 81 209 337), lower := (rows 35 134 44 73 276 34 64 128 256), losses := [] }

theorem u22894 : Upper (D 6) (R 6) [34,132,40,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22895 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 73 276 48 67 195 323), lower := (rows 35 134 44 73 276 48 64 128 256), losses := [] }

theorem u22895 : Upper (D 6) (R 6) [34,132,40,65,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22895 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22896 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 73 276 96 83 147 275), lower := (rows 35 134 44 73 276 96 64 128 256), losses := [] }

theorem u22896 : Upper (D 6) (R 6) [34,132,40,65,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22897 : PairBound 9 := { available := 22, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 134 44 73 336 33 86 150 278), lower := (rows 35 134 44 73 336 33 64 128 256), losses := [] }

theorem u22897 : Upper (D 6) (R 6) [34,132,40,65,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22898 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 134 44 73 336 34 85 149 277), lower := (rows 35 134 44 73 336 34 64 128 256), losses := [] }

theorem u22898 : Upper (D 6) (R 6) [34,132,40,65,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22899 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 73 336 36 83 147 275), lower := (rows 35 134 44 73 336 36 64 128 256), losses := [] }

theorem u22899 : Upper (D 6) (R 6) [34,132,40,65,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22900 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 73 336 48 71 135 263), lower := (rows 35 134 44 73 336 48 64 128 256), losses := [] }

theorem u22900 : Upper (D 6) (R 6) [34,132,40,65,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22900 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22901 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 134 44 74 21 33 336 464 336), lower := (rows 35 134 44 74 21 33 64 128 256), losses := [] }

theorem u22901 : Upper (D 6) (R 6) [34,132,40,66,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22902 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 134 44 74 21 48 321 449 321), lower := (rows 35 134 44 74 21 48 64 128 256), losses := [] }

theorem u22902 : Upper (D 6) (R 6) [34,132,40,66,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22902 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22903 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 74 21 96 337 401 273), lower := (rows 35 134 44 74 21 96 64 128 256), losses := [] }

theorem u22903 : Upper (D 6) (R 6) [34,132,40,66,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22904 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5),(3,5)], upper := (rows 35 134 44 74 21 288 81 209 337), lower := (rows 35 134 44 74 21 288 64 128 256), losses := [] }

theorem u22904 : Upper (D 6) (R 6) [34,132,40,66,5,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22904 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22905 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 49, targets := 4 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 134 44 74 81 33 340 404 276), lower := (rows 35 134 44 74 81 33 64 128 256), losses := [] }

theorem u22905 : Upper (D 6) (R 6) [34,132,40,66,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22906 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 74 81 36 337 401 273), lower := (rows 35 134 44 74 81 36 64 128 256), losses := [] }

theorem u22906 : Upper (D 6) (R 6) [34,132,40,66,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22907 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 74 81 48 325 389 261), lower := (rows 35 134 44 74 81 48 64 128 256), losses := [] }

theorem u22907 : Upper (D 6) (R 6) [34,132,40,66,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22907 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22908 : Route 9 := (fun mask => (mask,id))

def c22908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22908 : Upper (D 6) (R 6) [34,132,40,66,65,256] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,65,256] 13 (by decide) (choices 1) [1,4,16] r22908 c22908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7013
  · exact u7014
  · exact u7015

def b22909 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 74 84 33 337 401 273), lower := (rows 35 134 44 74 84 33 64 128 256), losses := [] }

theorem u22909 : Upper (D 6) (R 6) [34,132,40,66,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22910 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 52, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 134 44 74 84 48 321 385 257), lower := (rows 35 134 44 74 84 48 64 128 256), losses := [] }

theorem u22910 : Upper (D 6) (R 6) [34,132,40,66,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22910 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22911 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 134 44 74 84 288 81 145 273), lower := (rows 35 134 44 74 84 288 64 128 256), losses := [] }

theorem u22911 : Upper (D 6) (R 6) [34,132,40,66,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22911 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22912 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 74 273 33 84 212 340), lower := (rows 35 134 44 74 273 33 64 128 256), losses := [] }

theorem u22912 : Upper (D 6) (R 6) [34,132,40,66,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22913 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 344, targets := 36 }], pairs := [(3,2),(3,5),(4,2)], upper := (rows 35 134 44 74 273 36 81 209 337), lower := (rows 35 134 44 74 273 36 64 128 256), losses := [] }

theorem u22913 : Upper (D 6) (R 6) [34,132,40,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r22914 : Route 9 := (fun mask => (mask,id))

def c22914 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22914 : Upper (D 6) (R 6) [34,132,40,66,257,16] 13 := by
  apply FastRouting.sound _ _ [34,132,40,66,257,16] 13 (by decide) (choices 1) [1,4] r22914 c22914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u7016
  · exact u7017

def b22915 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 74 273 96 85 149 277), lower := (rows 35 134 44 74 273 96 64 128 256), losses := [] }

theorem u22915 : Upper (D 6) (R 6) [34,132,40,66,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22916 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 74 276 33 81 209 337), lower := (rows 35 134 44 74 276 33 64 128 256), losses := [] }

theorem u22916 : Upper (D 6) (R 6) [34,132,40,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22917 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 72, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 134 44 74 276 48 65 193 321), lower := (rows 35 134 44 74 276 48 64 128 256), losses := [] }

theorem u22917 : Upper (D 6) (R 6) [34,132,40,66,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22918 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 134 44 74 276 96 81 145 273), lower := (rows 35 134 44 74 276 96 64 128 256), losses := [] }

theorem u22918 : Upper (D 6) (R 6) [34,132,40,66,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b22919 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 37, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 134 44 74 336 33 85 149 277), lower := (rows 35 134 44 74 336 33 64 128 256), losses := [] }

theorem u22919 : Upper (D 6) (R 6) [34,132,40,66,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b22919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u22919
end Delivery.IrregularNine14.P06
