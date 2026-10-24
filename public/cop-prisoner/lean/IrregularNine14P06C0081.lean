import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0006

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 296 21 33 68 194 322), lower := (rows 11 162 84 296 21 33 68 128 256), losses := [] }

theorem u4860 : Upper (D 6) (R 6) [10,160,80,288,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4861 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 84, targets := 2 },{ cop := 0, region := 84, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 162 84 296 21 96 65 134 262), lower := (rows 11 162 84 296 21 96 65 128 256), losses := [] }

theorem u4861 : Upper (D 6) (R 6) [10,160,80,288,5,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4862 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 7, region := 98, targets := 1 }], pairs := [(1,0),(2,5),(4,5)], upper := (rows 11 162 84 296 21 96 66 133 261), lower := (rows 11 162 84 296 21 96 66 128 256), losses := [] }

theorem u4862 : Upper (D 6) (R 6) [10,160,80,288,5,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 296 21 96 68 131 259), lower := (rows 11 162 84 296 21 96 68 128 256), losses := [] }

theorem u4863 : Upper (D 6) (R 6) [10,160,80,288,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4864 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 84 296 22 33 65 196 324), lower := (rows 11 162 84 296 22 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 97 97 132 260), good := (rows 105 224 508 360 412 97 97 128 256) }] }

theorem u4864 : Upper (D 6) (R 6) [10,160,80,288,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4865 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 84 296 22 33 68 193 321), lower := (rows 11 162 84 296 22 33 68 128 256), losses := [] }

theorem u4865 : Upper (D 6) (R 6) [10,160,80,288,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4866 : Route 9 := (fun mask => (mask,id))

def c4866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4866 : Upper (D 6) (R 6) [10,160,80,288,6,64,1] 13 := by
  apply FastRouting.sound _ _ [10,160,80,288,6,64,1] 13 (by decide) (choices 1) [1,4] r4866 c4866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u362
  · exact u363

def b4867 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 395, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 296 22 96 68 129 257), lower := (rows 11 162 84 296 22 96 68 128 256), losses := [] }

theorem u4867 : Upper (D 6) (R 6) [10,160,80,288,6,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 162 84 328 21 33 66 164 292), lower := (rows 11 162 84 328 21 33 66 128 256), losses := [] }

theorem u4868 : Upper (D 6) (R 6) [10,160,80,320,5,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4868 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4869 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 328 21 33 68 162 290), lower := (rows 11 162 84 328 21 33 68 128 256), losses := [] }

theorem u4869 : Upper (D 6) (R 6) [10,160,80,320,5,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4870 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(4,1)], upper := (rows 11 162 84 328 21 33 96 134 262), lower := (rows 11 162 84 328 21 33 96 128 256), losses := [] }

theorem u4870 : Upper (D 6) (R 6) [10,160,80,320,5,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 84, targets := 32 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 162 84 328 22 33 65 164 292), lower := (rows 11 162 84 328 22 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 16 97 97 132 260), good := (rows 105 224 508 360 412 97 97 128 256) }] }

theorem u4871 : Upper (D 6) (R 6) [10,160,80,320,6,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4872 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 11 162 84 328 22 33 68 161 289), lower := (rows 11 162 84 328 22 33 68 128 256), losses := [] }

theorem u4872 : Upper (D 6) (R 6) [10,160,80,320,6,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4872 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4873 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 328 22 33 96 133 261), lower := (rows 11 162 84 328 22 33 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 33 99 128 256), good := (rows 105 224 84 328 84 97 96 128 256) }] }

theorem u4873 : Upper (D 6) (R 6) [10,160,80,320,6,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 162, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 328 49 36 65 134 262), lower := (rows 11 162 84 328 49 36 65 128 256), losses := [] }

theorem u4874 : Upper (D 6) (R 6) [10,160,80,320,33,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0),(2,5),(3,5)], upper := (rows 11 162 84 328 49 36 66 133 261), lower := (rows 11 162 84 328 49 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 52 67 128 256), good := (rows 74 226 116 328 116 36 66 128 256) },{ target := 5, region := (rows 1 2 20 28 16 0 67 144 272), good := (rows 75 194 476 328 477 12 66 128 256) }] }

theorem u4875 : Upper (D 6) (R 6) [10,160,80,320,33,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 130, targets := 4 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 11 162 84 328 49 36 68 131 259), lower := (rows 11 162 84 328 49 36 68 128 256), losses := [] }

theorem u4876 : Upper (D 6) (R 6) [10,160,80,320,33,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 11 162 84 328 52 33 65 134 262), lower := (rows 11 162 84 328 52 33 65 128 256), losses := [] }

theorem u4877 : Upper (D 6) (R 6) [10,160,80,320,36,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4878 : Route 9 := (fun mask => (mask,id))

def c4878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4878 : Upper (D 6) (R 6) [10,160,80,320,36,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,80,320,36,1,2] 13 (by decide) (choices 1) [1,4] r4878 c4878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u364
  · exact u365

def b4879 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 84 328 52 33 68 131 259), lower := (rows 11 162 84 328 52 33 68 128 256), losses := [] }

theorem u4879 : Upper (D 6) (R 6) [10,160,80,320,36,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4880 : PairBound 9 := { available := 20, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 13 82 288 65 148 276), lower := (rows 11 162 100 13 82 288 65 128 256), losses := [] }

theorem u4880 : Upper (D 6) (R 6) [10,160,96,5,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4880 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 84, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 11 162 100 13 82 288 68 145 273), lower := (rows 11 162 100 13 82 288 68 128 256), losses := [] }

theorem u4881 : Upper (D 6) (R 6) [10,160,96,5,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4881 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6)], upper := (rows 11 162 100 13 82 288 80 133 261), lower := (rows 11 162 100 13 82 288 80 128 256), losses := [] }

theorem u4882 : Upper (D 6) (R 6) [10,160,96,5,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4882 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 13 274 48 65 196 324), lower := (rows 11 162 100 13 274 48 65 128 256), losses := [] }

theorem u4883 : Upper (D 6) (R 6) [10,160,96,5,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4883 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 100 13 274 48 68 193 321), lower := (rows 11 162 100 13 274 48 68 128 256), losses := [] }

theorem u4884 : Upper (D 6) (R 6) [10,160,96,5,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4884 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 11 162 100 13 276 48 65 194 322), lower := (rows 11 162 100 13 276 48 65 128 256), losses := [] }

theorem u4885 : Upper (D 6) (R 6) [10,160,96,5,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4885 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(4,5)], upper := (rows 11 162 100 13 276 48 66 193 321), lower := (rows 11 162 100 13 276 48 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 24 0 67 137 265), good := (rows 475 194 68 477 276 16 66 128 256) }] }

theorem u4886 : Upper (D 6) (R 6) [10,160,96,5,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4886 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 25 276 36 65 194 322), lower := (rows 11 162 100 25 276 36 65 128 256), losses := [] }

theorem u4887 : Upper (D 6) (R 6) [10,160,96,17,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 36, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 25 276 36 66 193 321), lower := (rows 11 162 100 25 276 36 66 128 256), losses := [] }

theorem u4888 : Upper (D 6) (R 6) [10,160,96,17,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 100 25 336 36 65 134 262), lower := (rows 11 162 100 25 336 36 65 128 256), losses := [] }

theorem u4889 : Upper (D 6) (R 6) [10,160,96,17,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 36, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 25 336 36 66 133 261), lower := (rows 11 162 100 25 336 36 66 128 256), losses := [] }

theorem u4890 : Upper (D 6) (R 6) [10,160,96,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 100 25 336 36 68 131 259), lower := (rows 11 162 100 25 336 36 68 128 256), losses := [] }

theorem u4891 : Upper (D 6) (R 6) [10,160,96,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4892 : Route 9 := (fun mask => (mask,id))

def c4892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4892 : Upper (D 6) (R 6) [10,160,96,20,257,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,96,20,257,1,2] 13 (by decide) (choices 1) [4,64] r4892 c4892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u366
  · exact u367

def b4893 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 108, targets := 2 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(2,1),(3,1)], upper := (rows 11 162 100 28 273 33 68 194 322), lower := (rows 11 162 100 28 273 33 68 128 256), losses := [] }

theorem u4893 : Upper (D 6) (R 6) [10,160,96,20,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4894 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 28 274 33 65 196 324), lower := (rows 11 162 100 28 274 33 65 128 256), losses := [] }

theorem u4894 : Upper (D 6) (R 6) [10,160,96,20,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4895 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 100 28 274 33 68 193 321), lower := (rows 11 162 100 28 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 127 128 256), good := (rows 78 230 100 92 350 100 68 128 256) }] }

theorem u4895 : Upper (D 6) (R 6) [10,160,96,20,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 28 336 33 65 134 262), lower := (rows 11 162 100 28 336 33 65 128 256), losses := [] }

theorem u4896 : Upper (D 6) (R 6) [10,160,96,20,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 1, region := 68, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 11 162 100 28 336 33 66 133 261), lower := (rows 11 162 100 28 336 33 66 128 256), losses := [] }

theorem u4897 : Upper (D 6) (R 6) [10,160,96,20,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4897 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 100 28 336 33 68 131 259), lower := (rows 11 162 100 28 336 33 68 128 256), losses := [] }

theorem u4898 : Upper (D 6) (R 6) [10,160,96,20,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 73 274 36 65 148 276), lower := (rows 11 162 100 73 274 36 65 128 256), losses := [] }

theorem u4899 : Upper (D 6) (R 6) [10,160,96,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4900 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 100 73 274 36 68 145 273), lower := (rows 11 162 100 73 274 36 68 128 256), losses := [] }

theorem u4900 : Upper (D 6) (R 6) [10,160,96,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4901 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 100 73 274 36 80 133 261), lower := (rows 11 162 100 73 274 36 80 128 256), losses := [] }

theorem u4901 : Upper (D 6) (R 6) [10,160,96,65,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4901 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4902 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 100 73 274 48 65 132 260), lower := (rows 11 162 100 73 274 48 65 128 256), losses := [] }

theorem u4902 : Upper (D 6) (R 6) [10,160,96,65,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4902 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4903 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 100 73 274 48 68 133 261), lower := (rows 11 162 100 73 274 48 68 128 256), losses := [] }

theorem u4903 : Upper (D 6) (R 6) [10,160,96,65,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4903 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 73 276 36 65 146 274), lower := (rows 11 162 100 73 276 36 65 128 256), losses := [] }

theorem u4904 : Upper (D 6) (R 6) [10,160,96,65,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4905 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 73 276 36 66 145 273), lower := (rows 11 162 100 73 276 36 66 128 256), losses := [] }

theorem u4905 : Upper (D 6) (R 6) [10,160,96,65,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4906 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 100 73 276 36 80 131 259), lower := (rows 11 162 100 73 276 36 80 128 256), losses := [] }

theorem u4906 : Upper (D 6) (R 6) [10,160,96,65,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4906 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4907 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 100 73 276 48 65 134 262), lower := (rows 11 162 100 73 276 48 65 128 256), losses := [] }

theorem u4907 : Upper (D 6) (R 6) [10,160,96,65,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4907 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4908 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 162 100 73 276 48 66 133 261), lower := (rows 11 162 100 73 276 48 66 128 256), losses := [] }

theorem u4908 : Upper (D 6) (R 6) [10,160,96,65,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4908 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4909 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 11 162 100 73 276 48 68 131 259), lower := (rows 11 162 100 73 276 48 68 128 256), losses := [] }

theorem u4909 : Upper (D 6) (R 6) [10,160,96,65,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4909 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 130, targets := 65 },{ cop := 4, region := 100, targets := 2 }], pairs := [(1,0),(1,6),(2,1)], upper := (rows 11 162 100 88 273 36 65 134 262), lower := (rows 11 162 100 88 273 36 65 128 256), losses := [] }

theorem u4910 : Upper (D 6) (R 6) [10,160,96,80,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4910 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4911 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 36, targets := 3 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 162 100 88 273 36 66 133 261), lower := (rows 11 162 100 88 273 36 66 128 256), losses := [] }

theorem u4911 : Upper (D 6) (R 6) [10,160,96,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4912 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 100 88 273 36 68 131 259), lower := (rows 11 162 100 88 273 36 68 128 256), losses := [] }

theorem u4912 : Upper (D 6) (R 6) [10,160,96,80,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 88 274 33 65 132 260), lower := (rows 11 162 100 88 274 33 65 128 256), losses := [] }

theorem u4913 : Upper (D 6) (R 6) [10,160,96,80,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 162 100 88 274 33 68 133 261), lower := (rows 11 162 100 88 274 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 38 24 16 32 119 128 256), good := (rows 78 230 100 88 350 100 68 128 256) }] }

theorem u4914 : Upper (D 6) (R 6) [10,160,96,80,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4915 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 73, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 162 100 88 274 36 65 133 261), lower := (rows 11 162 100 88 274 36 65 128 256), losses := [] }

theorem u4915 : Upper (D 6) (R 6) [10,160,96,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4916 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 100 88 274 36 68 129 257), lower := (rows 11 162 100 88 274 36 68 128 256), losses := [] }

theorem u4916 : Upper (D 6) (R 6) [10,160,96,80,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b4917 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 11 162 100 88 276 33 65 134 262), lower := (rows 11 162 100 88 276 33 65 128 256), losses := [] }

theorem u4917 : Upper (D 6) (R 6) [10,160,96,80,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r4918 : Route 9 := (fun mask => (mask,id))

def c4918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4918 : Upper (D 6) (R 6) [10,160,96,80,260,1,2] 13 := by
  apply FastRouting.sound _ _ [10,160,96,80,260,1,2] 13 (by decide) (choices 1) [1,4] r4918 c4918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u368
  · exact u369

def b4919 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 100 88 276 33 68 131 259), lower := (rows 11 162 100 88 276 33 68 128 256), losses := [] }

theorem u4919 : Upper (D 6) (R 6) [10,160,96,80,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b4919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P06
