import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0006

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4860 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 440, targets := 1 },{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5),(3,0),(4,0)], upper := (rows 35 67 13 392 112 160 68 146 274), lower := (rows 35 67 13 392 112 160 68 128 256), losses := [] }

theorem u4860 : Upper (D 7) (R 7) [34,65,9,384,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4860 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4861 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 67 13 392 112 160 80 134 262), lower := (rows 35 67 13 392 112 160 80 128 256), losses := [] }

theorem u4861 : Upper (D 7) (R 7) [34,65,9,384,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4861 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4862 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 67 13 392 146 36 80 224 352), lower := (rows 35 67 13 392 146 36 80 128 256), losses := [] }

theorem u4862 : Upper (D 7) (R 7) [34,65,9,384,130,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4862 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4863 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 392 146 36 96 208 336), lower := (rows 35 67 13 392 146 36 96 128 256), losses := [] }

theorem u4863 : Upper (D 7) (R 7) [34,65,9,384,130,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4863 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4864 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 13 392 208 36 66 176 304), lower := (rows 35 67 13 392 208 36 66 128 256), losses := [] }

theorem u4864 : Upper (D 7) (R 7) [34,65,9,384,192,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4864 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4865 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 13 392 208 36 80 162 290), lower := (rows 35 67 13 392 208 36 80 128 256), losses := [] }

theorem u4865 : Upper (D 7) (R 7) [34,65,9,384,192,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4865 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4866 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 13 392 208 36 96 146 274), lower := (rows 35 67 13 392 208 36 96 128 256), losses := [] }

theorem u4866 : Upper (D 7) (R 7) [34,65,9,384,192,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4866 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4867 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 44 336 160 65 130 386), lower := (rows 35 67 28 44 336 160 65 128 256), losses := [] }

theorem u4867 : Upper (D 7) (R 7) [34,65,24,36,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4868 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 44 336 160 66 129 385), lower := (rows 35 67 28 44 336 160 66 128 256), losses := [] }

theorem u4868 : Upper (D 7) (R 7) [34,65,24,36,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4869 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 1, region := 161, targets := 64 },{ cop := 1, region := 272, targets := 128 }], pairs := [(0,6),(1,5),(4,5),(4,7)], upper := (rows 35 67 28 44 336 160 192 131 259), lower := (rows 35 67 28 44 336 160 192 128 256), losses := [] }

theorem u4869 : Upper (D 7) (R 7) [34,65,24,36,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4870 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 145 160 66 388 260), lower := (rows 35 67 28 104 145 160 66 128 256), losses := [] }

theorem u4870 : Upper (D 7) (R 7) [34,65,24,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4871 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 28 104 145 160 68 386 258), lower := (rows 35 67 28 104 145 160 68 128 256), losses := [] }

theorem u4871 : Upper (D 7) (R 7) [34,65,24,96,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4871 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4872 : Route 9 := (fun mask => (mask,id))

def c4872 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4872 : Upper (D 7) (R 7) [34,65,24,96,129,128,256] 13 := by
  apply FastRouting.sound _ _ [34,65,24,96,129,128,256] 13 (by decide) (choices 1) [2,4] r4872 c4872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u376
  · exact u377

def b4873 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 145 288 66 132 388), lower := (rows 35 67 28 104 145 288 66 128 256), losses := [] }

theorem u4873 : Upper (D 7) (R 7) [34,65,24,96,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4873 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4874 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 67 28 104 145 288 68 130 386), lower := (rows 35 67 28 104 145 288 68 128 256), losses := [] }

theorem u4874 : Upper (D 7) (R 7) [34,65,24,96,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4874 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4875 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 3, targets := 128 },{ cop := 4, region := 66, targets := 32 }], pairs := [(0,7),(1,5),(1,7)], upper := (rows 35 67 28 104 145 288 192 134 262), lower := (rows 35 67 28 104 145 288 192 128 256), losses := [] }

theorem u4875 : Upper (D 7) (R 7) [34,65,24,96,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4875 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4876 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 273 160 66 132 388), lower := (rows 35 67 28 104 273 160 66 128 256), losses := [] }

theorem u4876 : Upper (D 7) (R 7) [34,65,24,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4877 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 3, region := 3, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 67 28 104 273 160 68 130 386), lower := (rows 35 67 28 104 273 160 68 128 256), losses := [] }

theorem u4877 : Upper (D 7) (R 7) [34,65,24,96,257,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4877 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4878 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 67 28 104 273 160 192 134 262), lower := (rows 35 67 28 104 273 160 192 128 256), losses := [] }

theorem u4878 : Upper (D 7) (R 7) [34,65,24,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4879 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 104 400 33 192 134 262), lower := (rows 35 67 28 104 400 33 192 128 256), losses := [] }

theorem u4879 : Upper (D 7) (R 7) [34,65,24,96,384,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4880 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 6, region := 35, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 104 400 34 192 133 261), lower := (rows 35 67 28 104 400 34 192 128 256), losses := [] }

theorem u4880 : Upper (D 7) (R 7) [34,65,24,96,384,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4881 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 28 104 400 36 192 131 259), lower := (rows 35 67 28 104 400 36 192 128 256), losses := [] }

theorem u4881 : Upper (D 7) (R 7) [34,65,24,96,384,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4881 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4882 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 28 137 146 36 320 224 352), lower := (rows 35 67 28 137 146 36 320 128 256), losses := [] }

theorem u4882 : Upper (D 7) (R 7) [34,65,24,129,130,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4882 [(5,2),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4883 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 28 137 146 96 320 164 292), lower := (rows 35 67 28 137 146 96 320 128 256), losses := [] }

theorem u4883 : Upper (D 7) (R 7) [34,65,24,129,130,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4883 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4884 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 176 288 66 196 324), lower := (rows 35 67 28 137 176 288 66 128 256), losses := [] }

theorem u4884 : Upper (D 7) (R 7) [34,65,24,129,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4884 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4885 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 28 137 176 288 68 194 322), lower := (rows 35 67 28 137 176 288 68 128 256), losses := [] }

theorem u4885 : Upper (D 7) (R 7) [34,65,24,129,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4885 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4886 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 208 288 66 164 292), lower := (rows 35 67 28 137 208 288 66 128 256), losses := [] }

theorem u4886 : Upper (D 7) (R 7) [34,65,24,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4886 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4887 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 28 137 208 288 68 162 290), lower := (rows 35 67 28 137 208 288 68 128 256), losses := [] }

theorem u4887 : Upper (D 7) (R 7) [34,65,24,129,192,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4887 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4888 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 67 28 137 208 288 96 134 262), lower := (rows 35 67 28 137 208 288 96 128 256), losses := [] }

theorem u4888 : Upper (D 7) (R 7) [34,65,24,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4888 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4889 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 432, targets := 1 },{ cop := 1, region := 168, targets := 2 }], pairs := [(2,0),(3,1),(4,0)], upper := (rows 35 67 28 137 274 160 68 224 352), lower := (rows 35 67 28 137 274 160 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 76 206 334), good := (rows 434 498 508 508 434 160 484 160 256) }] }

theorem u4889 : Upper (D 7) (R 7) [34,65,24,129,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4889 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4890 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 28 137 274 160 96 196 324), lower := (rows 35 67 28 137 274 160 96 128 256), losses := [] }

theorem u4890 : Upper (D 7) (R 7) [34,65,24,129,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4891 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 304 160 66 196 324), lower := (rows 35 67 28 137 304 160 66 128 256), losses := [] }

theorem u4891 : Upper (D 7) (R 7) [34,65,24,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4892 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 432, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(2,0),(3,5),(4,0)], upper := (rows 35 67 28 137 304 160 68 194 322), lower := (rows 35 67 28 137 304 160 68 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 171 76 130 258), good := (rows 434 498 124 252 304 160 68 160 256) }] }

theorem u4892 : Upper (D 7) (R 7) [34,65,24,129,288,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4892 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4893 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,1),(3,1),(4,1)], upper := (rows 35 67 28 137 336 160 66 164 292), lower := (rows 35 67 28 137 336 160 66 128 256), losses := [] }

theorem u4893 : Upper (D 7) (R 7) [34,65,24,129,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4893 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4894 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 67 28 137 336 160 68 162 290), lower := (rows 35 67 28 137 336 160 68 128 256), losses := [] }

theorem u4894 : Upper (D 7) (R 7) [34,65,24,129,320,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4894 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4895 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 412, targets := 32 },{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7),(2,5),(3,5),(4,5)], upper := (rows 35 67 28 137 336 160 96 134 262), lower := (rows 35 67 28 137 336 160 96 128 256), losses := [] }

theorem u4895 : Upper (D 7) (R 7) [34,65,24,129,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4896 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 208 33 320 134 262), lower := (rows 35 67 28 168 208 33 320 128 256), losses := [] }

theorem u4896 : Upper (D 7) (R 7) [34,65,24,160,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4896 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4897 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 28 168 208 34 320 133 261), lower := (rows 35 67 28 168 208 34 320 128 256), losses := [] }

theorem u4897 : Upper (D 7) (R 7) [34,65,24,160,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4897 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4898 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 67 28 168 208 36 320 131 259), lower := (rows 35 67 28 168 208 36 320 128 256), losses := [] }

theorem u4898 : Upper (D 7) (R 7) [34,65,24,160,192,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4898 [(5,2),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4899 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 67 44 88 145 288 66 132 388), lower := (rows 35 67 44 88 145 288 66 128 256), losses := [] }

theorem u4899 : Upper (D 7) (R 7) [34,65,40,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4899 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4900 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 88 145 288 68 130 386), lower := (rows 35 67 44 88 145 288 68 128 256), losses := [] }

theorem u4900 : Upper (D 7) (R 7) [34,65,40,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4900 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4901 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 44 88 145 288 192 134 262), lower := (rows 35 67 44 88 145 288 192 128 256), losses := [] }

theorem u4901 : Upper (D 7) (R 7) [34,65,40,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4901 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4902 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 146 288 65 132 388), lower := (rows 35 67 44 88 146 288 65 128 256), losses := [] }

theorem u4902 : Upper (D 7) (R 7) [34,65,40,80,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4902 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4903 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 88 146 288 68 129 385), lower := (rows 35 67 44 88 146 288 68 128 256), losses := [] }

theorem u4903 : Upper (D 7) (R 7) [34,65,40,80,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4903 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4904 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 44 88 146 288 192 133 261), lower := (rows 35 67 44 88 146 288 192 128 256), losses := [] }

theorem u4904 : Upper (D 7) (R 7) [34,65,40,80,130,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4904 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4905 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 444, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 148 288 65 130 386), lower := (rows 35 67 44 88 148 288 65 128 256), losses := [] }

theorem u4905 : Upper (D 7) (R 7) [34,65,40,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4905 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4906 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 148 288 66 129 385), lower := (rows 35 67 44 88 148 288 66 128 256), losses := [] }

theorem u4906 : Upper (D 7) (R 7) [34,65,40,80,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4906 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4907 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 67 44 88 148 288 192 131 259), lower := (rows 35 67 44 88 148 288 192 128 256), losses := [] }

theorem u4907 : Upper (D 7) (R 7) [34,65,40,80,132,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4907 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4908 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7)], upper := (rows 35 67 44 88 273 160 66 132 388), lower := (rows 35 67 44 88 273 160 66 128 256), losses := [] }

theorem u4908 : Upper (D 7) (R 7) [34,65,40,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4908 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4909 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 67 44 88 273 160 68 130 386), lower := (rows 35 67 44 88 273 160 68 128 256), losses := [] }

theorem u4909 : Upper (D 7) (R 7) [34,65,40,80,257,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4909 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4910 : PairBound 9 := { available := 6, camps := [], pairs := [(0,6),(1,5),(2,0),(2,1)], upper := (rows 35 67 44 88 273 160 192 134 262), lower := (rows 35 67 44 88 273 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 98 98 108 124 272 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 97 97 108 124 273 224 224 224 256) },{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 76 88 275 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 35 44 60 273 160 160 160 256) }] }

theorem u4910 : Upper (D 7) (R 7) [34,65,40,80,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4911 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 274 160 65 132 388), lower := (rows 35 67 44 88 274 160 65 128 256), losses := [] }

theorem u4911 : Upper (D 7) (R 7) [34,65,40,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4911 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4912 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 408, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 67 44 88 274 160 68 129 385), lower := (rows 35 67 44 88 274 160 68 128 256), losses := [] }

theorem u4912 : Upper (D 7) (R 7) [34,65,40,80,258,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4912 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4913 : PairBound 9 := { available := 5, camps := [], pairs := [(0,6),(1,5),(2,0),(2,1)], upper := (rows 35 67 44 88 274 160 192 133 261), lower := (rows 35 67 44 88 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 98 98 108 124 274 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 97 97 108 124 272 224 224 224 256) },{ target := 5, region := (rows 1 3 4 8 16 0 224 128 256), good := (rows 67 67 76 88 274 192 192 192 256) },{ target := 6, region := (rows 3 2 12 8 16 224 0 128 256), good := (rows 35 35 44 60 275 160 160 160 256) }] }

theorem u4913 : Upper (D 7) (R 7) [34,65,40,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4914 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 444, targets := 1 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 44 88 276 160 65 130 386), lower := (rows 35 67 44 88 276 160 65 128 256), losses := [] }

theorem u4914 : Upper (D 7) (R 7) [34,65,40,80,260,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4915 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 444, targets := 2 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 67 44 88 276 160 66 129 385), lower := (rows 35 67 44 88 276 160 66 128 256), losses := [] }

theorem u4915 : Upper (D 7) (R 7) [34,65,40,80,260,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4915 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4916 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(1,5),(2,0),(2,1)], upper := (rows 35 67 44 88 276 160 192 131 259), lower := (rows 35 67 44 88 276 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 98 98 108 124 276 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 16 224 224 128 256), good := (rows 97 97 108 124 276 224 224 224 256) }] }

theorem u4916 : Upper (D 7) (R 7) [34,65,40,80,260,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4916 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4917 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 67 44 137 146 288 68 208 336), lower := (rows 35 67 44 137 146 288 68 128 256), losses := [] }

theorem u4917 : Upper (D 7) (R 7) [34,65,40,129,130,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4917 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4918 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 428, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 146 288 80 196 324), lower := (rows 35 67 44 137 146 288 80 128 256), losses := [] }

theorem u4918 : Upper (D 7) (R 7) [34,65,40,129,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4918 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4919 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 444, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 44 137 148 288 66 208 336), lower := (rows 35 67 44 137 148 288 66 128 256), losses := [] }

theorem u4919 : Upper (D 7) (R 7) [34,65,40,129,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4919 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4919
end Delivery.IrregularNine14.P07
