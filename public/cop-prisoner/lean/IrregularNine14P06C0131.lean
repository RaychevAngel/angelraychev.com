import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 2, camps := [{ cop := 7, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 73 336 36 68 130 258), lower := (rows 41 50 133 73 336 36 68 128 256), losses := [] }

theorem u7860 : Upper (D 6) (R 6) [40,48,129,65,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7861 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 41 50 133 74 273 36 66 196 324), lower := (rows 41 50 133 74 273 36 66 128 256), losses := [] }

theorem u7861 : Upper (D 6) (R 6) [40,48,129,66,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7861 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7862 : PairBound 9 := { available := 66, camps := [], pairs := [(0,1),(1,2),(3,0)], upper := (rows 41 50 133 74 273 36 68 194 322), lower := (rows 41 50 133 74 273 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 100 100 138 266), good := (rows 488 506 228 490 272 100 100 128 256) },{ target := 1, region := (rows 9 0 4 8 16 100 100 128 256), good := (rows 105 112 229 105 273 100 100 128 256) },{ target := 2, region := (rows 1 3 0 8 17 32 64 136 264), good := (rows 443 50 147 458 275 32 64 128 256) }] }

theorem u7862 : Upper (D 6) (R 6) [40,48,129,66,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7863 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 50 133 74 336 36 65 134 262), lower := (rows 41 50 133 74 336 36 65 128 256), losses := [] }

theorem u7863 : Upper (D 6) (R 6) [40,48,129,66,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7864 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 41 50 133 74 336 36 66 133 261), lower := (rows 41 50 133 74 336 36 66 128 256), losses := [] }

theorem u7864 : Upper (D 6) (R 6) [40,48,129,66,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7865 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 41 50 133 74 336 36 68 131 259), lower := (rows 41 50 133 74 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 26 16 100 100 128 256), good := (rows 104 122 228 106 378 100 100 128 256) }] }

theorem u7865 : Upper (D 6) (R 6) [40,48,129,66,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7865 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7866 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 41 50 133 76 22 288 65 194 322), lower := (rows 41 50 133 76 22 288 65 128 256), losses := [] }

theorem u7866 : Upper (D 6) (R 6) [40,48,129,68,6,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7866 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7867 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 429, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 50 133 76 22 288 66 193 321), lower := (rows 41 50 133 76 22 288 66 128 256), losses := [] }

theorem u7867 : Upper (D 6) (R 6) [40,48,129,68,6,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7867 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7868 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 41 50 133 76 82 288 65 134 262), lower := (rows 41 50 133 76 82 288 65 128 256), losses := [] }

theorem u7868 : Upper (D 6) (R 6) [40,48,129,68,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7868 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7869 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 289, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 50 133 76 82 288 66 133 261), lower := (rows 41 50 133 76 82 288 66 128 256), losses := [] }

theorem u7869 : Upper (D 6) (R 6) [40,48,129,68,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7869 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7870 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 41 50 133 76 82 288 68 131 259), lower := (rows 41 50 133 76 82 288 68 128 256), losses := [] }

theorem u7870 : Upper (D 6) (R 6) [40,48,129,68,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7870 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7871 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 265 22 96 66 196 324), lower := (rows 41 50 133 265 22 96 66 128 256), losses := [] }

theorem u7871 : Upper (D 6) (R 6) [40,48,129,257,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7872 : Route 9 := (fun mask => (mask,id))

def c7872 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7872 : Upper (D 6) (R 6) [40,48,129,257,6,64,4] 13 := by
  apply FastRouting.sound _ _ [40,48,129,257,6,64,4] 13 (by decide) (choices 1) [2,64] r7872 c7872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u609
  · exact u610

def b7873 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 80, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 41 50 133 265 82 36 66 196 324), lower := (rows 41 50 133 265 82 36 66 128 256), losses := [] }

theorem u7873 : Upper (D 6) (R 6) [40,48,129,257,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7874 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(0,2),(1,0),(4,0)], upper := (rows 41 50 133 265 82 36 68 194 322), lower := (rows 41 50 133 265 82 36 68 128 256), losses := [{ target := 2, region := (rows 3 2 0 26 16 32 64 144 272), good := (rows 41 443 129 265 475 32 64 128 256) }] }

theorem u7874 : Upper (D 6) (R 6) [40,48,129,257,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7875 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 132, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 41 50 133 266 81 36 66 196 324), lower := (rows 41 50 133 266 81 36 66 128 256), losses := [] }

theorem u7875 : Upper (D 6) (R 6) [40,48,129,258,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7875 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7876 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 80, targets := 2 },{ cop := 2, region := 80, targets := 32 }], pairs := [(1,0),(4,1),(4,5)], upper := (rows 41 50 133 266 81 36 68 194 322), lower := (rows 41 50 133 266 81 36 68 128 256), losses := [{ target := 0, region := (rows 0 18 4 26 16 100 100 146 274), good := (rows 104 506 228 394 506 100 100 128 256) }] }

theorem u7876 : Upper (D 6) (R 6) [40,48,129,258,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7877 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 97, targets := 6 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 41 50 133 268 22 96 65 194 322), lower := (rows 41 50 133 268 22 96 65 128 256), losses := [{ target := 2, region := (rows 9 18 0 8 16 125 77 144 272), good := (rows 105 434 225 361 498 96 97 128 256) }] }

theorem u7877 : Upper (D 6) (R 6) [40,48,129,260,6,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7878 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 133 268 22 96 66 193 321), lower := (rows 41 50 133 268 22 96 66 128 256), losses := [] }

theorem u7878 : Upper (D 6) (R 6) [40,48,129,260,6,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7879 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 166, targets := 64 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 133 328 81 36 66 134 262), lower := (rows 41 50 133 328 81 36 66 128 256), losses := [] }

theorem u7879 : Upper (D 6) (R 6) [40,48,129,320,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7879 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7880 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 166, targets := 64 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,6),(2,6),(4,1)], upper := (rows 41 50 133 328 81 36 68 130 258), lower := (rows 41 50 133 328 81 36 68 128 256), losses := [] }

theorem u7880 : Upper (D 6) (R 6) [40,48,129,320,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7881 : Route 9 := (fun mask => (mask,id))

def c7881 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7881 : Upper (D 6) (R 6) [40,48,129,320,66,4,1] 13 := by
  apply FastRouting.sound _ _ [40,48,129,320,66,4,1] 13 (by decide) (choices 1) [2,4] r7881 c7881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u611
  · exact u612

def b7882 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 41 50 133 328 82 36 66 133 261), lower := (rows 41 50 133 328 82 36 66 128 256), losses := [] }

theorem u7882 : Upper (D 6) (R 6) [40,48,129,320,66,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7883 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 114, targets := 1 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 50 133 328 82 36 68 131 259), lower := (rows 41 50 133 328 82 36 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 100 100 128 256), good := (rows 105 112 229 361 112 100 100 128 256) }] }

theorem u7883 : Upper (D 6) (R 6) [40,48,129,320,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7884 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 50 196 13 82 288 65 134 262), lower := (rows 41 50 196 13 82 288 65 128 256), losses := [] }

theorem u7884 : Upper (D 6) (R 6) [40,48,192,5,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7884 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7885 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 297, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 50 196 13 82 288 66 133 261), lower := (rows 41 50 196 13 82 288 66 128 256), losses := [] }

theorem u7885 : Upper (D 6) (R 6) [40,48,192,5,66,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7885 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7886 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 50 196 13 82 288 68 131 259), lower := (rows 41 50 196 13 82 288 68 128 256), losses := [] }

theorem u7886 : Upper (D 6) (R 6) [40,48,192,5,66,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7886 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7887 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 4, region := 98, targets := 4 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 41 50 196 14 273 96 65 134 262), lower := (rows 41 50 196 14 273 96 65 128 256), losses := [] }

theorem u7887 : Upper (D 6) (R 6) [40,48,192,6,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7888 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 98, targets := 5 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 50 196 14 273 96 66 133 261), lower := (rows 41 50 196 14 273 96 66 128 256), losses := [] }

theorem u7888 : Upper (D 6) (R 6) [40,48,192,6,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7889 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 274, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 196 14 273 96 68 131 259), lower := (rows 41 50 196 14 273 96 68 128 256), losses := [] }

theorem u7889 : Upper (D 6) (R 6) [40,48,192,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7890 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 41 50 196 73 274 36 65 134 262), lower := (rows 41 50 196 73 274 36 65 128 256), losses := [] }

theorem u7890 : Upper (D 6) (R 6) [40,48,192,65,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7891 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 173, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 50 196 73 274 36 66 133 261), lower := (rows 41 50 196 73 274 36 66 128 256), losses := [] }

theorem u7891 : Upper (D 6) (R 6) [40,48,192,65,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7892 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 274, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 196 73 274 36 68 131 259), lower := (rows 41 50 196 73 274 36 68 128 256), losses := [] }

theorem u7892 : Upper (D 6) (R 6) [40,48,192,65,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7892 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7893 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 3, region := 132, targets := 1 }], pairs := [(0,2),(2,0),(3,2)], upper := (rows 41 50 196 74 273 36 65 134 262), lower := (rows 41 50 196 74 273 36 65 128 256), losses := [] }

theorem u7893 : Upper (D 6) (R 6) [40,48,192,66,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7893 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7894 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 437, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 41 50 196 74 273 36 66 133 261), lower := (rows 41 50 196 74 273 36 66 128 256), losses := [] }

theorem u7894 : Upper (D 6) (R 6) [40,48,192,66,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7895 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 274, targets := 68 }], pairs := [(1,2),(1,6),(4,2)], upper := (rows 41 50 196 74 273 36 68 131 259), lower := (rows 41 50 196 74 273 36 68 128 256), losses := [] }

theorem u7895 : Upper (D 6) (R 6) [40,48,192,66,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7895 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7896 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 82 100 11 148 288 65 134 262), lower := (rows 41 82 100 11 148 288 65 128 256), losses := [] }

theorem u7896 : Upper (D 6) (R 6) [40,80,96,3,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7896 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7897 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 82 100 11 148 288 66 133 261), lower := (rows 41 82 100 11 148 288 66 128 256), losses := [] }

theorem u7897 : Upper (D 6) (R 6) [40,80,96,3,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7897 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7898 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 297, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 82 100 11 148 288 68 131 259), lower := (rows 41 82 100 11 148 288 68 128 256), losses := [] }

theorem u7898 : Upper (D 6) (R 6) [40,80,96,3,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7898 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7899 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 137, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 137 273 34 66 132 260), lower := (rows 41 82 100 137 273 34 66 128 256), losses := [] }

theorem u7899 : Upper (D 6) (R 6) [40,80,96,129,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7900 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 0, region := 68, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 41 82 100 137 273 34 68 134 262), lower := (rows 41 82 100 137 273 34 68 128 256), losses := [] }

theorem u7900 : Upper (D 6) (R 6) [40,80,96,129,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7901 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 274, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 41 82 100 137 274 33 68 134 262), lower := (rows 41 82 100 137 274 33 68 128 256), losses := [] }

theorem u7901 : Upper (D 6) (R 6) [40,80,96,129,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7902 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 205, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 82 100 137 274 34 68 133 261), lower := (rows 41 82 100 137 274 34 68 128 256), losses := [] }

theorem u7902 : Upper (D 6) (R 6) [40,80,96,129,258,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7903 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 82 100 137 274 36 68 131 259), lower := (rows 41 82 100 137 274 36 68 128 256), losses := [] }

theorem u7903 : Upper (D 6) (R 6) [40,80,96,129,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7904 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 310, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 82 100 137 276 34 65 134 262), lower := (rows 41 82 100 137 276 34 65 128 256), losses := [] }

theorem u7904 : Upper (D 6) (R 6) [40,80,96,129,260,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7905 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 137, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 82 100 137 276 34 66 133 261), lower := (rows 41 82 100 137 276 34 66 128 256), losses := [] }

theorem u7905 : Upper (D 6) (R 6) [40,80,96,129,260,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7906 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 169, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 82 100 137 276 34 68 131 259), lower := (rows 41 82 100 137 276 34 68 128 256), losses := [] }

theorem u7906 : Upper (D 6) (R 6) [40,80,96,129,260,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7907 : PairBound 9 := { available := 2, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 41 82 100 140 276 33 65 130 258), lower := (rows 41 82 100 140 276 33 65 128 256), losses := [] }

theorem u7907 : Upper (D 6) (R 6) [40,80,96,132,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r7908 : Route 9 := (fun mask => (mask,id))

def c7908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7908 : Upper (D 6) (R 6) [40,80,96,132,260,2,1] 13 := by
  apply FastRouting.sound _ _ [40,80,96,132,260,2,1] 13 (by decide) (choices 1) [1,2] r7908 c7908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u613
  · exact u614

def b7909 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 353, targets := 4 }], pairs := [(0,2),(4,0)], upper := (rows 41 82 133 14 52 288 65 194 322), lower := (rows 41 82 133 14 52 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 298 64 130 258), good := (rows 56 498 132 446 52 288 64 128 288) }] }

theorem u7909 : Upper (D 6) (R 6) [40,80,129,6,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7909 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7910 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 41 82 133 14 52 288 66 193 321), lower := (rows 41 82 133 14 52 288 66 128 256), losses := [] }

theorem u7910 : Upper (D 6) (R 6) [40,80,129,6,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7910 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7911 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 14 273 96 66 164 292), lower := (rows 41 82 133 14 273 96 66 128 256), losses := [] }

theorem u7911 : Upper (D 6) (R 6) [40,80,129,6,257,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7912 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 41 82 133 14 273 96 68 162 290), lower := (rows 41 82 133 14 273 96 68 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 25 98 64 138 266), good := (rows 441 498 145 443 273 96 96 128 256) }] }

theorem u7912 : Upper (D 6) (R 6) [40,80,129,6,257,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7913 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 82 133 14 273 96 96 134 262), lower := (rows 41 82 133 14 273 96 96 128 256), losses := [] }

theorem u7913 : Upper (D 6) (R 6) [40,80,129,6,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7913 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7914 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 97, targets := 2 },{ cop := 3, region := 97, targets := 4 }], pairs := [(0,1),(0,2),(4,0)], upper := (rows 41 82 133 14 276 96 65 162 290), lower := (rows 41 82 133 14 276 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 98 64 138 266), good := (rows 440 498 132 446 276 96 96 128 256) }] }

theorem u7914 : Upper (D 6) (R 6) [40,80,129,6,260,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7915 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 14 276 96 66 161 289), lower := (rows 41 82 133 14 276 96 66 128 256), losses := [] }

theorem u7915 : Upper (D 6) (R 6) [40,80,129,6,260,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7916 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 41 82 133 14 276 96 96 131 259), lower := (rows 41 82 133 14 276 96 96 128 256), losses := [] }

theorem u7916 : Upper (D 6) (R 6) [40,80,129,6,260,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7917 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 97, targets := 6 }], pairs := [(0,1),(0,2),(1,0)], upper := (rows 41 82 133 14 304 96 65 134 262), lower := (rows 41 82 133 14 304 96 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 8 25 98 64 136 264), good := (rows 440 114 148 446 304 98 114 128 256) }] }

theorem u7917 : Upper (D 6) (R 6) [40,80,129,6,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7918 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 404, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 41 82 133 14 304 96 66 133 261), lower := (rows 41 82 133 14 304 96 66 128 256), losses := [] }

theorem u7918 : Upper (D 6) (R 6) [40,80,129,6,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b7919 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(0,2),(4,2)], upper := (rows 41 82 133 14 304 96 68 131 259), lower := (rows 41 82 133 14 304 96 68 128 256), losses := [{ target := 2, region := (rows 9 2 0 8 25 98 64 136 264), good := (rows 441 114 145 443 304 96 96 128 256) }] }

theorem u7919 : Upper (D 6) (R 6) [40,80,129,6,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b7919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u7919
end Delivery.IrregularNine14.P06
