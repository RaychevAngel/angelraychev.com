import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7860 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 152 336 34 66 137 265), lower := (rows 37 98 133 152 336 34 66 128 256), losses := [] }

theorem u7860 : Upper (D 7) (R 7) [36,96,129,144,320,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7861 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 133 152 336 34 72 131 259), lower := (rows 37 98 133 152 336 34 72 128 256), losses := [] }

theorem u7861 : Upper (D 7) (R 7) [36,96,129,144,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7861 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7862 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 200 273 34 66 152 280), lower := (rows 37 98 133 200 273 34 66 128 256), losses := [] }

theorem u7862 : Upper (D 7) (R 7) [36,96,129,192,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7863 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 200 273 34 72 146 274), lower := (rows 37 98 133 200 273 34 72 128 256), losses := [] }

theorem u7863 : Upper (D 7) (R 7) [36,96,129,192,257,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7863 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7864 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 1, region := 136, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 98 133 200 273 34 80 138 266), lower := (rows 37 98 133 200 273 34 80 128 256), losses := [] }

theorem u7864 : Upper (D 7) (R 7) [36,96,129,192,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7864 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7865 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 200 274 34 65 152 280), lower := (rows 37 98 133 200 274 34 65 128 256), losses := [] }

theorem u7865 : Upper (D 7) (R 7) [36,96,129,192,258,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7866 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 37 98 133 200 274 34 72 145 273), lower := (rows 37 98 133 200 274 34 72 128 256), losses := [] }

theorem u7866 : Upper (D 7) (R 7) [36,96,129,192,258,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7866 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7867 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 200 274 34 80 137 265), lower := (rows 37 98 133 200 274 34 80 128 256), losses := [] }

theorem u7867 : Upper (D 7) (R 7) [36,96,129,192,258,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7867 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7868 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 98 133 200 274 48 65 138 266), lower := (rows 37 98 133 200 274 48 65 128 256), losses := [] }

theorem u7868 : Upper (D 7) (R 7) [36,96,129,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7868 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7869 : PairBound 9 := { available := 9, camps := [{ cop := 8, region := 114, targets := 129 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 133 200 274 48 66 137 265), lower := (rows 37 98 133 200 274 48 66 128 256), losses := [] }

theorem u7869 : Upper (D 7) (R 7) [36,96,129,192,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7869 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7870 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 133 200 274 48 72 131 259), lower := (rows 37 98 133 200 274 48 72 128 256), losses := [] }

theorem u7870 : Upper (D 7) (R 7) [36,96,129,192,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7870 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7871 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 408, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 37 98 133 200 280 34 65 146 274), lower := (rows 37 98 133 200 280 34 65 128 256), losses := [] }

theorem u7871 : Upper (D 7) (R 7) [36,96,129,192,264,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7872 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 133 200 280 34 66 145 273), lower := (rows 37 98 133 200 280 34 66 128 256), losses := [] }

theorem u7872 : Upper (D 7) (R 7) [36,96,129,192,264,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7873 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 133 200 280 34 80 131 259), lower := (rows 37 98 133 200 280 34 80 128 256), losses := [] }

theorem u7873 : Upper (D 7) (R 7) [36,96,129,192,264,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7873 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7874 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 26 288 65 192 448), lower := (rows 37 98 134 25 26 288 65 128 256), losses := [] }

theorem u7874 : Upper (D 7) (R 7) [36,96,130,17,10,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7874 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7875 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 353, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 37 98 134 25 26 288 192 193 321), lower := (rows 37 98 134 25 26 288 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 24 288 196 128 256), good := (rows 102 98 198 26 26 288 192 192 288) }] }

theorem u7875 : Upper (D 7) (R 7) [36,96,130,17,10,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7875 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7876 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 24, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 37 98 134 25 88 288 65 130 386), lower := (rows 37 98 134 25 88 288 65 128 256), losses := [] }

theorem u7876 : Upper (D 7) (R 7) [36,96,130,17,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7876 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7877 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 134 25 88 288 66 129 385), lower := (rows 37 98 134 25 88 288 66 128 256), losses := [] }

theorem u7877 : Upper (D 7) (R 7) [36,96,130,17,72,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7877 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7878 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 2, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 37 98 134 25 88 288 192 131 259), lower := (rows 37 98 134 25 88 288 192 128 256), losses := [] }

theorem u7878 : Upper (D 7) (R 7) [36,96,130,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7878 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7879 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 134 25 152 288 65 194 322), lower := (rows 37 98 134 25 152 288 65 128 256), losses := [] }

theorem u7879 : Upper (D 7) (R 7) [36,96,130,17,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7879 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7880 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7)], upper := (rows 37 98 134 25 152 288 66 193 321), lower := (rows 37 98 134 25 152 288 66 128 256), losses := [] }

theorem u7880 : Upper (D 7) (R 7) [36,96,130,17,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7880 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7881 : Route 9 := (fun mask => (mask,id))

def c7881 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7881 : Upper (D 7) (R 7) [36,96,130,17,192,256,1] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,192,256,1] 13 (by decide) (choices 1) [2,8] r7881 c7881
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u614
  · exact u615

def b7882 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 98 134 25 208 288 66 137 265), lower := (rows 37 98 134 25 208 288 66 128 256), losses := [] }

theorem u7882 : Upper (D 7) (R 7) [36,96,130,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7882 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7883 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 25 208 288 72 131 259), lower := (rows 37 98 134 25 208 288 72 128 256), losses := [] }

theorem u7883 : Upper (D 7) (R 7) [36,96,130,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7883 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7884 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 274 33 72 192 448), lower := (rows 37 98 134 25 274 33 72 128 256), losses := [] }

theorem u7884 : Upper (D 7) (R 7) [36,96,130,17,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7884 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7885 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 134 25 274 33 192 200 328), lower := (rows 37 98 134 25 274 33 192 128 256), losses := [{ target := 0, region := (rows 0 3 12 8 24 32 204 136 264), good := (rows 102 98 198 478 274 34 192 192 256) }] }

theorem u7885 : Upper (D 7) (R 7) [36,96,130,17,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7886 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 274 40 65 192 448), lower := (rows 37 98 134 25 274 40 65 128 256), losses := [] }

theorem u7886 : Upper (D 7) (R 7) [36,96,130,17,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7886 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7887 : Route 9 := (fun mask => (mask,id))

def c7887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7887 : Upper (D 7) (R 7) [36,96,130,17,258,8,128] 13 := by
  apply FastRouting.sound _ _ [36,96,130,17,258,8,128] 13 (by decide) (choices 1) [1,64] r7887 c7887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u616
  · exact u617

def b7888 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 134 25 336 33 66 136 392), lower := (rows 37 98 134 25 336 33 66 128 256), losses := [] }

theorem u7888 : Upper (D 7) (R 7) [36,96,130,17,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7889 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 336 33 72 130 386), lower := (rows 37 98 134 25 336 33 72 128 256), losses := [] }

theorem u7889 : Upper (D 7) (R 7) [36,96,130,17,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7889 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7890 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 33, targets := 192 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 98 134 25 336 33 192 138 266), lower := (rows 37 98 134 25 336 33 192 128 256), losses := [{ target := 0, region := (rows 0 3 12 8 24 32 204 136 264), good := (rows 102 98 198 478 336 34 192 192 256) }] }

theorem u7890 : Upper (D 7) (R 7) [36,96,130,17,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7891 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 336 40 65 130 386), lower := (rows 37 98 134 25 336 40 65 128 256), losses := [] }

theorem u7891 : Upper (D 7) (R 7) [36,96,130,17,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7891 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7892 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 134 25 336 40 66 129 385), lower := (rows 37 98 134 25 336 40 66 128 256), losses := [] }

theorem u7892 : Upper (D 7) (R 7) [36,96,130,17,320,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7892 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7893 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,0),(2,6)], upper := (rows 37 98 134 25 336 40 192 131 259), lower := (rows 37 98 134 25 336 40 192 128 256), losses := [{ target := 0, region := (rows 0 3 4 8 16 40 196 128 256), good := (rows 102 98 198 58 336 40 192 192 256) }] }

theorem u7893 : Upper (D 7) (R 7) [36,96,130,17,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7893 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7894 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 134 25 400 40 65 194 322), lower := (rows 37 98 134 25 400 40 65 128 256), losses := [] }

theorem u7894 : Upper (D 7) (R 7) [36,96,130,17,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7894 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7895 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(3,5)], upper := (rows 37 98 134 25 400 40 66 193 321), lower := (rows 37 98 134 25 400 40 66 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 25 0 70 129 257), good := (rows 477 66 198 409 400 24 66 128 256) }] }

theorem u7895 : Upper (D 7) (R 7) [36,96,130,17,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7895 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7896 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7),(4,7)], upper := (rows 37 98 134 26 81 288 65 136 392), lower := (rows 37 98 134 26 81 288 65 128 256), losses := [] }

theorem u7896 : Upper (D 7) (R 7) [36,96,130,18,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7896 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7897 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 37 98 134 26 81 288 72 129 385), lower := (rows 37 98 134 26 81 288 72 128 256), losses := [] }

theorem u7897 : Upper (D 7) (R 7) [36,96,130,18,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7897 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7898 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 4, region := 298, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 134 26 81 288 192 137 265), lower := (rows 37 98 134 26 81 288 192 128 256), losses := [] }

theorem u7898 : Upper (D 7) (R 7) [36,96,130,18,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7898 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7899 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 134 26 145 288 65 200 328), lower := (rows 37 98 134 26 145 288 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 81 136 264), good := (rows 69 66 134 478 209 256 65 128 256) }] }

theorem u7899 : Upper (D 7) (R 7) [36,96,130,18,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7899 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7900 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 37 98 134 26 145 288 72 193 321), lower := (rows 37 98 134 26 145 288 72 128 256), losses := [] }

theorem u7900 : Upper (D 7) (R 7) [36,96,130,18,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7900 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7901 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 0, region := 66, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 134 26 208 288 65 137 265), lower := (rows 37 98 134 26 208 288 65 128 256), losses := [] }

theorem u7901 : Upper (D 7) (R 7) [36,96,130,18,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7901 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7902 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 37 98 134 26 208 288 72 129 257), lower := (rows 37 98 134 26 208 288 72 128 256), losses := [] }

theorem u7902 : Upper (D 7) (R 7) [36,96,130,18,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7902 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7903 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 134 26 400 33 65 200 328), lower := (rows 37 98 134 26 400 33 65 128 256), losses := [] }

theorem u7903 : Upper (D 7) (R 7) [36,96,130,18,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7904 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 134 26 400 33 72 193 321), lower := (rows 37 98 134 26 400 33 72 128 256), losses := [] }

theorem u7904 : Upper (D 7) (R 7) [36,96,130,18,384,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7904 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7905 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 98 134 73 145 288 66 152 280), lower := (rows 37 98 134 73 145 288 66 128 256), losses := [] }

theorem u7905 : Upper (D 7) (R 7) [36,96,130,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7905 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7906 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 149, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 73 145 288 72 146 274), lower := (rows 37 98 134 73 145 288 72 128 256), losses := [] }

theorem u7906 : Upper (D 7) (R 7) [36,96,130,65,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7906 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7907 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 37 98 134 73 145 288 80 138 266), lower := (rows 37 98 134 73 145 288 80 128 256), losses := [] }

theorem u7907 : Upper (D 7) (R 7) [36,96,130,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7907 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7908 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 134 73 152 288 65 146 274), lower := (rows 37 98 134 73 152 288 65 128 256), losses := [] }

theorem u7908 : Upper (D 7) (R 7) [36,96,130,65,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7908 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7909 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 98 134 73 152 288 66 145 273), lower := (rows 37 98 134 73 152 288 66 128 256), losses := [] }

theorem u7909 : Upper (D 7) (R 7) [36,96,130,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7909 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7910 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 73 152 288 80 131 259), lower := (rows 37 98 134 73 152 288 80 128 256), losses := [] }

theorem u7910 : Upper (D 7) (R 7) [36,96,130,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7910 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7911 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 400, targets := 2 }], pairs := [(1,7),(3,7),(4,1)], upper := (rows 37 98 134 73 273 48 66 136 392), lower := (rows 37 98 134 73 273 48 66 128 256), losses := [] }

theorem u7911 : Upper (D 7) (R 7) [36,96,130,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7911 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7912 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 73 273 48 72 130 386), lower := (rows 37 98 134 73 273 48 72 128 256), losses := [] }

theorem u7912 : Upper (D 7) (R 7) [36,96,130,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7912 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7913 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 306, targets := 128 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 37 98 134 73 273 48 192 138 266), lower := (rows 37 98 134 73 273 48 192 128 256), losses := [{ target := 0, region := (rows 0 3 12 8 16 48 204 136 264), good := (rows 102 98 198 462 306 48 192 192 256) }] }

theorem u7913 : Upper (D 7) (R 7) [36,96,130,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7913 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7914 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 134 73 274 48 65 136 392), lower := (rows 37 98 134 73 274 48 65 128 256), losses := [] }

theorem u7914 : Upper (D 7) (R 7) [36,96,130,65,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7914 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7915 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 98 134 73 274 48 72 129 385), lower := (rows 37 98 134 73 274 48 72 128 256), losses := [] }

theorem u7915 : Upper (D 7) (R 7) [36,96,130,65,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7915 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7916 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 3, region := 306, targets := 128 }], pairs := [(1,7),(3,1),(3,5)], upper := (rows 37 98 134 73 274 48 192 137 265), lower := (rows 37 98 134 73 274 48 192 128 256), losses := [] }

theorem u7916 : Upper (D 7) (R 7) [36,96,130,65,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7916 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7917 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 37 98 134 73 280 48 65 130 386), lower := (rows 37 98 134 73 280 48 65 128 256), losses := [] }

theorem u7917 : Upper (D 7) (R 7) [36,96,130,65,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7917 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7918 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 1, region := 133, targets := 64 }], pairs := [(0,6),(1,7),(3,7)], upper := (rows 37 98 134 73 280 48 66 129 385), lower := (rows 37 98 134 73 280 48 66 128 256), losses := [] }

theorem u7918 : Upper (D 7) (R 7) [36,96,130,65,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7919 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 64 },{ cop := 3, region := 306, targets := 128 }], pairs := [(0,6),(1,7),(2,6)], upper := (rows 37 98 134 73 280 48 192 131 259), lower := (rows 37 98 134 73 280 48 192 128 256), losses := [] }

theorem u7919 : Upper (D 7) (R 7) [36,96,130,65,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7919 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7919
end Delivery.IrregularNine14.P07
