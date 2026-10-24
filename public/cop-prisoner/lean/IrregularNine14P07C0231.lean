import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0036

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13860 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 25 400 33 194 194 450), lower := (rows 7 98 44 25 400 33 64 128 256), losses := [] }

theorem u13860 : Upper (D 7) (R 7) [6,96,40,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13861 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 25 400 34 193 193 449), lower := (rows 7 98 44 25 400 34 64 128 256), losses := [] }

theorem u13861 : Upper (D 7) (R 7) [6,96,40,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13862 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 25 400 96 195 131 387), lower := (rows 7 98 44 25 400 96 64 128 256), losses := [] }

theorem u13862 : Upper (D 7) (R 7) [6,96,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13863 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 25 400 160 67 195 323), lower := (rows 7 98 44 25 400 160 64 128 256), losses := [] }

theorem u13863 : Upper (D 7) (R 7) [6,96,40,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13864 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 26 400 33 193 193 449), lower := (rows 7 98 44 26 400 33 64 128 256), losses := [] }

theorem u13864 : Upper (D 7) (R 7) [6,96,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13865 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 26 400 96 193 129 385), lower := (rows 7 98 44 26 400 96 64 128 256), losses := [] }

theorem u13865 : Upper (D 7) (R 7) [6,96,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13866 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 26 400 160 65 193 321), lower := (rows 7 98 44 26 400 160 64 128 256), losses := [] }

theorem u13866 : Upper (D 7) (R 7) [6,96,40,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13867 : PairBound 9 := { available := 386, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 88 145 33 450 386 386), lower := (rows 7 98 44 88 145 33 64 128 256), losses := [] }

theorem u13867 : Upper (D 7) (R 7) [6,96,40,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13868 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 88 145 34 449 385 385), lower := (rows 7 98 44 88 145 34 64 128 256), losses := [] }

theorem u13868 : Upper (D 7) (R 7) [6,96,40,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13869 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 88 145 160 323 387 259), lower := (rows 7 98 44 88 145 160 64 128 256), losses := [] }

theorem u13869 : Upper (D 7) (R 7) [6,96,40,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13870 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 98 44 88 145 288 195 131 387), lower := (rows 7 98 44 88 145 288 64 128 256), losses := [] }

theorem u13870 : Upper (D 7) (R 7) [6,96,40,80,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13870 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13871 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 88 146 33 449 385 385), lower := (rows 7 98 44 88 146 33 64 128 256), losses := [] }

theorem u13871 : Upper (D 7) (R 7) [6,96,40,80,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13871 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13872 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 88 146 160 321 385 257), lower := (rows 7 98 44 88 146 160 64 128 256), losses := [] }

theorem u13872 : Upper (D 7) (R 7) [6,96,40,80,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13873 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 7 98 44 88 146 288 193 129 385), lower := (rows 7 98 44 88 146 288 64 128 256), losses := [] }

theorem u13873 : Upper (D 7) (R 7) [6,96,40,80,130,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13873 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13874 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 88 273 33 194 130 386), lower := (rows 7 98 44 88 273 33 64 128 256), losses := [] }

theorem u13874 : Upper (D 7) (R 7) [6,96,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13874 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13875 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 88 273 34 193 129 385), lower := (rows 7 98 44 88 273 34 64 128 256), losses := [] }

theorem u13875 : Upper (D 7) (R 7) [6,96,40,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13875 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13876 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 44 88 273 160 195 131 387), lower := (rows 7 98 44 88 273 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 17 177 0 129 257), good := (rows 439 34 44 60 433 160 0 160 256) }] }

theorem u13876 : Upper (D 7) (R 7) [6,96,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13877 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 88 274 33 193 129 385), lower := (rows 7 98 44 88 274 33 64 128 256), losses := [] }

theorem u13877 : Upper (D 7) (R 7) [6,96,40,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13877 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13878 : Route 9 := (fun mask => (mask,id))

def c13878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u13878 : Upper (D 7) (R 7) [6,96,40,80,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,40,80,258,128] 13 (by decide) (choices 1) [1,128] r13878 c13878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2165
  · exact u2166

def b13879 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 98 44 88 400 33 195 131 387), lower := (rows 7 98 44 88 400 33 64 128 256), losses := [] }

theorem u13879 : Upper (D 7) (R 7) [6,96,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13879 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13880 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 88 400 34 193 129 385), lower := (rows 7 98 44 88 400 34 64 128 256), losses := [] }

theorem u13880 : Upper (D 7) (R 7) [6,96,40,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13881 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 7 98 44 88 400 160 67 131 259), lower := (rows 7 98 44 88 400 160 64 128 256), losses := [] }

theorem u13881 : Upper (D 7) (R 7) [6,96,40,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13882 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 137 81 34 464 400 400), lower := (rows 7 98 44 137 81 34 64 128 256), losses := [] }

theorem u13882 : Upper (D 7) (R 7) [6,96,40,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13883 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 137 81 48 450 386 386), lower := (rows 7 98 44 137 81 48 64 128 256), losses := [] }

theorem u13883 : Upper (D 7) (R 7) [6,96,40,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13883 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13884 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 137 81 160 338 402 274), lower := (rows 7 98 44 137 81 160 64 128 256), losses := [] }

theorem u13884 : Upper (D 7) (R 7) [6,96,40,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13885 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 44 137 81 288 210 146 402), lower := (rows 7 98 44 137 81 288 64 128 256), losses := [] }

theorem u13885 : Upper (D 7) (R 7) [6,96,40,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13885 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13886 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 137 146 33 336 464 336), lower := (rows 7 98 44 137 146 33 64 128 256), losses := [] }

theorem u13886 : Upper (D 7) (R 7) [6,96,40,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13886 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13887 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 45, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 137 146 48 321 449 321), lower := (rows 7 98 44 137 146 48 64 128 256), losses := [] }

theorem u13887 : Upper (D 7) (R 7) [6,96,40,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13887 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13888 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 137 146 96 337 401 273), lower := (rows 7 98 44 137 146 96 64 128 256), losses := [] }

theorem u13888 : Upper (D 7) (R 7) [6,96,40,129,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13889 : Route 9 := (fun mask => (mask,id))

def c13889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13889 : Upper (D 7) (R 7) [6,96,40,129,130,256] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,130,256] 13 (by decide) (choices 1) [1,16] r13889 c13889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2167
  · exact u2168

def b13890 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 137 208 33 338 402 274), lower := (rows 7 98 44 137 208 33 64 128 256), losses := [] }

theorem u13890 : Upper (D 7) (R 7) [6,96,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13890 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13891 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 137 208 34 337 401 273), lower := (rows 7 98 44 137 208 34 64 128 256), losses := [] }

theorem u13891 : Upper (D 7) (R 7) [6,96,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13892 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 137 208 48 323 387 259), lower := (rows 7 98 44 137 208 48 64 128 256), losses := [] }

theorem u13892 : Upper (D 7) (R 7) [6,96,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13892 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r13893 : Route 9 := (fun mask => (mask,id))

def c13893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13893 : Upper (D 7) (R 7) [6,96,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,40,129,192,256] 13 (by decide) (choices 1) [1,2,16] r13893 c13893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2169
  · exact u2170
  · exact u2171

def b13894 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 137 273 34 208 208 464), lower := (rows 7 98 44 137 273 34 64 128 256), losses := [] }

theorem u13894 : Upper (D 7) (R 7) [6,96,40,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13895 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 98 44 137 273 48 194 194 450), lower := (rows 7 98 44 137 273 48 64 128 256), losses := [] }

theorem u13895 : Upper (D 7) (R 7) [6,96,40,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13895 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13896 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 137 273 96 210 146 402), lower := (rows 7 98 44 137 273 96 64 128 256), losses := [] }

theorem u13896 : Upper (D 7) (R 7) [6,96,40,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13897 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 137 273 160 82 210 338), lower := (rows 7 98 44 137 273 160 64 128 256), losses := [] }

theorem u13897 : Upper (D 7) (R 7) [6,96,40,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13898 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 137 274 33 208 208 464), lower := (rows 7 98 44 137 274 33 64 128 256), losses := [] }

theorem u13898 : Upper (D 7) (R 7) [6,96,40,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13899 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 7 98 44 137 274 48 193 193 449), lower := (rows 7 98 44 137 274 48 64 128 256), losses := [] }

theorem u13899 : Upper (D 7) (R 7) [6,96,40,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13899 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13900 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 137 274 96 209 145 401), lower := (rows 7 98 44 137 274 96 64 128 256), losses := [] }

theorem u13900 : Upper (D 7) (R 7) [6,96,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13900 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13901 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 137 274 160 81 209 337), lower := (rows 7 98 44 137 274 160 64 128 256), losses := [] }

theorem u13901 : Upper (D 7) (R 7) [6,96,40,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13901 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13902 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 137 336 33 210 146 402), lower := (rows 7 98 44 137 336 33 64 128 256), losses := [] }

theorem u13902 : Upper (D 7) (R 7) [6,96,40,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13902 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13903 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 137 336 34 209 145 401), lower := (rows 7 98 44 137 336 34 64 128 256), losses := [] }

theorem u13903 : Upper (D 7) (R 7) [6,96,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13903 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13904 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 137 336 48 195 131 387), lower := (rows 7 98 44 137 336 48 64 128 256), losses := [] }

theorem u13904 : Upper (D 7) (R 7) [6,96,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13904 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13905 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 7 98 44 137 336 160 83 147 275), lower := (rows 7 98 44 137 336 160 64 128 256), losses := [] }

theorem u13905 : Upper (D 7) (R 7) [6,96,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13905 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13906 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 36, targets := 194 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(2,6),(2,7),(3,5)], upper := (rows 7 98 44 137 400 33 82 210 338), lower := (rows 7 98 44 137 400 33 64 128 256), losses := [] }

theorem u13906 : Upper (D 7) (R 7) [6,96,40,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13906 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13907 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 98 44 137 400 34 81 209 337), lower := (rows 7 98 44 137 400 34 64 128 256), losses := [] }

theorem u13907 : Upper (D 7) (R 7) [6,96,40,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13907 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13908 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 98 44 137 400 48 67 195 323), lower := (rows 7 98 44 137 400 48 64 128 256), losses := [] }

theorem u13908 : Upper (D 7) (R 7) [6,96,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13908 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13909 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 137 400 96 83 147 275), lower := (rows 7 98 44 137 400 96 64 128 256), losses := [] }

theorem u13909 : Upper (D 7) (R 7) [6,96,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13909 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13910 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 138 81 33 464 400 400), lower := (rows 7 98 44 138 81 33 64 128 256), losses := [] }

theorem u13910 : Upper (D 7) (R 7) [6,96,40,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13910 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13911 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 138 81 48 449 385 385), lower := (rows 7 98 44 138 81 48 64 128 256), losses := [] }

theorem u13911 : Upper (D 7) (R 7) [6,96,40,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13911 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13912 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 7 98 44 138 81 160 337 401 273), lower := (rows 7 98 44 138 81 160 64 128 256), losses := [] }

theorem u13912 : Upper (D 7) (R 7) [6,96,40,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13912 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13913 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 44 138 81 288 209 145 401), lower := (rows 7 98 44 138 81 288 64 128 256), losses := [] }

theorem u13913 : Upper (D 7) (R 7) [6,96,40,130,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13913 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13914 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 138 208 33 337 401 273), lower := (rows 7 98 44 138 208 33 64 128 256), losses := [] }

theorem u13914 : Upper (D 7) (R 7) [6,96,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13914 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13915 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 44 138 208 48 321 385 257), lower := (rows 7 98 44 138 208 48 64 128 256), losses := [] }

theorem u13915 : Upper (D 7) (R 7) [6,96,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13915 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13916 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 44 138 208 288 81 145 273), lower := (rows 7 98 44 138 208 288 64 128 256), losses := [] }

theorem u13916 : Upper (D 7) (R 7) [6,96,40,130,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13916 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13917 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 44 138 273 33 208 208 464), lower := (rows 7 98 44 138 273 33 64 128 256), losses := [] }

theorem u13917 : Upper (D 7) (R 7) [6,96,40,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13917 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13918 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 7 98 44 138 273 48 193 193 449), lower := (rows 7 98 44 138 273 48 64 128 256), losses := [] }

theorem u13918 : Upper (D 7) (R 7) [6,96,40,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13918 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13919 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 44 138 273 96 209 145 401), lower := (rows 7 98 44 138 273 96 64 128 256), losses := [] }

theorem u13919 : Upper (D 7) (R 7) [6,96,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u13919
end Delivery.IrregularNine14.P07
