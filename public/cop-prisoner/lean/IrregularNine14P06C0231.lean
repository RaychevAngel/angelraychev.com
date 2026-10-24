import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0049

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13860 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 265 49 36 82 210 338), lower := (rows 11 38 196 265 49 36 64 128 256), losses := [] }

theorem u13860 : Upper (D 6) (R 6) [10,36,192,257,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13860 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13861 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 196 265 49 48 70 198 326), lower := (rows 11 38 196 265 49 48 64 128 256), losses := [] }

theorem u13861 : Upper (D 6) (R 6) [10,36,192,257,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13861 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13862 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 265 49 96 86 150 278), lower := (rows 11 38 196 265 49 96 64 128 256), losses := [] }

theorem u13862 : Upper (D 6) (R 6) [10,36,192,257,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13862 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13863 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 265 81 34 116 180 308), lower := (rows 11 38 196 265 81 34 64 128 256), losses := [] }

theorem u13863 : Upper (D 6) (R 6) [10,36,192,257,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13863 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13864 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 265 81 36 114 178 306), lower := (rows 11 38 196 265 81 36 64 128 256), losses := [] }

theorem u13864 : Upper (D 6) (R 6) [10,36,192,257,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13864 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13865 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 196 265 81 48 102 166 294), lower := (rows 11 38 196 265 81 48 64 128 256), losses := [] }

theorem u13865 : Upper (D 6) (R 6) [10,36,192,257,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13865 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13866 : PairBound 9 := { available := 52, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 265 82 33 116 180 308), lower := (rows 11 38 196 265 82 33 64 128 256), losses := [] }

theorem u13866 : Upper (D 6) (R 6) [10,36,192,257,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13866 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13867 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 265 82 36 113 177 305), lower := (rows 11 38 196 265 82 36 64 128 256), losses := [] }

theorem u13867 : Upper (D 6) (R 6) [10,36,192,257,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13867 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13868 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 196 265 82 48 101 165 293), lower := (rows 11 38 196 265 82 48 64 128 256), losses := [] }

theorem u13868 : Upper (D 6) (R 6) [10,36,192,257,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13868 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13869 : PairBound 9 := { available := 22, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 38 196 265 112 33 86 150 278), lower := (rows 11 38 196 265 112 33 64 128 256), losses := [] }

theorem u13869 : Upper (D 6) (R 6) [10,36,192,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13869 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13870 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 11 38 196 265 112 34 85 149 277), lower := (rows 11 38 196 265 112 34 64 128 256), losses := [] }

theorem u13870 : Upper (D 6) (R 6) [10,36,192,257,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13870 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13871 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 265 112 36 83 147 275), lower := (rows 11 38 196 265 112 36 64 128 256), losses := [] }

theorem u13871 : Upper (D 6) (R 6) [10,36,192,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13871 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13872 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 196 265 112 48 71 135 263), lower := (rows 11 38 196 265 112 48 64 128 256), losses := [] }

theorem u13872 : Upper (D 6) (R 6) [10,36,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13872 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13873 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 51, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 196 268 49 33 82 210 338), lower := (rows 11 38 196 268 49 33 64 128 256), losses := [] }

theorem u13873 : Upper (D 6) (R 6) [10,36,192,260,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13873 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13874 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 268 49 34 81 209 337), lower := (rows 11 38 196 268 49 34 64 128 256), losses := [] }

theorem u13874 : Upper (D 6) (R 6) [10,36,192,260,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13874 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13875 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 196 268 49 48 67 195 323), lower := (rows 11 38 196 268 49 48 64 128 256), losses := [] }

theorem u13875 : Upper (D 6) (R 6) [10,36,192,260,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13875 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13876 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 268 49 96 83 147 275), lower := (rows 11 38 196 268 49 96 64 128 256), losses := [] }

theorem u13876 : Upper (D 6) (R 6) [10,36,192,260,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13876 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13877 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 268 81 33 114 178 306), lower := (rows 11 38 196 268 81 33 64 128 256), losses := [] }

theorem u13877 : Upper (D 6) (R 6) [10,36,192,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13877 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13878 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 34, targets := 65 },{ cop := 0, region := 112, targets := 4 }], pairs := [(1,0),(1,6),(4,2)], upper := (rows 11 38 196 268 81 34 113 177 305), lower := (rows 11 38 196 268 81 34 64 128 256), losses := [] }

theorem u13878 : Upper (D 6) (R 6) [10,36,192,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13878 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13879 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 196 268 81 48 99 163 291), lower := (rows 11 38 196 268 81 48 64 128 256), losses := [] }

theorem u13879 : Upper (D 6) (R 6) [10,36,192,260,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13879 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13880 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 268 82 33 113 177 305), lower := (rows 11 38 196 268 82 33 64 128 256), losses := [] }

theorem u13880 : Upper (D 6) (R 6) [10,36,192,260,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13880 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13881 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 265, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 11 38 196 268 82 48 97 161 289), lower := (rows 11 38 196 268 82 48 64 128 256), losses := [] }

theorem u13881 : Upper (D 6) (R 6) [10,36,192,260,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13881 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13882 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 35, targets := 64 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,6),(1,6),(4,2)], upper := (rows 11 38 196 268 112 33 83 147 275), lower := (rows 11 38 196 268 112 33 64 128 256), losses := [] }

theorem u13882 : Upper (D 6) (R 6) [10,36,192,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13882 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13883 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 3, region := 35, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 11 38 196 268 112 34 81 145 273), lower := (rows 11 38 196 268 112 34 64 128 256), losses := [] }

theorem u13883 : Upper (D 6) (R 6) [10,36,192,260,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13883 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13884 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 11 38 196 268 112 48 67 131 259), lower := (rows 11 38 196 268 112 48 64 128 256), losses := [] }

theorem u13884 : Upper (D 6) (R 6) [10,36,192,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13884 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13885 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 38 196 280 21 33 98 226 354), lower := (rows 11 38 196 280 21 33 64 128 256), losses := [] }

theorem u13885 : Upper (D 6) (R 6) [10,36,192,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13885 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13886 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 196 280 21 34 97 225 353), lower := (rows 11 38 196 280 21 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 81 145 273), good := (rows 491 34 192 472 505 34 64 128 256) }] }

theorem u13886 : Upper (D 6) (R 6) [10,36,192,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13886 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13887 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 280 21 96 99 163 291), lower := (rows 11 38 196 280 21 96 64 128 256), losses := [] }

theorem u13887 : Upper (D 6) (R 6) [10,36,192,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13887 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13888 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 196 280 49 33 70 198 326), lower := (rows 11 38 196 280 49 33 64 128 256), losses := [] }

theorem u13888 : Upper (D 6) (R 6) [10,36,192,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13888 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13889 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 280 49 34 69 197 325), lower := (rows 11 38 196 280 49 34 64 128 256), losses := [] }

theorem u13889 : Upper (D 6) (R 6) [10,36,192,272,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13889 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13890 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 280 49 36 67 195 323), lower := (rows 11 38 196 280 49 36 64 128 256), losses := [] }

theorem u13890 : Upper (D 6) (R 6) [10,36,192,272,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13890 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13891 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 280 49 96 71 135 263), lower := (rows 11 38 196 280 49 96 64 128 256), losses := [] }

theorem u13891 : Upper (D 6) (R 6) [10,36,192,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13891 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13892 : Route 9 := (fun mask => (mask,id))

def c13892 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13892 : Upper (D 6) (R 6) [10,36,192,272,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,65,1] 13 (by decide) (choices 1) [2,4,32] r13892 c13892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2968
  · exact u2969
  · exact u2970

def r13893 : Route 9 := (fun mask => (mask,id))

def c13893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13893 : Upper (D 6) (R 6) [10,36,192,272,65,2] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,65,2] 13 (by decide) (choices 1) [1,4,32] r13893 c13893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2971
  · exact u2972
  · exact u2973

def b13894 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 280 81 36 99 163 291), lower := (rows 11 38 196 280 81 36 64 128 256), losses := [] }

theorem u13894 : Upper (D 6) (R 6) [10,36,192,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13894 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13895 : Route 9 := (fun mask => (mask,id))

def c13895 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13895 : Upper (D 6) (R 6) [10,36,192,272,66,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,66,1] 13 (by decide) (choices 1) [1,4,32] r13895 c13895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2974
  · exact u2975
  · exact u2976

def b13896 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 280 82 36 97 161 289), lower := (rows 11 38 196 280 82 36 64 128 256), losses := [] }

theorem u13896 : Upper (D 6) (R 6) [10,36,192,272,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13896 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13897 : Route 9 := (fun mask => (mask,id))

def c13897 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13897 : Upper (D 6) (R 6) [10,36,192,272,96,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,272,96,1] 13 (by decide) (choices 1) [1,2,4] r13897 c13897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2977
  · exact u2978
  · exact u2979

def b13898 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 11 38 196 280 112 34 69 133 261), lower := (rows 11 38 196 280 112 34 64 128 256), losses := [] }

theorem u13898 : Upper (D 6) (R 6) [10,36,192,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13898 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13899 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 280 112 36 67 131 259), lower := (rows 11 38 196 280 112 36 64 128 256), losses := [] }

theorem u13899 : Upper (D 6) (R 6) [10,36,192,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13899 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13900 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 196 296 21 33 82 210 338), lower := (rows 11 38 196 296 21 33 64 128 256), losses := [] }

theorem u13900 : Upper (D 6) (R 6) [10,36,192,288,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13900 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13901 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 296 21 34 81 209 337), lower := (rows 11 38 196 296 21 34 64 128 256), losses := [] }

theorem u13901 : Upper (D 6) (R 6) [10,36,192,288,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13901 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13902 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 296 21 48 67 195 323), lower := (rows 11 38 196 296 21 48 64 128 256), losses := [] }

theorem u13902 : Upper (D 6) (R 6) [10,36,192,288,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13902 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13903 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 281, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 196 296 21 96 83 147 275), lower := (rows 11 38 196 296 21 96 64 128 256), losses := [] }

theorem u13903 : Upper (D 6) (R 6) [10,36,192,288,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13903 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13904 : Route 9 := (fun mask => (mask,id))

def c13904 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13904 : Upper (D 6) (R 6) [10,36,192,288,65,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288,65,1] 13 (by decide) (choices 1) [2,4,16] r13904 c13904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2980
  · exact u2981
  · exact u2982

def b13905 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 38 196 296 81 34 85 149 277), lower := (rows 11 38 196 296 81 34 64 128 256), losses := [] }

theorem u13905 : Upper (D 6) (R 6) [10,36,192,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13906 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 296 81 36 83 147 275), lower := (rows 11 38 196 296 81 36 64 128 256), losses := [] }

theorem u13906 : Upper (D 6) (R 6) [10,36,192,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13906 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13907 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 296 81 48 71 135 263), lower := (rows 11 38 196 296 81 48 64 128 256), losses := [] }

theorem u13907 : Upper (D 6) (R 6) [10,36,192,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13907 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13908 : Route 9 := (fun mask => (mask,id))

def c13908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13908 : Upper (D 6) (R 6) [10,36,192,288,66,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,288,66,1] 13 (by decide) (choices 1) [1,4,16] r13908 c13908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2983
  · exact u2984
  · exact u2985

def b13909 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 296 82 36 81 145 273), lower := (rows 11 38 196 296 82 36 64 128 256), losses := [] }

theorem u13909 : Upper (D 6) (R 6) [10,36,192,288,66,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13909 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13910 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 38 196 296 82 48 69 133 261), lower := (rows 11 38 196 296 82 48 64 128 256), losses := [] }

theorem u13910 : Upper (D 6) (R 6) [10,36,192,288,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13910 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r13911 : Route 9 := (fun mask => (mask,id))

def c13911 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u13911 : Upper (D 6) (R 6) [10,36,192,320,5,1] 13 := by
  apply FastRouting.sound _ _ [10,36,192,320,5,1] 13 (by decide) (choices 1) [2,16,32] r13911 c13911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2986
  · exact u2987
  · exact u2988

def b13912 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 34, targets := 65 }], pairs := [(1,0),(1,6),(3,2)], upper := (rows 11 38 196 328 21 34 113 177 305), lower := (rows 11 38 196 328 21 34 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 35 80 144 272), good := (rows 43 34 192 328 505 34 64 128 256) }] }

theorem u13912 : Upper (D 6) (R 6) [10,36,192,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13913 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 329, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 38 196 328 21 48 99 163 291), lower := (rows 11 38 196 328 21 48 64 128 256), losses := [] }

theorem u13913 : Upper (D 6) (R 6) [10,36,192,320,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13913 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13914 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 48, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 38 196 328 49 33 86 150 278), lower := (rows 11 38 196 328 49 33 64 128 256), losses := [] }

theorem u13914 : Upper (D 6) (R 6) [10,36,192,320,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13915 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 11 38 196 328 49 34 85 149 277), lower := (rows 11 38 196 328 49 34 64 128 256), losses := [] }

theorem u13915 : Upper (D 6) (R 6) [10,36,192,320,33,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13916 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 345, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 11 38 196 328 49 36 83 147 275), lower := (rows 11 38 196 328 49 36 64 128 256), losses := [] }

theorem u13916 : Upper (D 6) (R 6) [10,36,192,320,33,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13916 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13917 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 38 196 328 49 48 71 135 263), lower := (rows 11 38 196 328 49 48 64 128 256), losses := [] }

theorem u13917 : Upper (D 6) (R 6) [10,36,192,320,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13917 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13918 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 388 25 84 33 98 226 354), lower := (rows 11 38 388 25 84 33 64 128 256), losses := [] }

theorem u13918 : Upper (D 6) (R 6) [10,36,384,17,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b13919 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 388 25 84 34 97 225 353), lower := (rows 11 38 388 25 84 34 64 128 256), losses := [] }

theorem u13919 : Upper (D 6) (R 6) [10,36,384,17,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b13919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u13919
end Delivery.IrregularNine14.P06
