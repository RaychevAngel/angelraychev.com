import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0078

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b13860 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 392 145 113 113 241 369), lower := (rows 97 14 38 392 145 32 64 128 256), losses := [] }

theorem u13860 : Upper (D 8) (R 8) [96,12,34,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13861 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 392 176 113 81 209 337), lower := (rows 97 14 38 392 176 32 64 128 256), losses := [] }

theorem u13861 : Upper (D 8) (R 8) [96,12,34,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13862 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 38 392 208 49 113 177 305), lower := (rows 97 14 38 392 208 32 64 128 256), losses := [] }

theorem u13862 : Upper (D 8) (R 8) [96,12,34,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13863 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 145 418 482 418 418), lower := (rows 97 14 52 73 145 32 64 128 256), losses := [] }

theorem u13863 : Upper (D 8) (R 8) [96,12,48,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13864 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 146 417 481 417 417), lower := (rows 97 14 52 73 146 32 64 128 256), losses := [] }

theorem u13864 : Upper (D 8) (R 8) [96,12,48,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13865 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 273 162 226 162 418), lower := (rows 97 14 52 73 273 32 64 128 256), losses := [] }

theorem u13865 : Upper (D 8) (R 8) [96,12,48,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13866 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 274 161 225 161 417), lower := (rows 97 14 52 73 274 32 64 128 256), losses := [] }

theorem u13866 : Upper (D 8) (R 8) [96,12,48,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13867 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 400 163 227 163 419), lower := (rows 97 14 52 73 400 32 64 128 256), losses := [] }

theorem u13867 : Upper (D 8) (R 8) [96,12,48,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13868 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 74 145 417 481 417 417), lower := (rows 97 14 52 74 145 32 64 128 256), losses := [] }

theorem u13868 : Upper (D 8) (R 8) [96,12,48,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13869 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 74 273 161 225 161 417), lower := (rows 97 14 52 74 273 32 64 128 256), losses := [] }

theorem u13869 : Upper (D 8) (R 8) [96,12,48,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13870 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 74 400 161 225 161 417), lower := (rows 97 14 52 74 400 32 64 128 256), losses := [] }

theorem u13870 : Upper (D 8) (R 8) [96,12,48,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13871 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 145 419 451 387 387), lower := (rows 97 14 52 104 145 32 64 128 256), losses := [] }

theorem u13871 : Upper (D 8) (R 8) [96,12,48,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13872 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 146 417 449 385 385), lower := (rows 97 14 52 104 146 32 64 128 256), losses := [] }

theorem u13872 : Upper (D 8) (R 8) [96,12,48,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13873 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 273 163 195 131 387), lower := (rows 97 14 52 104 273 32 64 128 256), losses := [] }

theorem u13873 : Upper (D 8) (R 8) [96,12,48,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13874 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 274 161 193 129 385), lower := (rows 97 14 52 104 274 32 64 128 256), losses := [] }

theorem u13874 : Upper (D 8) (R 8) [96,12,48,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13875 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 400 163 195 131 387), lower := (rows 97 14 52 104 400 32 64 128 256), losses := [] }

theorem u13875 : Upper (D 8) (R 8) [96,12,48,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13876 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 137 49 482 450 450 450), lower := (rows 97 14 52 137 49 32 64 128 256), losses := [] }

theorem u13876 : Upper (D 8) (R 8) [96,12,48,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13877 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 137 50 481 449 449 449), lower := (rows 97 14 52 137 50 32 64 128 256), losses := [] }

theorem u13877 : Upper (D 8) (R 8) [96,12,48,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13878 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 137 81 418 482 418 418), lower := (rows 97 14 52 137 81 32 64 128 256), losses := [] }

theorem u13878 : Upper (D 8) (R 8) [96,12,48,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13879 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 52 137 82 417 481 417 417), lower := (rows 97 14 52 137 82 32 64 128 256), losses := [] }

theorem u13879 : Upper (D 8) (R 8) [96,12,48,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13880 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 137 112 419 451 387 387), lower := (rows 97 14 52 137 112 32 64 128 256), losses := [] }

theorem u13880 : Upper (D 8) (R 8) [96,12,48,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13881 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 52 137 145 354 354 482 354), lower := (rows 97 14 52 137 145 32 64 128 256), losses := [] }

theorem u13881 : Upper (D 8) (R 8) [96,12,48,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13882 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 146 353 353 481 353), lower := (rows 97 14 52 137 146 32 64 128 256), losses := [] }

theorem u13882 : Upper (D 8) (R 8) [96,12,48,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13883 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 137 176 355 323 451 323), lower := (rows 97 14 52 137 176 32 64 128 256), losses := [] }

theorem u13883 : Upper (D 8) (R 8) [96,12,48,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13884 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 208 291 355 419 291), lower := (rows 97 14 52 137 208 32 64 128 256), losses := [] }

theorem u13884 : Upper (D 8) (R 8) [96,12,48,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13885 : Route 9 := (fun mask => (mask,id))

def c13885 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13885 : Upper (D 8) (R 8) [96,12,48,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257] 13 (by decide) (choices 1) [2,64,128] r13885 c13885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4690
  · exact u4691
  · exact u4692

def r13886 : Route 9 := (fun mask => (mask,id))

def c13886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13886 : Upper (D 8) (R 8) [96,12,48,129,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,258] 13 (by decide) (choices 1) [1,64,128] r13886 c13886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4693
  · exact u4694
  · exact u4695

def b13887 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 137 304 227 195 195 451), lower := (rows 97 14 52 137 304 32 64 128 256), losses := [] }

theorem u13887 : Upper (D 8) (R 8) [96,12,48,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13888 : Route 9 := (fun mask => (mask,id))

def c13888 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13888 : Upper (D 8) (R 8) [96,12,48,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320] 13 (by decide) (choices 1) [1,2,128] r13888 c13888
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4696
  · exact u4697
  · exact u4698

def b13889 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 400 99 99 227 355), lower := (rows 97 14 52 137 400 32 64 128 256), losses := [] }

theorem u13889 : Upper (D 8) (R 8) [96,12,48,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13890 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 138 49 481 449 449 449), lower := (rows 97 14 52 138 49 32 64 128 256), losses := [] }

theorem u13890 : Upper (D 8) (R 8) [96,12,48,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13891 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 138 81 417 481 417 417), lower := (rows 97 14 52 138 81 32 64 128 256), losses := [] }

theorem u13891 : Upper (D 8) (R 8) [96,12,48,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13892 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 138 112 417 449 385 385), lower := (rows 97 14 52 138 112 32 64 128 256), losses := [] }

theorem u13892 : Upper (D 8) (R 8) [96,12,48,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13893 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 145 353 353 481 353), lower := (rows 97 14 52 138 145 32 64 128 256), losses := [] }

theorem u13893 : Upper (D 8) (R 8) [96,12,48,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13894 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 138 176 353 321 449 321), lower := (rows 97 14 52 138 176 32 64 128 256), losses := [] }

theorem u13894 : Upper (D 8) (R 8) [96,12,48,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13895 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 208 289 353 417 289), lower := (rows 97 14 52 138 208 32 64 128 256), losses := [] }

theorem u13895 : Upper (D 8) (R 8) [96,12,48,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13896 : Route 9 := (fun mask => (mask,id))

def c13896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13896 : Upper (D 8) (R 8) [96,12,48,130,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,257] 13 (by decide) (choices 1) [1,64,128] r13896 c13896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4699
  · exact u4700
  · exact u4701

def b13897 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 138 304 225 193 193 449), lower := (rows 97 14 52 138 304 32 64 128 256), losses := [] }

theorem u13897 : Upper (D 8) (R 8) [96,12,48,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13898 : Route 9 := (fun mask => (mask,id))

def c13898 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13898 : Upper (D 8) (R 8) [96,12,48,130,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,320] 13 (by decide) (choices 1) [1,128] r13898 c13898
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4702
  · exact u4703

def b13899 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 138 400 97 97 225 353), lower := (rows 97 14 52 138 400 32 64 128 256), losses := [] }

theorem u13899 : Upper (D 8) (R 8) [96,12,48,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13900 : PairBound 9 := { available := 387, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 168 81 419 451 387 387), lower := (rows 97 14 52 168 81 32 64 128 256), losses := [] }

theorem u13900 : Upper (D 8) (R 8) [96,12,48,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13901 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 52 168 82 417 449 385 385), lower := (rows 97 14 52 168 82 32 64 128 256), losses := [] }

theorem u13901 : Upper (D 8) (R 8) [96,12,48,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13902 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 145 355 323 451 323), lower := (rows 97 14 52 168 145 32 64 128 256), losses := [] }

theorem u13902 : Upper (D 8) (R 8) [96,12,48,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13903 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 52 168 146 353 321 449 321), lower := (rows 97 14 52 168 146 32 64 128 256), losses := [] }

theorem u13903 : Upper (D 8) (R 8) [96,12,48,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13904 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 208 291 323 387 259), lower := (rows 97 14 52 168 208 32 64 128 256), losses := [] }

theorem u13904 : Upper (D 8) (R 8) [96,12,48,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13905 : Route 9 := (fun mask => (mask,id))

def c13905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13905 : Upper (D 8) (R 8) [96,12,48,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,160,257] 13 (by decide) (choices 1) [1,2,64,128] r13905 c13905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4704
  · exact u4705
  · exact u4706
  · exact u4707

def r13906 : Route 9 := (fun mask => (mask,id))

def c13906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u13906 : Upper (D 8) (R 8) [96,12,48,160,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,160,258] 13 (by decide) (choices 1) [1,64,128] r13906 c13906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4708
  · exact u4709
  · exact u4710

def r13907 : Route 9 := (fun mask => (mask,id))

def c13907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13907 : Upper (D 8) (R 8) [96,12,48,160,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,160,320] 13 (by decide) (choices 1) [1,2,128] r13907 c13907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4711
  · exact u4712
  · exact u4713

def b13908 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 168 400 99 67 195 323), lower := (rows 97 14 52 168 400 32 64 128 256), losses := [] }

theorem u13908 : Upper (D 8) (R 8) [96,12,48,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13909 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 200 49 419 451 387 387), lower := (rows 97 14 52 200 49 32 64 128 256), losses := [] }

theorem u13909 : Upper (D 8) (R 8) [96,12,48,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13910 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 200 50 417 449 385 385), lower := (rows 97 14 52 200 50 32 64 128 256), losses := [] }

theorem u13910 : Upper (D 8) (R 8) [96,12,48,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13911 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 145 291 355 419 291), lower := (rows 97 14 52 200 145 32 64 128 256), losses := [] }

theorem u13911 : Upper (D 8) (R 8) [96,12,48,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13912 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 146 289 353 417 289), lower := (rows 97 14 52 200 146 32 64 128 256), losses := [] }

theorem u13912 : Upper (D 8) (R 8) [96,12,48,192,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13913 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 200 176 291 323 387 259), lower := (rows 97 14 52 200 176 32 64 128 256), losses := [] }

theorem u13913 : Upper (D 8) (R 8) [96,12,48,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r13914 : Route 9 := (fun mask => (mask,id))

def c13914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13914 : Upper (D 8) (R 8) [96,12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257] 13 (by decide) (choices 1) [1,2,128] r13914 c13914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4714
  · exact u4715
  · exact u4716

def r13915 : Route 9 := (fun mask => (mask,id))

def c13915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u13915 : Upper (D 8) (R 8) [96,12,48,192,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,258] 13 (by decide) (choices 1) [1,128] r13915 c13915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u4717
  · exact u4718

def b13916 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 200 304 163 195 131 387), lower := (rows 97 14 52 200 304 32 64 128 256), losses := [] }

theorem u13916 : Upper (D 8) (R 8) [96,12,48,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13917 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 400 35 99 163 291), lower := (rows 97 14 52 200 400 32 64 128 256), losses := [] }

theorem u13917 : Upper (D 8) (R 8) [96,12,48,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13918 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 20, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 265 49 226 194 194 450), lower := (rows 97 14 52 265 49 32 64 128 256), losses := [] }

theorem u13918 : Upper (D 8) (R 8) [96,12,48,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13919 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 14 52 265 50 225 193 193 449), lower := (rows 97 14 52 265 50 32 64 128 256), losses := [] }

theorem u13919 : Upper (D 8) (R 8) [96,12,48,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u13919
end Delivery.IrregularNine14.P08
