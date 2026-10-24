import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0033
import IrregularNine14P08C0034

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8880 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 28 41 304 225 193 193 449), lower := (rows 35 70 28 41 304 32 64 128 256), losses := [] }

theorem u8880 : Upper (D 8) (R 8) [34,68,24,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8881 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 28 41 400 225 225 225 481), lower := (rows 35 70 28 41 400 32 64 128 256), losses := [] }

theorem u8881 : Upper (D 8) (R 8) [34,68,24,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8882 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 145 416 480 416 416), lower := (rows 35 70 28 73 145 32 64 128 256), losses := [] }

theorem u8882 : Upper (D 8) (R 8) [34,68,24,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8883 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 176 417 481 417 417), lower := (rows 35 70 28 73 176 32 64 128 256), losses := [] }

theorem u8883 : Upper (D 8) (R 8) [34,68,24,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8884 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 273 160 224 160 416), lower := (rows 35 70 28 73 273 32 64 128 256), losses := [] }

theorem u8884 : Upper (D 8) (R 8) [34,68,24,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8885 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 304 161 225 161 417), lower := (rows 35 70 28 73 304 32 64 128 256), losses := [] }

theorem u8885 : Upper (D 8) (R 8) [34,68,24,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8886 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 400 161 225 161 417), lower := (rows 35 70 28 73 400 32 64 128 256), losses := [] }

theorem u8886 : Upper (D 8) (R 8) [34,68,24,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8887 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 145 417 481 417 417), lower := (rows 35 70 28 104 145 32 64 128 256), losses := [] }

theorem u8887 : Upper (D 8) (R 8) [34,68,24,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8888 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 176 417 449 385 385), lower := (rows 35 70 28 104 176 32 64 128 256), losses := [] }

theorem u8888 : Upper (D 8) (R 8) [34,68,24,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8889 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 273 161 225 161 417), lower := (rows 35 70 28 104 273 32 64 128 256), losses := [] }

theorem u8889 : Upper (D 8) (R 8) [34,68,24,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8890 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 304 161 193 129 385), lower := (rows 35 70 28 104 304 32 64 128 256), losses := [] }

theorem u8890 : Upper (D 8) (R 8) [34,68,24,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8890 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8891 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 400 161 225 161 417), lower := (rows 35 70 28 104 400 32 64 128 256), losses := [] }

theorem u8891 : Upper (D 8) (R 8) [34,68,24,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8891 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8892 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 28 137 145 352 352 480 352), lower := (rows 35 70 28 137 145 32 64 128 256), losses := [] }

theorem u8892 : Upper (D 8) (R 8) [34,68,24,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8892 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8893 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 137 176 353 353 481 353), lower := (rows 35 70 28 137 176 32 64 128 256), losses := [] }

theorem u8893 : Upper (D 8) (R 8) [34,68,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8893 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8894 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 208 289 353 417 289), lower := (rows 35 70 28 137 208 32 64 128 256), losses := [] }

theorem u8894 : Upper (D 8) (R 8) [34,68,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8895 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 28 137 273 224 224 224 480), lower := (rows 35 70 28 137 273 32 64 128 256), losses := [] }

theorem u8895 : Upper (D 8) (R 8) [34,68,24,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8896 : Route 9 := (fun mask => (mask,id))

def c8896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8896 : Upper (D 8) (R 8) [34,68,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,288] 13 (by decide) (choices 1) [1,64,128] r8896 c8896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2027
  · exact u2028
  · exact u2029

def b8897 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 336 161 225 161 417), lower := (rows 35 70 28 137 336 32 64 128 256), losses := [] }

theorem u8897 : Upper (D 8) (R 8) [34,68,24,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8898 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 137 400 97 97 225 353), lower := (rows 35 70 28 137 400 32 64 128 256), losses := [] }

theorem u8898 : Upper (D 8) (R 8) [34,68,24,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8899 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 28 168 176 353 321 449 321), lower := (rows 35 70 28 168 176 32 64 128 256), losses := [] }

theorem u8899 : Upper (D 8) (R 8) [34,68,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8900 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 168 208 289 353 417 289), lower := (rows 35 70 28 168 208 32 64 128 256), losses := [] }

theorem u8900 : Upper (D 8) (R 8) [34,68,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8901 : Route 9 := (fun mask => (mask,id))

def c8901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8901 : Upper (D 8) (R 8) [34,68,24,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,257] 13 (by decide) (choices 1) [1,64,128] r8901 c8901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2030
  · exact u2031
  · exact u2032

def r8902 : Route 9 := (fun mask => (mask,id))

def c8902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8902 : Upper (D 8) (R 8) [34,68,24,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,24,160,288] 13 (by decide) (choices 1) [1,64,128] r8902 c8902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2033
  · exact u2034
  · exact u2035

def b8903 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 168 336 161 225 161 417), lower := (rows 35 70 28 168 336 32 64 128 256), losses := [] }

theorem u8903 : Upper (D 8) (R 8) [34,68,24,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8904 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 168 400 97 97 225 353), lower := (rows 35 70 28 168 400 32 64 128 256), losses := [] }

theorem u8904 : Upper (D 8) (R 8) [34,68,24,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8905 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 273 161 225 161 417), lower := (rows 35 70 28 200 273 32 64 128 256), losses := [] }

theorem u8905 : Upper (D 8) (R 8) [34,68,24,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8906 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 304 161 225 161 417), lower := (rows 35 70 28 200 304 32 64 128 256), losses := [] }

theorem u8906 : Upper (D 8) (R 8) [34,68,24,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8907 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 400 33 97 161 289), lower := (rows 35 70 28 200 400 32 64 128 256), losses := [] }

theorem u8907 : Upper (D 8) (R 8) [34,68,24,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8908 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 25 49 480 448 448 448), lower := (rows 35 70 44 25 49 32 64 128 256), losses := [] }

theorem u8908 : Upper (D 8) (R 8) [34,68,40,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8909 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 44 25 81 416 480 416 416), lower := (rows 35 70 44 25 81 32 64 128 256), losses := [] }

theorem u8909 : Upper (D 8) (R 8) [34,68,40,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8910 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 25 112 417 449 385 385), lower := (rows 35 70 44 25 112 32 64 128 256), losses := [] }

theorem u8910 : Upper (D 8) (R 8) [34,68,40,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8910 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8911 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 44 25 145 480 480 480 480), lower := (rows 35 70 44 25 145 32 64 128 256), losses := [] }

theorem u8911 : Upper (D 8) (R 8) [34,68,40,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8911 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8912 : PairBound 9 := { available := 449, camps := [], pairs := [(1,5)], upper := (rows 35 70 44 25 176 481 449 449 449), lower := (rows 35 70 44 25 176 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 137 265), good := (rows 451 70 462 473 144 0 64 128 256) }] }

theorem u8912 : Upper (D 8) (R 8) [34,68,40,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8912 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8913 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 25 208 417 481 417 417), lower := (rows 35 70 44 25 208 32 64 128 256), losses := [] }

theorem u8913 : Upper (D 8) (R 8) [34,68,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8914 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 44 25 273 224 224 224 480), lower := (rows 35 70 44 25 273 32 64 128 256), losses := [] }

theorem u8914 : Upper (D 8) (R 8) [34,68,40,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8915 : PairBound 9 := { available := 193, camps := [], pairs := [(1,5)], upper := (rows 35 70 44 25 304 225 193 193 449), lower := (rows 35 70 44 25 304 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 137 265), good := (rows 451 70 462 473 272 0 64 128 256) }] }

theorem u8915 : Upper (D 8) (R 8) [34,68,40,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8916 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 25 336 161 225 161 417), lower := (rows 35 70 44 25 336 32 64 128 256), losses := [] }

theorem u8916 : Upper (D 8) (R 8) [34,68,40,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8917 : Route 9 := (fun mask => (mask,id))

def c8917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8917 : Upper (D 8) (R 8) [34,68,40,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,17,384] 13 (by decide) (choices 1) [1,64,128] r8917 c8917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2036
  · exact u2037
  · exact u2038

def b8918 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 137 49 496 464 464 464), lower := (rows 35 70 44 137 49 32 64 128 256), losses := [] }

theorem u8918 : Upper (D 8) (R 8) [34,68,40,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8919 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 137 81 432 496 432 432), lower := (rows 35 70 44 137 81 32 64 128 256), losses := [] }

theorem u8919 : Upper (D 8) (R 8) [34,68,40,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8919 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8920 : Route 9 := (fun mask => (mask,id))

def c8920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8920 : Upper (D 8) (R 8) [34,68,40,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,96] 13 (by decide) (choices 1) [1,16,128,256] r8920 c8920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2039
  · exact u2040
  · exact u2041
  · exact u2042

def b8921 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 44 137 145 368 368 496 368), lower := (rows 35 70 44 137 145 32 64 128 256), losses := [] }

theorem u8921 : Upper (D 8) (R 8) [34,68,40,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8921 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8922 : Route 9 := (fun mask => (mask,id))

def c8922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8922 : Upper (D 8) (R 8) [34,68,40,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,160] 13 (by decide) (choices 1) [1,16,64,256] r8922 c8922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2043
  · exact u2044
  · exact u2045
  · exact u2046

def r8923 : Route 9 := (fun mask => (mask,id))

def c8923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8923 : Upper (D 8) (R 8) [34,68,40,129,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192] 13 (by decide) (choices 1) [1,16,256] r8923 c8923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2047
  · exact u2048
  · exact u2049

def r8924 : Route 9 := (fun mask => (mask,id))

def c8924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8924 : Upper (D 8) (R 8) [34,68,40,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,257] 13 (by decide) (choices 1) [16,64,128] r8924 c8924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2050
  · exact u2051
  · exact u2052

def r8925 : Route 9 := (fun mask => (mask,id))

def c8925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8925 : Upper (D 8) (R 8) [34,68,40,129,288] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,288] 13 (by decide) (choices 1) [1,16,64,128] r8925 c8925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2053
  · exact u2054
  · exact u2055
  · exact u2056

def r8926 : Route 9 := (fun mask => (mask,id))

def c8926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8926 : Upper (D 8) (R 8) [34,68,40,129,320] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,320] 13 (by decide) (choices 1) [1,16,128] r8926 c8926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2057
  · exact u2058
  · exact u2059

def r8927 : Route 9 := (fun mask => (mask,id))

def c8927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8927 : Upper (D 8) (R 8) [34,68,40,129,384] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,384] 13 (by decide) (choices 1) [1,16,64] r8927 c8927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2060
  · exact u2061
  · exact u2062

def b8928 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 152 49 481 449 449 449), lower := (rows 35 70 44 152 49 32 64 128 256), losses := [] }

theorem u8928 : Upper (D 8) (R 8) [34,68,40,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8928 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8929 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 152 81 417 481 417 417), lower := (rows 35 70 44 152 81 32 64 128 256), losses := [] }

theorem u8929 : Upper (D 8) (R 8) [34,68,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8929 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8930 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 152 112 417 449 385 385), lower := (rows 35 70 44 152 112 32 64 128 256), losses := [] }

theorem u8930 : Upper (D 8) (R 8) [34,68,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8930 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8931 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 145 353 353 481 353), lower := (rows 35 70 44 152 145 32 64 128 256), losses := [] }

theorem u8931 : Upper (D 8) (R 8) [34,68,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8931 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8932 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 70 44 152 176 353 321 449 321), lower := (rows 35 70 44 152 176 32 64 128 256), losses := [] }

theorem u8932 : Upper (D 8) (R 8) [34,68,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8932 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8933 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 208 289 353 417 289), lower := (rows 35 70 44 152 208 32 64 128 256), losses := [] }

theorem u8933 : Upper (D 8) (R 8) [34,68,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8933 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8934 : Route 9 := (fun mask => (mask,id))

def c8934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8934 : Upper (D 8) (R 8) [34,68,40,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,257] 13 (by decide) (choices 1) [1,64,128] r8934 c8934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2063
  · exact u2064
  · exact u2065

def r8935 : Route 9 := (fun mask => (mask,id))

def c8935 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8935 : Upper (D 8) (R 8) [34,68,40,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,40,144,288] 13 (by decide) (choices 1) [1,64,128] r8935 c8935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2066
  · exact u2067
  · exact u2068

def b8936 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 44 152 336 161 225 161 417), lower := (rows 35 70 44 152 336 32 64 128 256), losses := [] }

theorem u8936 : Upper (D 8) (R 8) [34,68,40,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8937 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 44 152 400 97 97 225 353), lower := (rows 35 70 44 152 400 32 64 128 256), losses := [] }

theorem u8937 : Upper (D 8) (R 8) [34,68,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8938 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 44 265 49 240 208 208 464), lower := (rows 35 70 44 265 49 32 64 128 256), losses := [] }

theorem u8938 : Upper (D 8) (R 8) [34,68,40,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8938 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8939 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 44 265 81 176 240 176 432), lower := (rows 35 70 44 265 81 32 64 128 256), losses := [] }

theorem u8939 : Upper (D 8) (R 8) [34,68,40,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8939 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8939
end Delivery.IrregularNine14.P08
