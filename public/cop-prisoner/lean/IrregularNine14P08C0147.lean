import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0032
import IrregularNine14P08C0033

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8820 : Route 9 := (fun mask => (mask,id))

def c8820 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8820 : Upper (D 8) (R 8) [34,65,136,288,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,160] 13 (by decide) (choices 1) [1,4,16,64] r8820 c8820
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1963
  · exact u1964
  · exact u1965
  · exact u1966

def r8821 : Route 9 := (fun mask => (mask,id))

def c8821 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8821 : Upper (D 8) (R 8) [34,65,136,288,192] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288,192] 13 (by decide) (choices 1) [1,4,16] r8821 c8821
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1967
  · exact u1968
  · exact u1969

def r8822 : Route 9 := (fun mask => (mask,id))

def c8822 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8822 : Upper (D 8) (R 8) [34,65,136,320,160] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320,160] 13 (by decide) (choices 1) [1,4,16] r8822 c8822
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1970
  · exact u1971
  · exact u1972

def b8823 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 164 168 276 121 89 217 345), lower := (rows 35 67 164 168 276 32 64 128 256), losses := [] }

theorem u8823 : Upper (D 8) (R 8) [34,65,160,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8824 : PairBound 9 := { available := 29, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 67 164 168 336 61 93 157 285), lower := (rows 35 67 164 168 336 32 64 128 256), losses := [] }

theorem u8824 : Upper (D 8) (R 8) [34,65,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8825 : PairBound 9 := { available := 60, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 164 200 273 60 124 188 316), lower := (rows 35 67 164 200 273 32 64 128 256), losses := [] }

theorem u8825 : Upper (D 8) (R 8) [34,65,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8826 : Route 9 := (fun mask => (mask,id))

def c8826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8826 : Upper (D 8) (R 8) [34,65,160,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,260] 13 (by decide) (choices 1) [1,8,16] r8826 c8826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1973
  · exact u1974
  · exact u1975

def r8827 : Route 9 := (fun mask => (mask,id))

def c8827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8827 : Upper (D 8) (R 8) [34,65,160,192,264] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,264] 13 (by decide) (choices 1) [1,4,16] r8827 c8827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1976
  · exact u1977
  · exact u1978

def r8828 : Route 9 := (fun mask => (mask,id))

def c8828 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8828 : Upper (D 8) (R 8) [34,65,160,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192,288] 13 (by decide) (choices 1) [1,4,8,16] r8828 c8828
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1979
  · exact u1980
  · exact u1981
  · exact u1982

def b8829 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 28, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 56 49 480 448 448 448), lower := (rows 35 70 13 56 49 32 64 128 256), losses := [] }

theorem u8829 : Upper (D 8) (R 8) [34,68,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8830 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 56 81 416 480 416 416), lower := (rows 35 70 13 56 81 32 64 128 256), losses := [] }

theorem u8830 : Upper (D 8) (R 8) [34,68,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8831 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 56 112 417 449 385 385), lower := (rows 35 70 13 56 112 32 64 128 256), losses := [] }

theorem u8831 : Upper (D 8) (R 8) [34,68,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8832 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 13 56 145 480 480 480 480), lower := (rows 35 70 13 56 145 32 64 128 256), losses := [] }

theorem u8832 : Upper (D 8) (R 8) [34,68,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8833 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 56 176 481 449 449 449), lower := (rows 35 70 13 56 176 32 64 128 256), losses := [] }

theorem u8833 : Upper (D 8) (R 8) [34,68,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8834 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 56 208 417 481 417 417), lower := (rows 35 70 13 56 208 32 64 128 256), losses := [] }

theorem u8834 : Upper (D 8) (R 8) [34,68,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8835 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 13 56 273 224 224 224 480), lower := (rows 35 70 13 56 273 32 64 128 256), losses := [] }

theorem u8835 : Upper (D 8) (R 8) [34,68,9,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8836 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 56 304 225 193 193 449), lower := (rows 35 70 13 56 304 32 64 128 256), losses := [] }

theorem u8836 : Upper (D 8) (R 8) [34,68,9,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8837 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 56 336 161 225 161 417), lower := (rows 35 70 13 56 336 32 64 128 256), losses := [] }

theorem u8837 : Upper (D 8) (R 8) [34,68,9,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8838 : Route 9 := (fun mask => (mask,id))

def c8838 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8838 : Upper (D 8) (R 8) [34,68,9,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,48,384] 13 (by decide) (choices 1) [1,64,128] r8838 c8838
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1983
  · exact u1984
  · exact u1985

def b8839 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 13 152 49 480 480 480 480), lower := (rows 35 70 13 152 49 32 64 128 256), losses := [] }

theorem u8839 : Upper (D 8) (R 8) [34,68,9,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8840 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 152 81 416 480 416 416), lower := (rows 35 70 13 152 81 32 64 128 256), losses := [] }

theorem u8840 : Upper (D 8) (R 8) [34,68,9,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8841 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 152 112 417 481 417 417), lower := (rows 35 70 13 152 112 32 64 128 256), losses := [] }

theorem u8841 : Upper (D 8) (R 8) [34,68,9,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8842 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 13 152 145 352 352 480 352), lower := (rows 35 70 13 152 145 32 64 128 256), losses := [] }

theorem u8842 : Upper (D 8) (R 8) [34,68,9,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8843 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 176 353 353 481 353), lower := (rows 35 70 13 152 176 32 64 128 256), losses := [] }

theorem u8843 : Upper (D 8) (R 8) [34,68,9,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8844 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 208 289 353 417 289), lower := (rows 35 70 13 152 208 32 64 128 256), losses := [] }

theorem u8844 : Upper (D 8) (R 8) [34,68,9,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8845 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 13 152 273 224 224 224 480), lower := (rows 35 70 13 152 273 32 64 128 256), losses := [] }

theorem u8845 : Upper (D 8) (R 8) [34,68,9,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8846 : Route 9 := (fun mask => (mask,id))

def c8846 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8846 : Upper (D 8) (R 8) [34,68,9,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144,288] 13 (by decide) (choices 1) [1,64,128] r8846 c8846
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1986
  · exact u1987
  · exact u1988

def b8847 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 152 336 161 225 161 417), lower := (rows 35 70 13 152 336 32 64 128 256), losses := [] }

theorem u8847 : Upper (D 8) (R 8) [34,68,9,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8848 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 152 400 97 97 225 353), lower := (rows 35 70 13 152 400 32 64 128 256), losses := [] }

theorem u8848 : Upper (D 8) (R 8) [34,68,9,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8849 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 13 168 49 496 464 464 464), lower := (rows 35 70 13 168 49 32 64 128 256), losses := [] }

theorem u8849 : Upper (D 8) (R 8) [34,68,9,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8850 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 168 81 432 496 432 432), lower := (rows 35 70 13 168 81 32 64 128 256), losses := [] }

theorem u8850 : Upper (D 8) (R 8) [34,68,9,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8851 : Route 9 := (fun mask => (mask,id))

def c8851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8851 : Upper (D 8) (R 8) [34,68,9,160,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,96] 13 (by decide) (choices 1) [1,16,128,256] r8851 c8851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1989
  · exact u1990
  · exact u1991
  · exact u1992

def b8852 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 145 368 368 496 368), lower := (rows 35 70 13 168 145 32 64 128 256), losses := [] }

theorem u8852 : Upper (D 8) (R 8) [34,68,9,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8853 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 70 13 168 176 369 337 465 337), lower := (rows 35 70 13 168 176 32 64 128 256), losses := [] }

theorem u8853 : Upper (D 8) (R 8) [34,68,9,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8854 : Route 9 := (fun mask => (mask,id))

def c8854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8854 : Upper (D 8) (R 8) [34,68,9,160,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,192] 13 (by decide) (choices 1) [1,16,256] r8854 c8854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1993
  · exact u1994
  · exact u1995

def b8855 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 232, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 168 273 240 240 240 496), lower := (rows 35 70 13 168 273 32 64 128 256), losses := [] }

theorem u8855 : Upper (D 8) (R 8) [34,68,9,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8856 : Route 9 := (fun mask => (mask,id))

def c8856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8856 : Upper (D 8) (R 8) [34,68,9,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,288] 13 (by decide) (choices 1) [1,16,64,128] r8856 c8856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1996
  · exact u1997
  · exact u1998
  · exact u1999

def r8857 : Route 9 := (fun mask => (mask,id))

def c8857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8857 : Upper (D 8) (R 8) [34,68,9,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,320] 13 (by decide) (choices 1) [1,16,128] r8857 c8857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2000
  · exact u2001
  · exact u2002

def r8858 : Route 9 := (fun mask => (mask,id))

def c8858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8858 : Upper (D 8) (R 8) [34,68,9,160,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,160,384] 13 (by decide) (choices 1) [1,16,64] r8858 c8858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2003
  · exact u2004
  · exact u2005

def b8859 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 13 280 49 224 224 224 480), lower := (rows 35 70 13 280 49 32 64 128 256), losses := [] }

theorem u8859 : Upper (D 8) (R 8) [34,68,9,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8860 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 280 81 160 224 160 416), lower := (rows 35 70 13 280 81 32 64 128 256), losses := [] }

theorem u8860 : Upper (D 8) (R 8) [34,68,9,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8861 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 280 112 161 225 161 417), lower := (rows 35 70 13 280 112 32 64 128 256), losses := [] }

theorem u8861 : Upper (D 8) (R 8) [34,68,9,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8862 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 13 280 145 224 224 224 480), lower := (rows 35 70 13 280 145 32 64 128 256), losses := [] }

theorem u8862 : Upper (D 8) (R 8) [34,68,9,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8863 : Route 9 := (fun mask => (mask,id))

def c8863 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u8863 : Upper (D 8) (R 8) [34,68,9,272,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272,160] 13 (by decide) (choices 1) [1,64,128] r8863 c8863
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2006
  · exact u2007
  · exact u2008

def b8864 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 280 208 161 225 161 417), lower := (rows 35 70 13 280 208 32 64 128 256), losses := [] }

theorem u8864 : Upper (D 8) (R 8) [34,68,9,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8865 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 13 296 49 240 208 208 464), lower := (rows 35 70 13 296 49 32 64 128 256), losses := [] }

theorem u8865 : Upper (D 8) (R 8) [34,68,9,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8866 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 296 81 176 240 176 432), lower := (rows 35 70 13 296 81 32 64 128 256), losses := [] }

theorem u8866 : Upper (D 8) (R 8) [34,68,9,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8867 : Route 9 := (fun mask => (mask,id))

def c8867 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8867 : Upper (D 8) (R 8) [34,68,9,288,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,96] 13 (by decide) (choices 1) [1,16,128] r8867 c8867
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2009
  · exact u2010
  · exact u2011

def b8868 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 296 145 240 240 240 496), lower := (rows 35 70 13 296 145 32 64 128 256), losses := [] }

theorem u8868 : Upper (D 8) (R 8) [34,68,9,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8869 : Route 9 := (fun mask => (mask,id))

def c8869 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8869 : Upper (D 8) (R 8) [34,68,9,288,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,160] 13 (by decide) (choices 1) [1,16,64,128] r8869 c8869
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2012
  · exact u2013
  · exact u2014
  · exact u2015

def r8870 : Route 9 := (fun mask => (mask,id))

def c8870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8870 : Upper (D 8) (R 8) [34,68,9,288,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,288,192] 13 (by decide) (choices 1) [1,16,128] r8870 c8870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2016
  · exact u2017
  · exact u2018

def b8871 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 35 70 13 392 49 240 240 240 496), lower := (rows 35 70 13 392 49 32 64 128 256), losses := [] }

theorem u8871 : Upper (D 8) (R 8) [34,68,9,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8872 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 392 81 176 240 176 432), lower := (rows 35 70 13 392 81 32 64 128 256), losses := [] }

theorem u8872 : Upper (D 8) (R 8) [34,68,9,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8873 : Route 9 := (fun mask => (mask,id))

def c8873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8873 : Upper (D 8) (R 8) [34,68,9,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,96] 13 (by decide) (choices 1) [1,16,128] r8873 c8873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2019
  · exact u2020
  · exact u2021

def b8874 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 13 392 145 112 112 240 368), lower := (rows 35 70 13 392 145 32 64 128 256), losses := [] }

theorem u8874 : Upper (D 8) (R 8) [34,68,9,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r8875 : Route 9 := (fun mask => (mask,id))

def c8875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8875 : Upper (D 8) (R 8) [34,68,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,160] 13 (by decide) (choices 1) [1,16,64] r8875 c8875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2022
  · exact u2023
  · exact u2024

def r8876 : Route 9 := (fun mask => (mask,id))

def c8876 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8876 : Upper (D 8) (R 8) [34,68,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384,192] 13 (by decide) (choices 1) [1,16] r8876 c8876
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2025
  · exact u2026

def b8877 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 28 41 145 480 480 480 480), lower := (rows 35 70 28 41 145 32 64 128 256), losses := [] }

theorem u8877 : Upper (D 8) (R 8) [34,68,24,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8877 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8878 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 28 41 176 481 449 449 449), lower := (rows 35 70 28 41 176 32 64 128 256), losses := [] }

theorem u8878 : Upper (D 8) (R 8) [34,68,24,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8878 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8879 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 28 41 273 224 224 224 480), lower := (rows 35 70 28 41 273 32 64 128 256), losses := [] }

theorem u8879 : Upper (D 8) (R 8) [34,68,24,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8879 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u8879
end Delivery.IrregularNine14.P08
