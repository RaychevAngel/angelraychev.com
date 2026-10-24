import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0012
import IrregularNine14P10C0013

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2040 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2040 : Upper (D 10) (R 10) [34,68,40,384,96] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,96] 13 (by decide) (choices 1) [1,16,128] r2040 c2040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u758
  · exact u759
  · exact u760

def r2041 : Route 9 := (fun mask => (mask,id))

def c2041 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2041 : Upper (D 10) (R 10) [34,68,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,129] 13 (by decide) (choices 1) [16,64,256] r2041 c2041
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u761
  · exact u762
  · exact u763

def r2042 : Route 9 := (fun mask => (mask,id))

def c2042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2042 : Upper (D 10) (R 10) [34,68,40,384,160] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,160] 13 (by decide) (choices 1) [1,16,64,256] r2042 c2042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u764
  · exact u765
  · exact u766
  · exact u767

def r2043 : Route 9 := (fun mask => (mask,id))

def c2043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2043 : Upper (D 10) (R 10) [34,68,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,192] 13 (by decide) (choices 1) [1,16,256] r2043 c2043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u768
  · exact u769
  · exact u770

def b2044 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 35 70 44 392 400 113 113 241 369), lower := (rows 35 70 44 392 400 32 64 128 256), losses := [] }

theorem u2044 : Upper (D 10) (R 10) [34,68,40,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2044 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 56 400 424 488 424 424), lower := (rows 35 70 69 56 400 32 64 128 256), losses := [] }

theorem u2045 : Upper (D 10) (R 10) [34,68,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2045 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 152 280 416 480 416 416), lower := (rows 35 70 69 152 280 32 64 128 256), losses := [] }

theorem u2046 : Upper (D 10) (R 10) [34,68,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2046 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2047 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 152 304 424 488 424 424), lower := (rows 35 70 69 152 304 32 64 128 256), losses := [] }

theorem u2047 : Upper (D 10) (R 10) [34,68,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2047 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2048 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 168 304 440 472 408 408), lower := (rows 35 70 69 168 304 32 64 128 256), losses := [] }

theorem u2048 : Upper (D 10) (R 10) [34,68,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2048 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 69 168 400 312 376 440 312), lower := (rows 35 70 69 168 400 32 64 128 256), losses := [] }

theorem u2049 : Upper (D 10) (R 10) [34,68,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2049 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 56 400 417 481 417 417), lower := (rows 35 70 76 56 400 32 64 128 256), losses := [] }

theorem u2050 : Upper (D 10) (R 10) [34,68,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2050 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 137 176 304 368 432 304), lower := (rows 35 70 76 137 176 32 64 128 256), losses := [] }

theorem u2051 : Upper (D 10) (R 10) [34,68,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2051 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 137 304 432 496 432 432), lower := (rows 35 70 76 137 304 32 64 128 256), losses := [] }

theorem u2052 : Upper (D 10) (R 10) [34,68,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2052 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 137 400 304 368 432 304), lower := (rows 35 70 76 137 400 32 64 128 256), losses := [] }

theorem u2053 : Upper (D 10) (R 10) [34,68,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2053 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 152 273 416 480 416 416), lower := (rows 35 70 76 152 273 32 64 128 256), losses := [] }

theorem u2054 : Upper (D 10) (R 10) [34,68,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2054 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 152 304 417 481 417 417), lower := (rows 35 70 76 152 304 32 64 128 256), losses := [] }

theorem u2055 : Upper (D 10) (R 10) [34,68,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2055 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 168 145 304 368 432 304), lower := (rows 35 70 76 168 145 32 64 128 256), losses := [] }

theorem u2056 : Upper (D 10) (R 10) [34,68,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2056 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 168 273 432 496 432 432), lower := (rows 35 70 76 168 273 32 64 128 256), losses := [] }

theorem u2057 : Upper (D 10) (R 10) [34,68,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2057 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 168 304 433 465 401 401), lower := (rows 35 70 76 168 304 32 64 128 256), losses := [] }

theorem u2058 : Upper (D 10) (R 10) [34,68,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2058 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 168 400 305 369 433 305), lower := (rows 35 70 76 168 400 32 64 128 256), losses := [] }

theorem u2059 : Upper (D 10) (R 10) [34,68,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2059 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 392 145 304 368 432 304), lower := (rows 35 70 76 392 145 32 64 128 256), losses := [] }

theorem u2060 : Upper (D 10) (R 10) [34,68,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2060 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 76 392 176 305 369 433 305), lower := (rows 35 70 76 392 176 32 64 128 256), losses := [] }

theorem u2061 : Upper (D 10) (R 10) [34,68,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2061 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 56 400 425 457 393 393), lower := (rows 35 70 100 56 400 32 64 128 256), losses := [] }

theorem u2062 : Upper (D 10) (R 10) [34,68,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2062 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 137 176 312 344 408 280), lower := (rows 35 70 100 137 176 32 64 128 256), losses := [] }

theorem u2063 : Upper (D 10) (R 10) [34,68,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2063 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 137 280 432 496 432 432), lower := (rows 35 70 100 137 280 32 64 128 256), losses := [] }

theorem u2064 : Upper (D 10) (R 10) [34,68,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2064 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 137 304 440 472 408 408), lower := (rows 35 70 100 137 304 32 64 128 256), losses := [] }

theorem u2065 : Upper (D 10) (R 10) [34,68,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2065 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2066 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 137 400 312 376 440 312), lower := (rows 35 70 100 137 400 32 64 128 256), losses := [] }

theorem u2066 : Upper (D 10) (R 10) [34,68,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2066 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2067 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 152 280 417 481 417 417), lower := (rows 35 70 100 152 280 32 64 128 256), losses := [] }

theorem u2067 : Upper (D 10) (R 10) [34,68,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2067 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 152 304 425 457 393 393), lower := (rows 35 70 100 152 304 32 64 128 256), losses := [] }

theorem u2068 : Upper (D 10) (R 10) [34,68,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2068 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 70 100 168 400 313 345 409 281), lower := (rows 35 70 100 168 400 32 64 128 256), losses := [] }

theorem u2069 : Upper (D 10) (R 10) [34,68,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2069 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 35 70 133 56 112 424 456 392 392), lower := (rows 35 70 133 56 112 32 64 128 256), losses := [] }

theorem u2070 : Upper (D 10) (R 10) [34,68,129,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2070 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 328, camps := [{ cop := 4, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 35 70 133 56 176 360 328 456 328), lower := (rows 35 70 133 56 176 32 64 128 256), losses := [] }

theorem u2071 : Upper (D 10) (R 10) [34,68,129,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2071 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 296, targets := 64 },{ cop := 4, region := 296, targets := 128 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 133 56 208 296 360 424 296), lower := (rows 35 70 133 56 208 32 64 128 256), losses := [] }

theorem u2072 : Upper (D 10) (R 10) [34,68,129,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2072 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 35 70 133 56 304 488 456 456 456), lower := (rows 35 70 133 56 304 32 64 128 256), losses := [] }

theorem u2073 : Upper (D 10) (R 10) [34,68,129,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2073 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2074 : Route 9 := (fun mask => (mask,id))

def c2074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2074 : Upper (D 10) (R 10) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [8,128,256] r2074 c2074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u771
  · exact u772
  · exact u773

def r2075 : Route 9 := (fun mask => (mask,id))

def c2075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2075 : Upper (D 10) (R 10) [34,68,129,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,384] 13 (by decide) (choices 1) [8,64,256] r2075 c2075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u774
  · exact u775
  · exact u776

def b2076 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 88 152 288 352 416 288), lower := (rows 35 70 133 88 152 32 64 128 256), losses := [] }

theorem u2076 : Upper (D 10) (R 10) [34,68,129,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2076 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 88 176 296 360 424 296), lower := (rows 35 70 133 88 176 32 64 128 256), losses := [] }

theorem u2077 : Upper (D 10) (R 10) [34,68,129,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2077 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 88 280 416 480 416 416), lower := (rows 35 70 133 88 280 32 64 128 256), losses := [] }

theorem u2078 : Upper (D 10) (R 10) [34,68,129,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2078 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2079 : Route 9 := (fun mask => (mask,id))

def c2079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2079 : Upper (D 10) (R 10) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [8,128,256] r2079 c2079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u777
  · exact u778
  · exact u779

def b2080 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 88 400 296 360 424 296), lower := (rows 35 70 133 88 400 32 64 128 256), losses := [] }

theorem u2080 : Upper (D 10) (R 10) [34,68,129,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2080 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 104 152 304 368 432 304), lower := (rows 35 70 133 104 152 32 64 128 256), losses := [] }

theorem u2081 : Upper (D 10) (R 10) [34,68,129,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2081 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 104 176 312 344 408 280), lower := (rows 35 70 133 104 176 32 64 128 256), losses := [] }

theorem u2082 : Upper (D 10) (R 10) [34,68,129,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2082 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2083 : Route 9 := (fun mask => (mask,id))

def c2083 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2083 : Upper (D 10) (R 10) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [16,128,256] r2083 c2083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u780
  · exact u781
  · exact u782

def r2084 : Route 9 := (fun mask => (mask,id))

def c2084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u2084 : Upper (D 10) (R 10) [34,68,129,96,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,288] 13 (by decide) (choices 1) [8,16,128,256] r2084 c2084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u783
  · exact u784
  · exact u785
  · exact u786

def b2085 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 35 70 133 104 400 312 376 440 312), lower := (rows 35 70 133 104 400 32 64 128 256), losses := [] }

theorem u2085 : Upper (D 10) (R 10) [34,68,129,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2085 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 133 152 280 352 352 480 352), lower := (rows 35 70 133 152 280 32 64 128 256), losses := [] }

theorem u2086 : Upper (D 10) (R 10) [34,68,129,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2086 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2087 : Route 9 := (fun mask => (mask,id))

def c2087 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u2087 : Upper (D 10) (R 10) [34,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,288] 13 (by decide) (choices 1) [8,64,256] r2087 c2087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u787
  · exact u788
  · exact u789

def b2088 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 368, targets := 128 },{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6),(4,7)], upper := (rows 35 70 133 152 336 296 360 424 296), lower := (rows 35 70 133 152 336 32 64 128 256), losses := [] }

theorem u2088 : Upper (D 10) (R 10) [34,68,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2088 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2089 : Route 9 := (fun mask => (mask,id))

def c2089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u2089 : Upper (D 10) (R 10) [34,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264] 13 (by decide) (choices 1) [16,64,256] r2089 c2089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u790
  · exact u791
  · exact u792

def r2090 : Route 9 := (fun mask => (mask,id))

def c2090 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u2090 : Upper (D 10) (R 10) [34,68,129,160,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,288] 13 (by decide) (choices 1) [8,16,64,256] r2090 c2090
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u793
  · exact u794
  · exact u795
  · exact u796

def b2091 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 336, targets := 128 },{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6),(4,7)], upper := (rows 35 70 133 168 336 312 376 440 312), lower := (rows 35 70 133 168 336 32 64 128 256), losses := [] }

theorem u2091 : Upper (D 10) (R 10) [34,68,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2091 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 304, targets := 64 },{ cop := 3, region := 304, targets := 128 }], pairs := [(4,6),(4,7)], upper := (rows 35 70 133 200 280 304 368 432 304), lower := (rows 35 70 133 200 280 32 64 128 256), losses := [] }

theorem u2092 : Upper (D 10) (R 10) [34,68,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2092 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 304, targets := 64 },{ cop := 3, region := 304, targets := 128 }], pairs := [(4,6),(4,7)], upper := (rows 35 70 133 200 304 312 376 440 312), lower := (rows 35 70 133 200 304 32 64 128 256), losses := [] }

theorem u2093 : Upper (D 10) (R 10) [34,68,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2093 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 35 70 133 280 280 224 224 224 480), lower := (rows 35 70 133 280 280 32 64 128 256), losses := [] }

theorem u2094 : Upper (D 10) (R 10) [34,68,129,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2094 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 280 304 232 232 232 488), lower := (rows 35 70 133 280 304 32 64 128 256), losses := [] }

theorem u2095 : Upper (D 10) (R 10) [34,68,129,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2095 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 280 336 168 232 168 424), lower := (rows 35 70 133 280 336 32 64 128 256), losses := [] }

theorem u2096 : Upper (D 10) (R 10) [34,68,129,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2096 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 70 133 280 400 104 104 232 360), lower := (rows 35 70 133 280 400 32 64 128 256), losses := [] }

theorem u2097 : Upper (D 10) (R 10) [34,68,129,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2097 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 35 70 133 296 304 248 216 216 472), lower := (rows 35 70 133 296 304 32 64 128 256), losses := [] }

theorem u2098 : Upper (D 10) (R 10) [34,68,129,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2098 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2099 : Route 9 := (fun mask => (mask,id))

def c2099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2099 : Upper (D 10) (R 10) [34,68,129,288,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,288,320] 13 (by decide) (choices 1) [8,16,128] r2099 c2099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u797
  · exact u798
  · exact u799

#print axioms u2099
end Delivery.IrregularNine14.P10
