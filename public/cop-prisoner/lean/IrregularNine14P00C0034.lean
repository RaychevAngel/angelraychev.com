import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0013
import IrregularNine14P00C0014

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2040 : Route 9 := (fun mask => (mask,id))

def c2040 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2040 : Upper (D 0) (R 0) [274,96,40,80,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80,1] 13 (by decide) (choices 1) [1,4,128] r2040 c2040
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u809
  · exact u810
  · exact u811

def b2041 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 88 20 161 193 129 385), lower := (rows 275 98 44 88 20 32 64 128 256), losses := [] }

theorem u2041 : Upper (D 0) (R 0) [274,96,40,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2041
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2042 : Route 9 := (fun mask => (mask,id))

def c2042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2042 : Upper (D 0) (R 0) [274,96,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80,128] 13 (by decide) (choices 1) [1,4,128] r2042 c2042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u812
  · exact u813
  · exact u814

def r2043 : Route 9 := (fun mask => (mask,id))

def c2043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2043 : Upper (D 0) (R 0) [274,96,40,129,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,129,1] 13 (by decide) (choices 1) [4,16,64,128] r2043 c2043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u815
  · exact u816
  · exact u817
  · exact u818

def b2044 : PairBound 9 := { available := 209, camps := [], pairs := [], upper := (rows 275 98 44 137 20 241 209 209 465), lower := (rows 275 98 44 137 20 32 64 128 256), losses := [] }

theorem u2044 : Upper (D 0) (R 0) [274,96,40,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2044
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2045 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 44 137 80 181 213 149 405), lower := (rows 275 98 44 137 80 32 64 128 256), losses := [] }

theorem u2045 : Upper (D 0) (R 0) [274,96,40,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2045
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2046 : Route 9 := (fun mask => (mask,id))

def c2046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2046 : Upper (D 0) (R 0) [274,96,40,129,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,129,128] 13 (by decide) (choices 1) [1,4,16,64] r2046 c2046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u819
  · exact u820
  · exact u821
  · exact u822

def r2047 : Route 9 := (fun mask => (mask,id))

def c2047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2047 : Upper (D 0) (R 0) [274,96,40,144,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,144,1] 13 (by decide) (choices 1) [1,4,64,128] r2047 c2047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u823
  · exact u824
  · exact u825
  · exact u826

def b2048 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 44 152 20 225 193 193 449), lower := (rows 275 98 44 152 20 32 64 128 256), losses := [] }

theorem u2048 : Upper (D 0) (R 0) [274,96,40,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2048
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 44 152 80 165 197 133 389), lower := (rows 275 98 44 152 80 32 64 128 256), losses := [] }

theorem u2049 : Upper (D 0) (R 0) [274,96,40,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2049
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 152 144 101 69 197 325), lower := (rows 275 98 44 152 144 32 64 128 256), losses := [] }

theorem u2050 : Upper (D 0) (R 0) [274,96,40,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2050
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2051 : Route 9 := (fun mask => (mask,id))

def c2051 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2051 : Upper (D 0) (R 0) [274,96,40,192,1] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192,1] 13 (by decide) (choices 1) [1,4,16,128] r2051 c2051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u827
  · exact u828
  · exact u829
  · exact u830

def b2052 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 275 98 44 200 20 177 209 145 401), lower := (rows 275 98 44 200 20 32 64 128 256), losses := [] }

theorem u2052 : Upper (D 0) (R 0) [274,96,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2052
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2053 : Route 9 := (fun mask => (mask,id))

def c2053 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2053 : Upper (D 0) (R 0) [274,96,40,192,128] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192,128] 13 (by decide) (choices 1) [1,4,16] r2053 c2053
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u831
  · exact u832
  · exact u833

def r2054 : Route 9 := (fun mask => (mask,id))

def c2054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2054 : Upper (D 0) (R 0) [274,96,48,129,1] 13 := by
  apply FastRouting.sound _ _ [274,96,48,129,1] 13 (by decide) (choices 1) [4,8,64,128] r2054 c2054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u834
  · exact u835
  · exact u836
  · exact u837

def b2055 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 275 98 52 137 20 233 201 201 457), lower := (rows 275 98 52 137 20 32 64 128 256), losses := [] }

theorem u2055 : Upper (D 0) (R 0) [274,96,48,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2055
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 275 98 52 137 24 229 197 197 453), lower := (rows 275 98 52 137 24 32 64 128 256), losses := [] }

theorem u2056 : Upper (D 0) (R 0) [274,96,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2056
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 137 80 173 205 141 397), lower := (rows 275 98 52 137 80 32 64 128 256), losses := [] }

theorem u2057 : Upper (D 0) (R 0) [274,96,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2057
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2058 : Route 9 := (fun mask => (mask,id))

def c2058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2058 : Upper (D 0) (R 0) [274,96,48,129,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,129,128] 13 (by decide) (choices 1) [1,4,8,64] r2058 c2058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u838
  · exact u839
  · exact u840
  · exact u841

def r2059 : Route 9 := (fun mask => (mask,id))

def c2059 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2059 : Upper (D 0) (R 0) [274,96,48,132,1] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132,1] 13 (by decide) (choices 1) [1,8,64,128] r2059 c2059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u842
  · exact u843
  · exact u844
  · exact u845

def b2060 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 275 98 52 140 24 225 193 193 449), lower := (rows 275 98 52 140 24 32 64 128 256), losses := [] }

theorem u2060 : Upper (D 0) (R 0) [274,96,48,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2060
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 52 140 80 169 201 137 393), lower := (rows 275 98 52 140 80 32 64 128 256), losses := [] }

theorem u2061 : Upper (D 0) (R 0) [274,96,48,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2061
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2062 : Route 9 := (fun mask => (mask,id))

def c2062 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2062 : Upper (D 0) (R 0) [274,96,48,132,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132,128] 13 (by decide) (choices 1) [1,8,64] r2062 c2062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u846
  · exact u847
  · exact u848

def r2063 : Route 9 := (fun mask => (mask,id))

def c2063 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2063 : Upper (D 0) (R 0) [274,96,48,192,1] 13 := by
  apply FastRouting.sound _ _ [274,96,48,192,1] 13 (by decide) (choices 1) [1,4,8,128] r2063 c2063
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u849
  · exact u850
  · exact u851
  · exact u852

def b2064 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 275 98 52 200 20 169 201 137 393), lower := (rows 275 98 52 200 20 32 64 128 256), losses := [] }

theorem u2064 : Upper (D 0) (R 0) [274,96,48,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2064
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 275 98 52 200 24 165 197 133 389), lower := (rows 275 98 52 200 24 32 64 128 256), losses := [] }

theorem u2065 : Upper (D 0) (R 0) [274,96,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2065
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2066 : Route 9 := (fun mask => (mask,id))

def c2066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2066 : Upper (D 0) (R 0) [274,96,48,192,128] 13 := by
  apply FastRouting.sound _ _ [274,96,48,192,128] 13 (by decide) (choices 1) [1,4,8] r2066 c2066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u853
  · exact u854
  · exact u855

def b2067 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 133 152 17 108 108 236 364), lower := (rows 275 98 133 152 17 32 64 128 256), losses := [] }

theorem u2067 : Upper (D 0) (R 0) [274,96,129,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2067
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 275 98 133 152 20 105 105 233 361), lower := (rows 275 98 133 152 20 32 64 128 256), losses := [] }

theorem u2068 : Upper (D 0) (R 0) [274,96,129,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2068
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 275 98 133 152 24 101 101 229 357), lower := (rows 275 98 133 152 24 32 64 128 256), losses := [] }

theorem u2069 : Upper (D 0) (R 0) [274,96,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2069
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 133 152 48 109 77 205 333), lower := (rows 275 98 133 152 48 32 64 128 256), losses := [] }

theorem u2070 : Upper (D 0) (R 0) [274,96,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2070
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2071 : Route 9 := (fun mask => (mask,id))

def c2071 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2071 : Upper (D 0) (R 0) [274,96,129,160,1] 13 := by
  apply FastRouting.sound _ _ [274,96,129,160,1] 13 (by decide) (choices 1) [4,8,16,64] r2071 c2071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u856
  · exact u857
  · exact u858
  · exact u859

def b2072 : PairBound 9 := { available := 89, camps := [], pairs := [], upper := (rows 275 98 133 168 20 121 89 217 345), lower := (rows 275 98 133 168 20 32 64 128 256), losses := [] }

theorem u2072 : Upper (D 0) (R 0) [274,96,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2072
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 85, camps := [], pairs := [], upper := (rows 275 98 133 168 24 117 85 213 341), lower := (rows 275 98 133 168 24 32 64 128 256), losses := [] }

theorem u2073 : Upper (D 0) (R 0) [274,96,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2073
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2074 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 133 168 80 61 93 157 285), lower := (rows 275 98 133 168 80 32 64 128 256), losses := [] }

theorem u2074 : Upper (D 0) (R 0) [274,96,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2074
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2075 : Route 9 := (fun mask => (mask,id))

def c2075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2075 : Upper (D 0) (R 0) [274,96,144,160,1] 13 := by
  apply FastRouting.sound _ _ [274,96,144,160,1] 13 (by decide) (choices 1) [1,4,8,64] r2075 c2075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u860
  · exact u861
  · exact u862
  · exact u863

def b2076 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 275 98 148 168 20 105 73 201 329), lower := (rows 275 98 148 168 20 32 64 128 256), losses := [] }

theorem u2076 : Upper (D 0) (R 0) [274,96,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2076
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 275 98 148 168 24 101 69 197 325), lower := (rows 275 98 148 168 24 32 64 128 256), losses := [] }

theorem u2077 : Upper (D 0) (R 0) [274,96,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2077
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 172, targets := 64 }], pairs := [(2,6)], upper := (rows 275 98 148 168 80 45 77 141 269), lower := (rows 275 98 148 168 80 32 64 128 256), losses := [] }

theorem u2078 : Upper (D 0) (R 0) [274,96,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2078
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2079 : Route 9 := (fun mask => (mask,id))

def c2079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2079 : Upper (D 0) (R 0) [274,96,160,192,1] 13 := by
  apply FastRouting.sound _ _ [274,96,160,192,1] 13 (by decide) (choices 1) [1,4,8,16] r2079 c2079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u864
  · exact u865
  · exact u866
  · exact u867

def b2080 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 275 98 164 200 20 57 89 153 281), lower := (rows 275 98 164 200 20 32 64 128 256), losses := [] }

theorem u2080 : Upper (D 0) (R 0) [274,96,160,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2080
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 14 88 17 224 224 224 480), lower := (rows 305 7 14 88 17 32 64 128 256), losses := [] }

theorem u2081 : Upper (D 0) (R 0) [304,5,10,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2081
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 88 48 225 193 193 449), lower := (rows 305 7 14 88 48 32 64 128 256), losses := [] }

theorem u2082 : Upper (D 0) (R 0) [304,5,10,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2082
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 14 88 80 161 225 161 417), lower := (rows 305 7 14 88 80 32 64 128 256), losses := [] }

theorem u2083 : Upper (D 0) (R 0) [304,5,10,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2083
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2084 : Route 9 := (fun mask => (mask,id))

def c2084 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2084 : Upper (D 0) (R 0) [304,5,10,80,128] 13 := by
  apply FastRouting.sound _ _ [304,5,10,80,128] 13 (by decide) (choices 1) [1,64,128] r2084 c2084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u868
  · exact u869
  · exact u870

def b2085 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 14 200 17 240 240 240 496), lower := (rows 305 7 14 200 17 32 64 128 256), losses := [] }

theorem u2085 : Upper (D 0) (R 0) [304,5,10,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2085
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 200 48 241 209 209 465), lower := (rows 305 7 14 200 48 32 64 128 256), losses := [] }

theorem u2086 : Upper (D 0) (R 0) [304,5,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2086
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 14 200 80 177 241 177 433), lower := (rows 305 7 14 200 80 32 64 128 256), losses := [] }

theorem u2087 : Upper (D 0) (R 0) [304,5,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2087
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 305 7 70 137 24 240 240 240 496), lower := (rows 305 7 70 137 24 32 64 128 256), losses := [] }

theorem u2088 : Upper (D 0) (R 0) [304,5,66,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2088
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 137 48 248 216 216 472), lower := (rows 305 7 70 137 48 32 64 128 256), losses := [] }

theorem u2089 : Upper (D 0) (R 0) [304,5,66,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2089
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 70 137 80 184 248 184 440), lower := (rows 305 7 70 137 80 32 64 128 256), losses := [] }

theorem u2090 : Upper (D 0) (R 0) [304,5,66,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2090
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2091_8 : Upper (D 0) (R 0) [304,5,66,129,128,8] 13 :=
  permutation_upper _ _ _ [304,5,66,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u871

theorem m2091_16 : Upper (D 0) (R 0) [304,5,66,129,128,16] 13 :=
  permutation_upper _ _ _ [304,5,66,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u872

theorem m2091_64 : Upper (D 0) (R 0) [304,5,66,129,128,64] 13 :=
  permutation_upper _ _ _ [304,5,66,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u873

def r2091 : Route 9 := (fun mask => (mask,id))

def c2091 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2091 : Upper (D 0) (R 0) [304,5,66,129,128] 13 := by
  apply FastRouting.sound _ _ [304,5,66,129,128] 13 (by decide) (choices 1) [8,16,64] r2091 c2091
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2091_8
  · exact m2091_16
  · exact m2091_64

def b2092 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 70 152 17 232 232 232 488), lower := (rows 305 7 70 152 17 32 64 128 256), losses := [] }

theorem u2092 : Upper (D 0) (R 0) [304,5,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2092
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 7 70 152 24 225 225 225 481), lower := (rows 305 7 70 152 24 32 64 128 256), losses := [] }

theorem u2093 : Upper (D 0) (R 0) [304,5,66,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2093
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 70 152 48 233 201 201 457), lower := (rows 305 7 70 152 48 32 64 128 256), losses := [] }

theorem u2094 : Upper (D 0) (R 0) [304,5,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2094
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 70 152 80 169 233 169 425), lower := (rows 305 7 70 152 80 32 64 128 256), losses := [] }

theorem u2095 : Upper (D 0) (R 0) [304,5,66,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2095
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 70 152 144 105 105 233 361), lower := (rows 305 7 70 152 144 32 64 128 256), losses := [] }

theorem u2096 : Upper (D 0) (R 0) [304,5,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2096
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 305 7 76 137 18 240 240 240 496), lower := (rows 305 7 76 137 18 32 64 128 256), losses := [] }

theorem u2097 : Upper (D 0) (R 0) [304,5,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2097
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 137 48 242 210 210 466), lower := (rows 305 7 76 137 48 32 64 128 256), losses := [] }

theorem u2098 : Upper (D 0) (R 0) [304,5,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2098
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2099_2 : Upper (D 0) (R 0) [304,5,72,129,64,2] 13 :=
  permutation_upper _ _ _ [304,5,72,129,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u874

theorem m2099_16 : Upper (D 0) (R 0) [304,5,72,129,64,16] 13 :=
  permutation_upper _ _ _ [304,5,72,129,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u876

def r2099 : Route 9 := (fun mask => (mask,id))

def c2099 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2099 : Upper (D 0) (R 0) [304,5,72,129,64] 13 := by
  apply FastRouting.sound _ _ [304,5,72,129,64] 13 (by decide) (choices 1) [2,16,128] r2099 c2099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2099_2
  · exact m2099_16
  · exact u878

#print axioms u2099
end Delivery.IrregularNine14.P00
