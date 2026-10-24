import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0005

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2040 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 88 176 160 73 137 265), lower := (rows 259 38 69 88 176 160 64 128 256), losses := [] }

theorem u2040 : Upper (D 3) (R 3) [258,36,65,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2040
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2041 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 259 38 69 104 145 33 216 152 408), lower := (rows 259 38 69 104 145 33 64 128 256), losses := [] }

theorem u2041 : Upper (D 3) (R 3) [258,36,65,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2041
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2042 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 259 38 69 104 145 40 209 145 401), lower := (rows 259 38 69 104 145 40 64 128 256), losses := [] }

theorem u2042 : Upper (D 3) (R 3) [258,36,65,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2042
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2043 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 259 38 69 104 145 48 201 137 393), lower := (rows 259 38 69 104 145 48 64 128 256), losses := [] }

theorem u2043 : Upper (D 3) (R 3) [258,36,65,96,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2043
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2044 : Route 9 := (fun mask => (mask,id))

def c2044 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2044 : Upper (D 3) (R 3) [258,36,65,96,129,128] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,129,128] 13 (by decide) (choices 1) [1,8,16] r2044 c2044
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u334
  · exact u335
  · exact u336

def b2045 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 34, targets := 128 }], pairs := [(1,7)], upper := (rows 259 38 69 104 152 33 209 145 401), lower := (rows 259 38 69 104 152 33 64 128 256), losses := [] }

theorem u2045 : Upper (D 3) (R 3) [258,36,65,96,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2046 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 69 104 152 48 193 129 385), lower := (rows 259 38 69 104 152 48 64 128 256), losses := [] }

theorem u2046 : Upper (D 3) (R 3) [258,36,65,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2047 : Route 9 := (fun mask => (mask,id))

def c2047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2047 : Upper (D 3) (R 3) [258,36,65,96,136,128] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,136,128] 13 (by decide) (choices 1) [1,16] r2047 c2047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u337
  · exact u338

def b2048 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 137 176 33 88 216 344), lower := (rows 259 38 69 137 176 33 64 128 256), losses := [] }

theorem u2048 : Upper (D 3) (R 3) [258,36,65,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2048
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2049 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 259 38 69 137 176 40 81 209 337), lower := (rows 259 38 69 137 176 40 64 128 256), losses := [] }

theorem u2049 : Upper (D 3) (R 3) [258,36,65,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2049
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2050 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 259 38 69 137 176 48 73 201 329), lower := (rows 259 38 69 137 176 48 64 128 256), losses := [] }

theorem u2050 : Upper (D 3) (R 3) [258,36,65,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2051 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 137 176 96 89 153 281), lower := (rows 259 38 69 137 176 96 64 128 256), losses := [] }

theorem u2051 : Upper (D 3) (R 3) [258,36,65,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2051
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2052 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 137 208 33 120 184 312), lower := (rows 259 38 69 137 208 33 64 128 256), losses := [] }

theorem u2052 : Upper (D 3) (R 3) [258,36,65,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2053 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 259 38 69 137 208 40 113 177 305), lower := (rows 259 38 69 137 208 40 64 128 256), losses := [] }

theorem u2053 : Upper (D 3) (R 3) [258,36,65,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2054 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 259 38 69 137 208 48 105 169 297), lower := (rows 259 38 69 137 208 48 64 128 256), losses := [] }

theorem u2054 : Upper (D 3) (R 3) [258,36,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2055 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 259 38 69 168 208 33 89 153 281), lower := (rows 259 38 69 168 208 33 64 128 256), losses := [] }

theorem u2055 : Upper (D 3) (R 3) [258,36,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2055
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2056 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 38 69 168 208 40 81 145 273), lower := (rows 259 38 69 168 208 40 64 128 256), losses := [] }

theorem u2056 : Upper (D 3) (R 3) [258,36,65,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2056
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2057 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 38 69 168 208 48 73 137 265), lower := (rows 259 38 69 168 208 48 64 128 256), losses := [] }

theorem u2057 : Upper (D 3) (R 3) [258,36,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2058 : PairBound 9 := { available := 145, camps := [], pairs := [(1,6)], upper := (rows 259 38 76 137 112 33 209 145 401), lower := (rows 259 38 76 137 112 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 41 0 128 256), good := (rows 291 38 46 169 48 33 0 128 256) }] }

theorem u2058 : Upper (D 3) (R 3) [258,36,72,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2058
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2059 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 76 137 112 48 193 129 385), lower := (rows 259 38 76 137 112 48 64 128 256), losses := [] }

theorem u2059 : Upper (D 3) (R 3) [258,36,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2059
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2060 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 137 112 160 81 145 273), lower := (rows 259 38 76 137 112 160 64 128 256), losses := [] }

theorem u2060 : Upper (D 3) (R 3) [258,36,72,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2061 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 76 137 176 33 81 209 337), lower := (rows 259 38 76 137 176 33 64 128 256), losses := [] }

theorem u2061 : Upper (D 3) (R 3) [258,36,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2062 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 259 38 76 137 176 48 65 193 321), lower := (rows 259 38 76 137 176 48 64 128 256), losses := [] }

theorem u2062 : Upper (D 3) (R 3) [258,36,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2062
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2063 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 137 176 96 81 145 273), lower := (rows 259 38 76 137 176 96 64 128 256), losses := [] }

theorem u2063 : Upper (D 3) (R 3) [258,36,72,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2064 : PairBound 9 := { available := 49, camps := [], pairs := [(1,6)], upper := (rows 259 38 76 137 208 33 113 177 305), lower := (rows 259 38 76 137 208 33 64 128 256), losses := [{ target := 6, region := (rows 1 6 4 8 16 41 0 128 256), good := (rows 291 38 46 169 144 33 0 128 256) }] }

theorem u2064 : Upper (D 3) (R 3) [258,36,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2065 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 76 137 208 48 97 161 289), lower := (rows 259 38 76 137 208 48 64 128 256), losses := [] }

theorem u2065 : Upper (D 3) (R 3) [258,36,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2066 : Route 9 := (fun mask => (mask,id))

def c2066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2066 : Upper (D 3) (R 3) [258,36,192,80,160,1] 13 := by
  apply FastRouting.sound _ _ [258,36,192,80,160,1] 13 (by decide) (choices 1) [1,8] r2066 c2066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u339
  · exact u340

def b2067 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 259 38 196 88 176 40 65 129 257), lower := (rows 259 38 196 88 176 40 64 128 256), losses := [] }

theorem u2067 : Upper (D 3) (R 3) [258,36,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2067
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2068 : PairBound 9 := { available := 133, camps := [], pairs := [(2,6)], upper := (rows 259 98 44 88 145 33 197 133 389), lower := (rows 259 98 44 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 49 0 128 256), good := (rows 291 34 44 60 177 33 0 128 256) }] }

theorem u2068 : Upper (D 3) (R 3) [258,96,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2068
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2069 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 98 44 88 145 36 193 129 385), lower := (rows 259 98 44 88 145 36 64 128 256), losses := [] }

theorem u2069 : Upper (D 3) (R 3) [258,96,40,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2070 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 88 145 160 69 133 261), lower := (rows 259 98 44 88 145 160 64 128 256), losses := [] }

theorem u2070 : Upper (D 3) (R 3) [258,96,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2070
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2071 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 36, targets := 64 }], pairs := [(2,6)], upper := (rows 259 98 44 137 208 33 85 149 277), lower := (rows 259 98 44 137 208 33 64 128 256), losses := [] }

theorem u2071 : Upper (D 3) (R 3) [258,96,40,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2071
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2072 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 98 44 137 208 36 81 145 273), lower := (rows 259 98 44 137 208 36 64 128 256), losses := [] }

theorem u2072 : Upper (D 3) (R 3) [258,96,40,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2072
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2073 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 98 44 137 208 48 69 133 261), lower := (rows 259 98 44 137 208 48 64 128 256), losses := [] }

theorem u2073 : Upper (D 3) (R 3) [258,96,40,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2073
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2074 : Route 9 := (fun mask => (mask,id))

def c2074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2074 : Upper (D 3) (R 3) [258,96,40,192,129,1] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192,129,1] 13 (by decide) (choices 1) [1,4,16] r2074 c2074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u341
  · exact u342
  · exact u343

def b2075 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 98 44 200 145 36 81 145 273), lower := (rows 259 98 44 200 145 36 64 128 256), losses := [] }

theorem u2075 : Upper (D 3) (R 3) [258,96,40,192,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2075
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2076 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 98 44 200 145 48 69 133 261), lower := (rows 259 98 44 200 145 48 64 128 256), losses := [] }

theorem u2076 : Upper (D 3) (R 3) [258,96,40,192,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2077 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 145 33 224 224 480), lower := (rows 289 7 14 88 145 33 64 128 256), losses := [] }

theorem u2077 : Upper (D 3) (R 3) [288,5,10,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2078 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 145 96 225 161 417), lower := (rows 289 7 14 88 145 96 64 128 256), losses := [] }

theorem u2078 : Upper (D 3) (R 3) [288,5,10,80,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2079 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 14 88 145 160 97 225 353), lower := (rows 289 7 14 88 145 160 64 128 256), losses := [] }

theorem u2079 : Upper (D 3) (R 3) [288,5,10,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2079
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2080 : PairBound 9 := { available := 193, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 176 33 193 193 449), lower := (rows 289 7 14 88 176 33 64 128 256), losses := [] }

theorem u2080 : Upper (D 3) (R 3) [288,5,10,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2081 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 14 88 176 96 193 129 385), lower := (rows 289 7 14 88 176 96 64 128 256), losses := [] }

theorem u2081 : Upper (D 3) (R 3) [288,5,10,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2081
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2082 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 14 88 176 160 65 193 321), lower := (rows 289 7 14 88 176 160 64 128 256), losses := [] }

theorem u2082 : Upper (D 3) (R 3) [288,5,10,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2082
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2083 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 289 7 28 73 145 34 224 224 480), lower := (rows 289 7 28 73 145 34 64 128 256), losses := [] }

theorem u2083 : Upper (D 3) (R 3) [288,5,24,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2084 : Route 9 := (fun mask => (mask,id))

def c2084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2084 : Upper (D 3) (R 3) [288,5,24,65,129,64] 13 := by
  apply FastRouting.sound _ _ [288,5,24,65,129,64] 13 (by decide) (choices 1) [2,32,128] r2084 c2084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u344
  · exact u345
  · exact u346

def b2085 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 146 33 224 224 480), lower := (rows 289 7 28 73 146 33 64 128 256), losses := [] }

theorem u2085 : Upper (D 3) (R 3) [288,5,24,65,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2085
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2086 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 28 73 146 96 225 161 417), lower := (rows 289 7 28 73 146 96 64 128 256), losses := [] }

theorem u2086 : Upper (D 3) (R 3) [288,5,24,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2086
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2087 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 28 73 146 160 97 225 353), lower := (rows 289 7 28 73 146 160 64 128 256), losses := [] }

theorem u2087 : Upper (D 3) (R 3) [288,5,24,65,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2087
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2088 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 152 33 224 224 480), lower := (rows 289 7 70 25 152 33 64 128 256), losses := [] }

theorem u2088 : Upper (D 3) (R 3) [288,5,66,17,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2088
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2089 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 25 152 96 225 161 417), lower := (rows 289 7 70 25 152 96 64 128 256), losses := [] }

theorem u2089 : Upper (D 3) (R 3) [288,5,66,17,136,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2089
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2090 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 289 7 70 56 145 33 200 200 456), lower := (rows 289 7 70 56 145 33 64 128 256), losses := [] }

theorem u2090 : Upper (D 3) (R 3) [288,5,66,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2090
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2091 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 289 7 70 56 145 40 193 193 449), lower := (rows 289 7 70 56 145 40 64 128 256), losses := [] }

theorem u2091 : Upper (D 3) (R 3) [288,5,66,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2091
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2092 : PairBound 9 := { available := 137, camps := [{ cop := 5, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 56 145 96 201 137 393), lower := (rows 289 7 70 56 145 96 64 128 256), losses := [] }

theorem u2092 : Upper (D 3) (R 3) [288,5,66,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2092
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2093 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 289 7 70 56 145 160 73 201 329), lower := (rows 289 7 70 56 145 160 64 128 256), losses := [] }

theorem u2093 : Upper (D 3) (R 3) [288,5,66,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2093
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2094 : PairBound 9 := { available := 88, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 137 176 33 88 216 344), lower := (rows 289 7 70 137 176 33 64 128 256), losses := [] }

theorem u2094 : Upper (D 3) (R 3) [288,5,66,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2094
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2095 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 7 70 137 176 40 81 209 337), lower := (rows 289 7 70 137 176 40 64 128 256), losses := [] }

theorem u2095 : Upper (D 3) (R 3) [288,5,66,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2096 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 289 7 70 137 176 48 73 201 329), lower := (rows 289 7 70 137 176 48 64 128 256), losses := [] }

theorem u2096 : Upper (D 3) (R 3) [288,5,66,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2096
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2097 : PairBound 9 := { available := 25, camps := [{ cop := 5, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 137 176 96 89 153 281), lower := (rows 289 7 70 137 176 96 64 128 256), losses := [] }

theorem u2097 : Upper (D 3) (R 3) [288,5,66,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2098 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 146 33 224 224 480), lower := (rows 289 7 76 25 146 33 64 128 256), losses := [] }

theorem u2098 : Upper (D 3) (R 3) [288,5,72,17,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2098
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2099 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 385, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 25 146 96 225 161 417), lower := (rows 289 7 76 25 146 96 64 128 256), losses := [] }

theorem u2099 : Upper (D 3) (R 3) [288,5,72,17,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2099
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2099
end Delivery.IrregularNine14.P03
