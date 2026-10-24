import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0015
import IrregularNine14P00C0016

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2160 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 69 137 80 170 234 170 426), lower := (rows 305 22 69 137 80 32 64 128 256), losses := [] }

theorem u2160 : Upper (D 0) (R 0) [304,20,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2160
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2161 : Route 9 := (fun mask => (mask,id))

def c2161 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2161 : Upper (D 0) (R 0) [304,20,65,129,128] 13 := by
  apply FastRouting.sound _ _ [304,20,65,129,128] 13 (by decide) (choices 1) [2,8,64] r2161 c2161
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u920
  · exact u921
  · exact u922

def b2162 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 138 17 232 232 232 488), lower := (rows 305 22 69 138 17 32 64 128 256), losses := [] }

theorem u2162 : Upper (D 0) (R 0) [304,20,65,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2162
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 22 69 138 24 225 225 225 481), lower := (rows 305 22 69 138 24 32 64 128 256), losses := [] }

theorem u2163 : Upper (D 0) (R 0) [304,20,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2163
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 138 48 233 201 201 457), lower := (rows 305 22 69 138 48 32 64 128 256), losses := [] }

theorem u2164 : Upper (D 0) (R 0) [304,20,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2164
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 69 138 80 169 233 169 425), lower := (rows 305 22 69 138 80 32 64 128 256), losses := [] }

theorem u2165 : Upper (D 0) (R 0) [304,20,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2165
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2166 : Route 9 := (fun mask => (mask,id))

def c2166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2166 : Upper (D 0) (R 0) [304,20,65,130,128] 13 := by
  apply FastRouting.sound _ _ [304,20,65,130,128] 13 (by decide) (choices 1) [1,8,64] r2166 c2166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u923
  · exact u924
  · exact u925

def b2167 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 168 17 234 202 202 458), lower := (rows 305 22 69 168 17 32 64 128 256), losses := [] }

theorem u2167 : Upper (D 0) (R 0) [304,20,65,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2167
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2168 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 305 22 69 168 18 233 201 201 457), lower := (rows 305 22 69 168 18 32 64 128 256), losses := [] }

theorem u2168 : Upper (D 0) (R 0) [304,20,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2168
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 22 69 168 24 227 195 195 451), lower := (rows 305 22 69 168 24 32 64 128 256), losses := [] }

theorem u2169 : Upper (D 0) (R 0) [304,20,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2169
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 69 168 80 171 203 139 395), lower := (rows 305 22 69 168 80 32 64 128 256), losses := [] }

theorem u2170 : Upper (D 0) (R 0) [304,20,65,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2170
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2171 : Route 9 := (fun mask => (mask,id))

def c2171 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2171 : Upper (D 0) (R 0) [304,20,65,160,128] 13 := by
  apply FastRouting.sound _ _ [304,20,65,160,128] 13 (by decide) (choices 1) [1,2,8,64] r2171 c2171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u926
  · exact u927
  · exact u928
  · exact u929

def b2172 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 200 17 170 234 170 426), lower := (rows 305 22 69 200 17 32 64 128 256), losses := [] }

theorem u2172 : Upper (D 0) (R 0) [304,20,65,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2172
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 305 22 69 200 18 169 233 169 425), lower := (rows 305 22 69 200 18 32 64 128 256), losses := [] }

theorem u2173 : Upper (D 0) (R 0) [304,20,65,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2173
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 22 69 200 24 163 227 163 419), lower := (rows 305 22 69 200 24 32 64 128 256), losses := [] }

theorem u2174 : Upper (D 0) (R 0) [304,20,65,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2174
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 200 48 171 203 139 395), lower := (rows 305 22 69 200 48 32 64 128 256), losses := [] }

theorem u2175 : Upper (D 0) (R 0) [304,20,65,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2175
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2176 : Route 9 := (fun mask => (mask,id))

def c2176 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2176 : Upper (D 0) (R 0) [304,20,65,192,128] 13 := by
  apply FastRouting.sound _ _ [304,20,65,192,128] 13 (by decide) (choices 1) [1,2,8] r2176 c2176
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u930
  · exact u931
  · exact u932

def b2177 : PairBound 9 := { available := 226, camps := [], pairs := [(1,5)], upper := (rows 305 22 76 137 17 226 226 226 482), lower := (rows 305 22 76 137 17 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 25 0 64 128 256), good := (rows 273 22 94 153 17 0 64 128 256) }] }

theorem u2177 : Upper (D 0) (R 0) [304,20,72,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2177
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 305 22 76 137 18 225 225 225 481), lower := (rows 305 22 76 137 18 32 64 128 256), losses := [] }

theorem u2178 : Upper (D 0) (R 0) [304,20,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2178
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 137 48 227 195 195 451), lower := (rows 305 22 76 137 48 32 64 128 256), losses := [] }

theorem u2179 : Upper (D 0) (R 0) [304,20,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2179
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 76 137 80 163 227 163 419), lower := (rows 305 22 76 137 80 32 64 128 256), losses := [] }

theorem u2180 : Upper (D 0) (R 0) [304,20,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2180
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 137 144 99 99 227 355), lower := (rows 305 22 76 137 144 32 64 128 256), losses := [] }

theorem u2181 : Upper (D 0) (R 0) [304,20,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2181
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 225, camps := [], pairs := [(2,4)], upper := (rows 305 22 76 138 17 225 225 225 481), lower := (rows 305 22 76 138 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 6 10 0 49 81 145 273), good := (rows 481 494 76 142 481 32 64 128 256) }] }

theorem u2182 : Upper (D 0) (R 0) [304,20,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2182
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 76 138 48 225 193 193 449), lower := (rows 305 22 76 138 48 32 64 128 256), losses := [] }

theorem u2183 : Upper (D 0) (R 0) [304,20,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2183
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 76 138 80 161 225 161 417), lower := (rows 305 22 76 138 80 32 64 128 256), losses := [] }

theorem u2184 : Upper (D 0) (R 0) [304,20,72,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2184
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 138 144 97 97 225 353), lower := (rows 305 22 76 138 144 32 64 128 256), losses := [] }

theorem u2185 : Upper (D 0) (R 0) [304,20,72,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2185
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2186 : Route 9 := (fun mask => (mask,id))

def c2186 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2186 : Upper (D 0) (R 0) [304,20,72,160,1] 13 := by
  apply FastRouting.sound _ _ [304,20,72,160,1] 13 (by decide) (choices 1) [1,2,64,128] r2186 c2186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u933
  · exact u934
  · exact u935
  · exact u936

def b2187 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 76 168 18 225 193 193 449), lower := (rows 305 22 76 168 18 32 64 128 256), losses := [] }

theorem u2187 : Upper (D 0) (R 0) [304,20,72,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2187
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 76 168 80 163 195 131 387), lower := (rows 305 22 76 168 80 32 64 128 256), losses := [] }

theorem u2188 : Upper (D 0) (R 0) [304,20,72,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2188
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 168 144 99 67 195 323), lower := (rows 305 22 76 168 144 32 64 128 256), losses := [] }

theorem u2189 : Upper (D 0) (R 0) [304,20,72,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2189
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2190 : Route 9 := (fun mask => (mask,id))

def c2190 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2190 : Upper (D 0) (R 0) [304,20,96,65,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65,1] 13 (by decide) (choices 1) [2,8,128] r2190 c2190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u937
  · exact u938
  · exact u939

def b2191 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 100 73 18 169 201 137 393), lower := (rows 305 22 100 73 18 32 64 128 256), losses := [] }

theorem u2191 : Upper (D 0) (R 0) [304,20,96,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2191
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 100 73 24 163 195 131 387), lower := (rows 305 22 100 73 24 32 64 128 256), losses := [] }

theorem u2192 : Upper (D 0) (R 0) [304,20,96,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2192
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2193 : Route 9 := (fun mask => (mask,id))

def c2193 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2193 : Upper (D 0) (R 0) [304,20,96,65,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,65,128] 13 (by decide) (choices 1) [1,2,8,128] r2193 c2193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u940
  · exact u941
  · exact u942
  · exact u943

def r2194 : Route 9 := (fun mask => (mask,id))

def c2194 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2194 : Upper (D 0) (R 0) [304,20,96,129,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,1] 13 (by decide) (choices 1) [2,8,64,128] r2194 c2194
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u944
  · exact u945
  · exact u946
  · exact u947

def b2195 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 305 22 100 137 18 233 201 201 457), lower := (rows 305 22 100 137 18 32 64 128 256), losses := [] }

theorem u2195 : Upper (D 0) (R 0) [304,20,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2195
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 305 22 100 137 24 227 195 195 451), lower := (rows 305 22 100 137 24 32 64 128 256), losses := [] }

theorem u2196 : Upper (D 0) (R 0) [304,20,96,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2196
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 137 80 171 203 139 395), lower := (rows 305 22 100 137 80 32 64 128 256), losses := [] }

theorem u2197 : Upper (D 0) (R 0) [304,20,96,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2197
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2198 : Route 9 := (fun mask => (mask,id))

def c2198 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2198 : Upper (D 0) (R 0) [304,20,96,129,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129,128] 13 (by decide) (choices 1) [1,2,8,64] r2198 c2198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u948
  · exact u949
  · exact u950
  · exact u951

def r2199 : Route 9 := (fun mask => (mask,id))

def c2199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2199 : Upper (D 0) (R 0) [304,20,96,130,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,1] 13 (by decide) (choices 1) [1,8,64,128] r2199 c2199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u952
  · exact u953
  · exact u954
  · exact u955

def b2200 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 305 22 100 138 24 225 193 193 449), lower := (rows 305 22 100 138 24 32 64 128 256), losses := [] }

theorem u2200 : Upper (D 0) (R 0) [304,20,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2200
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 138 80 169 201 137 393), lower := (rows 305 22 100 138 80 32 64 128 256), losses := [] }

theorem u2201 : Upper (D 0) (R 0) [304,20,96,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2201
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2202 : Route 9 := (fun mask => (mask,id))

def c2202 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2202 : Upper (D 0) (R 0) [304,20,96,130,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130,128] 13 (by decide) (choices 1) [1,8,64] r2202 c2202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u956
  · exact u957
  · exact u958

def r2203 : Route 9 := (fun mask => (mask,id))

def c2203 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2203 : Upper (D 0) (R 0) [304,20,96,192,1] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192,1] 13 (by decide) (choices 1) [1,2,8,128] r2203 c2203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u959
  · exact u960
  · exact u961
  · exact u962

def b2204 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 100 200 18 169 201 137 393), lower := (rows 305 22 100 200 18 32 64 128 256), losses := [] }

theorem u2204 : Upper (D 0) (R 0) [304,20,96,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2204
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 100 200 24 163 195 131 387), lower := (rows 305 22 100 200 24 32 64 128 256), losses := [] }

theorem u2205 : Upper (D 0) (R 0) [304,20,96,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2205
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2206 : Route 9 := (fun mask => (mask,id))

def c2206 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2206 : Upper (D 0) (R 0) [304,20,96,192,128] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192,128] 13 (by decide) (choices 1) [1,2,8] r2206 c2206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u963
  · exact u964
  · exact u965

def r2207 : Route 9 := (fun mask => (mask,id))

def c2207 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2207 : Upper (D 0) (R 0) [304,20,192,65,1] 13 := by
  apply FastRouting.sound _ _ [304,20,192,65,1] 13 (by decide) (choices 1) [2,8,128] r2207 c2207
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u966
  · exact u967
  · exact u968

def b2208 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 305 22 196 73 18 169 233 169 425), lower := (rows 305 22 196 73 18 32 64 128 256), losses := [] }

theorem u2208 : Upper (D 0) (R 0) [304,20,192,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2208
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 305 22 196 73 24 163 227 163 419), lower := (rows 305 22 196 73 24 32 64 128 256), losses := [] }

theorem u2209 : Upper (D 0) (R 0) [304,20,192,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2209
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 73 48 171 203 139 395), lower := (rows 305 22 196 73 48 32 64 128 256), losses := [] }

theorem u2210 : Upper (D 0) (R 0) [304,20,192,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2210
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 196 73 144 43 107 171 299), lower := (rows 305 22 196 73 144 32 64 128 256), losses := [] }

theorem u2211 : Upper (D 0) (R 0) [304,20,192,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2211
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2212 : Route 9 := (fun mask => (mask,id))

def c2212 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2212 : Upper (D 0) (R 0) [304,20,192,96,1] 13 := by
  apply FastRouting.sound _ _ [304,20,192,96,1] 13 (by decide) (choices 1) [1,2,8,128] r2212 c2212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u969
  · exact u970
  · exact u971
  · exact u972

def b2213 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 305 22 196 104 18 169 201 137 393), lower := (rows 305 22 196 104 18 32 64 128 256), losses := [] }

theorem u2213 : Upper (D 0) (R 0) [304,20,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2213
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2214 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 305 22 196 104 24 163 195 131 387), lower := (rows 305 22 196 104 24 32 64 128 256), losses := [] }

theorem u2214 : Upper (D 0) (R 0) [304,20,192,96,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2214
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2215 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 18, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 196 104 144 43 75 139 267), lower := (rows 305 22 196 104 144 32 64 128 256), losses := [] }

theorem u2215 : Upper (D 0) (R 0) [304,20,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2215
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2216 : PairBound 9 := { available := 180, camps := [], pairs := [], upper := (rows 305 67 76 137 18 180 244 180 436), lower := (rows 305 67 76 137 18 32 64 128 256), losses := [] }

theorem u2216 : Upper (D 0) (R 0) [304,65,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2216
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2217 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 305 67 76 137 20 178 242 178 434), lower := (rows 305 67 76 137 20 32 64 128 256), losses := [] }

theorem u2217 : Upper (D 0) (R 0) [304,65,72,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2217
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 206, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 137 48 182 214 150 406), lower := (rows 305 67 76 137 48 32 64 128 256), losses := [] }

theorem u2218 : Upper (D 0) (R 0) [304,65,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2218
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m2219_2 : Upper (D 0) (R 0) [304,65,72,129,128,2] 13 :=
  permutation_upper _ _ _ [304,65,72,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u973

theorem m2219_4 : Upper (D 0) (R 0) [304,65,72,129,128,4] 13 :=
  permutation_upper _ _ _ [304,65,72,129,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u974

theorem m2219_16 : Upper (D 0) (R 0) [304,65,72,129,128,16] 13 :=
  permutation_upper _ _ _ [304,65,72,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u975

def r2219 : Route 9 := (fun mask => (mask,id))

def c2219 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2219 : Upper (D 0) (R 0) [304,65,72,129,128] 13 := by
  apply FastRouting.sound _ _ [304,65,72,129,128] 13 (by decide) (choices 1) [2,4,16] r2219 c2219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2219_2
  · exact m2219_4
  · exact m2219_16

#print axioms u2219
end Delivery.IrregularNine14.P00
