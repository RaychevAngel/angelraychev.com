import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0006

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2160 : Route 9 := (fun mask => (mask,id))

def c2160 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2160 : Upper (D 3) (R 3) [288,12,65,160,129,64] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160,129,64] 13 (by decide) (choices 1) [1,2,16] r2160 c2160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u362
  · exact u363
  · exact u364

def b2161 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 168 208 33 83 147 275), lower := (rows 289 14 69 168 208 33 64 128 256), losses := [] }

theorem u2161 : Upper (D 3) (R 3) [288,12,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2161
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2162 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 14 69 168 208 34 81 145 273), lower := (rows 289 14 69 168 208 34 64 128 256), losses := [] }

theorem u2162 : Upper (D 3) (R 3) [288,12,65,160,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2163 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 14 69 168 208 48 67 131 259), lower := (rows 289 14 69 168 208 48 64 128 256), losses := [] }

theorem u2163 : Upper (D 3) (R 3) [288,12,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2164 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 289 38 69 88 145 33 202 138 394), lower := (rows 289 38 69 88 145 33 64 128 256), losses := [] }

theorem u2164 : Upper (D 3) (R 3) [288,36,65,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2165 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 289 38 69 88 145 34 201 137 393), lower := (rows 289 38 69 88 145 34 64 128 256), losses := [] }

theorem u2165 : Upper (D 3) (R 3) [288,36,65,80,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2166 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 69 88 145 40 195 131 387), lower := (rows 289 38 69 88 145 40 64 128 256), losses := [] }

theorem u2166 : Upper (D 3) (R 3) [288,36,65,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2167 : Route 9 := (fun mask => (mask,id))

def c2167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2167 : Upper (D 3) (R 3) [288,36,65,80,129,128] 13 := by
  apply FastRouting.sound _ _ [288,36,65,80,129,128] 13 (by decide) (choices 1) [1,2,8] r2167 c2167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u365
  · exact u366
  · exact u367

def b2168 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 289 38 69 137 146 33 88 216 344), lower := (rows 289 38 69 137 146 33 64 128 256), losses := [] }

theorem u2168 : Upper (D 3) (R 3) [288,36,65,129,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2168
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2169 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 289 38 69 137 146 40 81 209 337), lower := (rows 289 38 69 137 146 40 64 128 256), losses := [] }

theorem u2169 : Upper (D 3) (R 3) [288,36,65,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2169
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2170 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 289 38 69 137 146 48 73 201 329), lower := (rows 289 38 69 137 146 48 64 128 256), losses := [] }

theorem u2170 : Upper (D 3) (R 3) [288,36,65,129,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2170
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2171 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 409, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 69 137 146 96 89 153 281), lower := (rows 289 38 69 137 146 96 64 128 256), losses := [] }

theorem u2171 : Upper (D 3) (R 3) [288,36,65,129,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2171
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2172 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 289 38 69 137 208 33 90 154 282), lower := (rows 289 38 69 137 208 33 64 128 256), losses := [] }

theorem u2172 : Upper (D 3) (R 3) [288,36,65,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2172
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2173 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 38 69 137 208 34 89 153 281), lower := (rows 289 38 69 137 208 34 64 128 256), losses := [] }

theorem u2173 : Upper (D 3) (R 3) [288,36,65,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2174 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 38 69 137 208 40 83 147 275), lower := (rows 289 38 69 137 208 40 64 128 256), losses := [] }

theorem u2174 : Upper (D 3) (R 3) [288,36,65,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2175 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 289 38 69 137 208 48 75 139 267), lower := (rows 289 38 69 137 208 48 64 128 256), losses := [] }

theorem u2175 : Upper (D 3) (R 3) [288,36,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2175
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2176 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 289 38 69 138 208 33 89 153 281), lower := (rows 289 38 69 138 208 33 64 128 256), losses := [] }

theorem u2176 : Upper (D 3) (R 3) [288,36,65,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2177 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 69 138 208 40 81 145 273), lower := (rows 289 38 69 138 208 40 64 128 256), losses := [] }

theorem u2177 : Upper (D 3) (R 3) [288,36,65,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2177
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2178 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 38 69 138 208 48 73 137 265), lower := (rows 289 38 69 138 208 48 64 128 256), losses := [] }

theorem u2178 : Upper (D 3) (R 3) [288,36,65,130,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2178
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2179 : PairBound 9 := { available := 146, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 81 33 210 146 402), lower := (rows 289 38 76 137 81 33 64 128 256), losses := [] }

theorem u2179 : Upper (D 3) (R 3) [288,36,72,129,65,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2179
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2180 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 289 38 76 137 81 34 209 145 401), lower := (rows 289 38 76 137 81 34 64 128 256), losses := [] }

theorem u2180 : Upper (D 3) (R 3) [288,36,72,129,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2181 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 289 38 76 137 81 48 195 131 387), lower := (rows 289 38 76 137 81 48 64 128 256), losses := [] }

theorem u2181 : Upper (D 3) (R 3) [288,36,72,129,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2182 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 289 38 76 137 81 160 83 147 275), lower := (rows 289 38 76 137 81 160 64 128 256), losses := [] }

theorem u2182 : Upper (D 3) (R 3) [288,36,72,129,65,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2182
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2183 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 76 137 208 33 83 147 275), lower := (rows 289 38 76 137 208 33 64 128 256), losses := [] }

theorem u2183 : Upper (D 3) (R 3) [288,36,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2183
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2184 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 76 137 208 34 81 145 273), lower := (rows 289 38 76 137 208 34 64 128 256), losses := [] }

theorem u2184 : Upper (D 3) (R 3) [288,36,72,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2185 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 76 137 208 48 67 131 259), lower := (rows 289 38 76 137 208 48 64 128 256), losses := [] }

theorem u2185 : Upper (D 3) (R 3) [288,36,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2185
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2186 : PairBound 9 := { available := 26, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 73 145 33 90 154 282), lower := (rows 289 38 196 73 145 33 64 128 256), losses := [] }

theorem u2186 : Upper (D 3) (R 3) [288,36,192,65,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2187 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 289 38 196 73 145 34 89 153 281), lower := (rows 289 38 196 73 145 34 64 128 256), losses := [] }

theorem u2187 : Upper (D 3) (R 3) [288,36,192,65,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2187
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2188 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 38 196 73 145 40 83 147 275), lower := (rows 289 38 196 73 145 40 64 128 256), losses := [] }

theorem u2188 : Upper (D 3) (R 3) [288,36,192,65,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2188
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2189 : PairBound 9 := { available := 19, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 38 196 73 152 33 83 147 275), lower := (rows 289 38 196 73 152 33 64 128 256), losses := [] }

theorem u2189 : Upper (D 3) (R 3) [288,36,192,65,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2190 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 38 196 73 152 34 81 145 273), lower := (rows 289 38 196 73 152 34 64 128 256), losses := [] }

theorem u2190 : Upper (D 3) (R 3) [288,36,192,65,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2190
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2191 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 289 38 196 73 152 48 67 131 259), lower := (rows 289 38 196 73 152 48 64 128 256), losses := [] }

theorem u2191 : Upper (D 3) (R 3) [288,36,192,65,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2192 : PairBound 9 := { available := 52, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 137 146 33 116 180 308), lower := (rows 289 67 76 137 146 33 64 128 256), losses := [] }

theorem u2192 : Upper (D 3) (R 3) [288,65,72,129,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2193 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 289 67 76 137 146 36 113 177 305), lower := (rows 289 67 76 137 146 36 64 128 256), losses := [] }

theorem u2193 : Upper (D 3) (R 3) [288,65,72,129,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2194 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 137 176 33 86 150 278), lower := (rows 289 67 76 137 176 33 64 128 256), losses := [] }

theorem u2194 : Upper (D 3) (R 3) [288,65,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2194
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2195 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 289 67 76 137 176 34 85 149 277), lower := (rows 289 67 76 137 176 34 64 128 256), losses := [] }

theorem u2195 : Upper (D 3) (R 3) [288,65,72,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2196 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 67 76 137 176 36 83 147 275), lower := (rows 289 67 76 137 176 36 64 128 256), losses := [] }

theorem u2196 : Upper (D 3) (R 3) [288,65,72,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2196
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2197 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 289 67 76 137 176 48 71 135 263), lower := (rows 289 67 76 137 176 48 64 128 256), losses := [] }

theorem u2197 : Upper (D 3) (R 3) [288,65,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2198 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 168 145 33 86 150 278), lower := (rows 289 67 76 168 145 33 64 128 256), losses := [] }

theorem u2198 : Upper (D 3) (R 3) [288,65,72,160,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2198
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2199 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 289 67 76 168 145 34 85 149 277), lower := (rows 289 67 76 168 145 34 64 128 256), losses := [] }

theorem u2199 : Upper (D 3) (R 3) [288,65,72,160,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2199
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2200 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 289 67 76 168 145 36 83 147 275), lower := (rows 289 67 76 168 145 36 64 128 256), losses := [] }

theorem u2200 : Upper (D 3) (R 3) [288,65,72,160,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2200
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2201 : PairBound 9 := { available := 7, camps := [], pairs := [], upper := (rows 289 67 76 168 145 48 71 135 263), lower := (rows 289 67 76 168 145 48 64 128 256), losses := [] }

theorem u2201 : Upper (D 3) (R 3) [288,65,72,160,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2201
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2202 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 76 168 146 33 85 149 277), lower := (rows 289 67 76 168 146 33 64 128 256), losses := [] }

theorem u2202 : Upper (D 3) (R 3) [288,65,72,160,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2202
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2203 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 67 76 168 146 36 81 145 273), lower := (rows 289 67 76 168 146 36 64 128 256), losses := [] }

theorem u2203 : Upper (D 3) (R 3) [288,65,72,160,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2203
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2204 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 289 67 76 168 146 48 69 133 261), lower := (rows 289 67 76 168 146 48 64 128 256), losses := [] }

theorem u2204 : Upper (D 3) (R 3) [288,65,72,160,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2205 : PairBound 9 := { available := 25, camps := [{ cop := 8, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 289 67 100 138 148 33 89 153 281), lower := (rows 289 67 100 138 148 33 64 128 256), losses := [] }

theorem u2205 : Upper (D 3) (R 3) [288,65,96,130,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2206 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 289 67 100 138 148 40 81 145 273), lower := (rows 289 67 100 138 148 40 64 128 256), losses := [] }

theorem u2206 : Upper (D 3) (R 3) [288,65,96,130,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2207 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 289 67 100 138 148 48 73 137 265), lower := (rows 289 67 100 138 148 48 64 128 256), losses := [] }

theorem u2207 : Upper (D 3) (R 3) [288,65,96,130,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2208 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 41 112 480 448 448 448), lower := (rows 7 11 21 41 112 32 64 128 256), losses := [] }

theorem u2208 : Upper (D 3) (R 3) [6,9,17,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2209 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 21 41 208 480 480 480 480), lower := (rows 7 11 21 41 208 32 64 128 256), losses := [] }

theorem u2209 : Upper (D 3) (R 3) [6,9,17,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2210 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6)], upper := (rows 7 11 21 41 304 224 192 192 448), lower := (rows 7 11 21 41 304 32 64 128 256), losses := [] }

theorem u2210 : Upper (D 3) (R 3) [6,9,17,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2211 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 21 41 336 224 224 224 480), lower := (rows 7 11 21 41 336 32 64 128 256), losses := [] }

theorem u2211 : Upper (D 3) (R 3) [6,9,17,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2212 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 23, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 21 104 112 417 449 385 385), lower := (rows 7 11 21 104 112 32 64 128 256), losses := [] }

theorem u2212 : Upper (D 3) (R 3) [6,9,17,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2212
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m2213_128 : Upper (D 3) (R 3) [6,9,17,96,160,128] 13 :=
  permutation_upper _ _ _ [6,9,17,96,160,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u369

def r2213 : Route 9 := (fun mask => (mask,id))

def c2213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2213 : Upper (D 3) (R 3) [6,9,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,160] 13 (by decide) (choices 1) [1,64,128,256] r2213 c2213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u368
  · exact u369
  · exact m2213_128
  · exact u370

def b2214 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 7 11 21 104 273 224 224 224 480), lower := (rows 7 11 21 104 273 32 64 128 256), losses := [] }

theorem u2214 : Upper (D 3) (R 3) [6,9,17,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2215 : Route 9 := (fun mask => (mask,id))

def c2215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2215 : Upper (D 3) (R 3) [6,9,17,96,288] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,288] 13 (by decide) (choices 1) [1,64,128] r2215 c2215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u371
  · exact u372
  · exact u373

def r2216 : Route 9 := (fun mask => (mask,id))

def c2216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2216 : Upper (D 3) (R 3) [6,9,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,17,96,384] 13 (by decide) (choices 1) [1,64,128] r2216 c2216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u374
  · exact u375
  · exact u376

def b2217 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 11 37 88 49 480 448 448 448), lower := (rows 7 11 37 88 49 32 64 128 256), losses := [] }

theorem u2217 : Upper (D 3) (R 3) [6,9,33,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2217
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2218 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 7 11 37 88 81 416 480 416 416), lower := (rows 7 11 37 88 81 32 64 128 256), losses := [] }

theorem u2218 : Upper (D 3) (R 3) [6,9,33,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2219 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 37 88 112 417 449 385 385), lower := (rows 7 11 37 88 112 32 64 128 256), losses := [] }

theorem u2219 : Upper (D 3) (R 3) [6,9,33,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2219
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2219
end Delivery.IrregularNine14.P03
