import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 164 104 280 48 193 129 385), lower := (rows 35 70 164 104 280 48 64 128 256), losses := [] }

theorem u2220 : Upper (D 8) (R 8) [34,68,160,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2220 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2221 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 280 160 81 145 273), lower := (rows 35 70 164 104 280 160 64 128 256), losses := [] }

theorem u2221 : Upper (D 8) (R 8) [34,68,160,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2222 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 164 104 400 33 89 153 281), lower := (rows 35 70 164 104 400 33 64 128 256), losses := [] }

theorem u2222 : Upper (D 8) (R 8) [34,68,160,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 164 104 400 40 81 145 273), lower := (rows 35 70 164 104 400 40 64 128 256), losses := [] }

theorem u2223 : Upper (D 8) (R 8) [34,68,160,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2223 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 164 104 400 48 73 137 265), lower := (rows 35 70 164 104 400 48 64 128 256), losses := [] }

theorem u2224 : Upper (D 8) (R 8) [34,68,160,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2224 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2225 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 273 33 104 232 360), lower := (rows 35 70 164 152 273 33 64 128 256), losses := [] }

theorem u2225 : Upper (D 8) (R 8) [34,68,160,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 164 152 273 40 97 225 353), lower := (rows 35 70 164 152 273 40 64 128 256), losses := [] }

theorem u2226 : Upper (D 8) (R 8) [34,68,160,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2226 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 152 273 96 105 169 297), lower := (rows 35 70 164 152 273 96 64 128 256), losses := [] }

theorem u2227 : Upper (D 8) (R 8) [34,68,160,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 304 33 73 201 329), lower := (rows 35 70 164 152 304 33 64 128 256), losses := [] }

theorem u2228 : Upper (D 8) (R 8) [34,68,160,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 70 164 152 304 40 65 193 321), lower := (rows 35 70 164 152 304 40 64 128 256), losses := [] }

theorem u2229 : Upper (D 8) (R 8) [34,68,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2229 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 152 304 96 73 137 265), lower := (rows 35 70 164 152 304 96 64 128 256), losses := [] }

theorem u2230 : Upper (D 8) (R 8) [34,68,160,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2231 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 152 336 33 105 169 297), lower := (rows 35 70 164 152 336 33 64 128 256), losses := [] }

theorem u2231 : Upper (D 8) (R 8) [34,68,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2232 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 164 152 336 40 97 161 289), lower := (rows 35 70 164 152 336 40 64 128 256), losses := [] }

theorem u2232 : Upper (D 8) (R 8) [34,68,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2232 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2233 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 273 33 120 184 312), lower := (rows 35 70 164 200 273 33 64 128 256), losses := [] }

theorem u2233 : Upper (D 8) (R 8) [34,68,160,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2234 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 164 200 273 40 113 177 305), lower := (rows 35 70 164 200 273 40 64 128 256), losses := [] }

theorem u2234 : Upper (D 8) (R 8) [34,68,160,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2234 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 164 200 273 48 105 169 297), lower := (rows 35 70 164 200 273 48 64 128 256), losses := [] }

theorem u2235 : Upper (D 8) (R 8) [34,68,160,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2235 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 280 33 113 177 305), lower := (rows 35 70 164 200 280 33 64 128 256), losses := [] }

theorem u2236 : Upper (D 8) (R 8) [34,68,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 164 200 280 48 97 161 289), lower := (rows 35 70 164 200 280 48 64 128 256), losses := [] }

theorem u2237 : Upper (D 8) (R 8) [34,68,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2237 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2238 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 164 200 304 33 89 153 281), lower := (rows 35 70 164 200 304 33 64 128 256), losses := [] }

theorem u2238 : Upper (D 8) (R 8) [34,68,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2239 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 164 200 304 40 81 145 273), lower := (rows 35 70 164 200 304 40 64 128 256), losses := [] }

theorem u2239 : Upper (D 8) (R 8) [34,68,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2239 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 164 200 304 48 73 137 265), lower := (rows 35 70 164 200 304 48 64 128 256), losses := [] }

theorem u2240 : Upper (D 8) (R 8) [34,68,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2240 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 152 33 224 224 480), lower := (rows 35 70 261 56 152 33 64 128 256), losses := [] }

theorem u2241 : Upper (D 8) (R 8) [34,68,257,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 56 152 96 225 161 417), lower := (rows 35 70 261 56 152 96 64 128 256), losses := [] }

theorem u2242 : Upper (D 8) (R 8) [34,68,257,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 152 160 97 225 353), lower := (rows 35 70 261 56 152 160 64 128 256), losses := [] }

theorem u2243 : Upper (D 8) (R 8) [34,68,257,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 56 208 33 232 168 424), lower := (rows 35 70 261 56 208 33 64 128 256), losses := [] }

theorem u2244 : Upper (D 8) (R 8) [34,68,257,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 261 56 208 40 225 161 417), lower := (rows 35 70 261 56 208 40 64 128 256), losses := [] }

theorem u2245 : Upper (D 8) (R 8) [34,68,257,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2245 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 56 208 160 105 169 297), lower := (rows 35 70 261 56 208 160 64 128 256), losses := [] }

theorem u2246 : Upper (D 8) (R 8) [34,68,257,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 88 176 33 232 168 424), lower := (rows 35 70 261 88 176 33 64 128 256), losses := [] }

theorem u2247 : Upper (D 8) (R 8) [34,68,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 261 88 176 40 225 161 417), lower := (rows 35 70 261 88 176 40 64 128 256), losses := [] }

theorem u2248 : Upper (D 8) (R 8) [34,68,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2248 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 88 176 160 105 169 297), lower := (rows 35 70 261 88 176 160 64 128 256), losses := [] }

theorem u2249 : Upper (D 8) (R 8) [34,68,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 104 152 33 240 176 432), lower := (rows 35 70 261 104 152 33 64 128 256), losses := [] }

theorem u2250 : Upper (D 8) (R 8) [34,68,257,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 261 104 152 48 225 161 417), lower := (rows 35 70 261 104 152 48 64 128 256), losses := [] }

theorem u2251 : Upper (D 8) (R 8) [34,68,257,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2251 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2252 : Route 9 := (fun mask => (mask,id))

def c2252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2252 : Upper (D 8) (R 8) [34,68,257,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,257,96,136,128] 13 (by decide) (choices 1) [1,16,32] r2252 c2252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u287
  · exact u288
  · exact u289

def b2253 : PairBound 9 := { available := 152, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 104 176 33 216 152 408), lower := (rows 35 70 261 104 176 33 64 128 256), losses := [] }

theorem u2253 : Upper (D 8) (R 8) [34,68,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 261 104 176 40 209 145 401), lower := (rows 35 70 261 104 176 40 64 128 256), losses := [] }

theorem u2254 : Upper (D 8) (R 8) [34,68,257,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2254 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 261 104 176 48 201 137 393), lower := (rows 35 70 261 104 176 48 64 128 256), losses := [] }

theorem u2255 : Upper (D 8) (R 8) [34,68,257,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2255 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 261 104 176 160 89 153 281), lower := (rows 35 70 261 104 176 160 64 128 256), losses := [] }

theorem u2256 : Upper (D 8) (R 8) [34,68,257,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 261 168 208 33 120 184 312), lower := (rows 35 70 261 168 208 33 64 128 256), losses := [] }

theorem u2257 : Upper (D 8) (R 8) [34,68,257,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 261 168 208 40 113 177 305), lower := (rows 35 70 261 168 208 40 64 128 256), losses := [] }

theorem u2258 : Upper (D 8) (R 8) [34,68,257,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2258 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2259 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 261 168 208 48 105 169 297), lower := (rows 35 70 261 168 208 48 64 128 256), losses := [] }

theorem u2259 : Upper (D 8) (R 8) [34,68,257,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2259 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2260 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 25 176 33 224 224 480), lower := (rows 35 70 268 25 176 33 64 128 256), losses := [] }

theorem u2260 : Upper (D 8) (R 8) [34,68,264,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2260 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 25 176 96 225 161 417), lower := (rows 35 70 268 25 176 96 64 128 256), losses := [] }

theorem u2261 : Upper (D 8) (R 8) [34,68,264,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2261 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 25 176 160 97 225 353), lower := (rows 35 70 268 25 176 160 64 128 256), losses := [] }

theorem u2262 : Upper (D 8) (R 8) [34,68,264,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2262 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 56 145 33 224 224 480), lower := (rows 35 70 268 56 145 33 64 128 256), losses := [] }

theorem u2263 : Upper (D 8) (R 8) [34,68,264,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2263 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 56 145 96 225 161 417), lower := (rows 35 70 268 56 145 96 64 128 256), losses := [] }

theorem u2264 : Upper (D 8) (R 8) [34,68,264,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2264 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 56 145 160 97 225 353), lower := (rows 35 70 268 56 145 160 64 128 256), losses := [] }

theorem u2265 : Upper (D 8) (R 8) [34,68,264,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2265 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 137 112 33 240 176 432), lower := (rows 35 70 268 137 112 33 64 128 256), losses := [] }

theorem u2266 : Upper (D 8) (R 8) [34,68,264,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2266 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 268 137 112 48 225 161 417), lower := (rows 35 70 268 137 112 48 64 128 256), losses := [] }

theorem u2267 : Upper (D 8) (R 8) [34,68,264,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2267 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 70 268 137 112 160 113 177 305), lower := (rows 35 70 268 137 112 160 64 128 256), losses := [] }

theorem u2268 : Upper (D 8) (R 8) [34,68,264,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2268 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 137 176 33 112 240 368), lower := (rows 35 70 268 137 176 33 64 128 256), losses := [] }

theorem u2269 : Upper (D 8) (R 8) [34,68,264,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2269 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2270 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 268 137 176 48 97 225 353), lower := (rows 35 70 268 137 176 48 64 128 256), losses := [] }

theorem u2270 : Upper (D 8) (R 8) [34,68,264,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2270 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2271 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 137 176 96 113 177 305), lower := (rows 35 70 268 137 176 96 64 128 256), losses := [] }

theorem u2271 : Upper (D 8) (R 8) [34,68,264,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2271 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 137 208 33 112 176 304), lower := (rows 35 70 268 137 208 33 64 128 256), losses := [] }

theorem u2272 : Upper (D 8) (R 8) [34,68,264,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2272 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 268 137 208 48 97 161 289), lower := (rows 35 70 268 137 208 48 64 128 256), losses := [] }

theorem u2273 : Upper (D 8) (R 8) [34,68,264,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2273 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 168 112 33 209 145 401), lower := (rows 35 70 268 168 112 33 64 128 256), losses := [] }

theorem u2274 : Upper (D 8) (R 8) [34,68,264,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2274 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 268 168 112 48 193 129 385), lower := (rows 35 70 268 168 112 48 64 128 256), losses := [] }

theorem u2275 : Upper (D 8) (R 8) [34,68,264,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2275 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2276 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 268 168 112 160 81 145 273), lower := (rows 35 70 268 168 112 160 64 128 256), losses := [] }

theorem u2276 : Upper (D 8) (R 8) [34,68,264,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2276 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 168 145 33 112 240 368), lower := (rows 35 70 268 168 145 33 64 128 256), losses := [] }

theorem u2277 : Upper (D 8) (R 8) [34,68,264,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2277 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 268 168 145 48 97 225 353), lower := (rows 35 70 268 168 145 48 64 128 256), losses := [] }

theorem u2278 : Upper (D 8) (R 8) [34,68,264,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2278 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 268 168 145 96 113 177 305), lower := (rows 35 70 268 168 145 96 64 128 256), losses := [] }

theorem u2279 : Upper (D 8) (R 8) [34,68,264,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2279 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P08
