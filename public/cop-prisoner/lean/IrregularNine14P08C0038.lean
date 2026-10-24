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

def b2280 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 268 168 208 33 113 177 305), lower := (rows 35 70 268 168 208 33 64 128 256), losses := [] }

theorem u2280 : Upper (D 8) (R 8) [34,68,264,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2280 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 268 168 208 48 97 161 289), lower := (rows 35 70 268 168 208 48 64 128 256), losses := [] }

theorem u2281 : Upper (D 8) (R 8) [34,68,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2281 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 454, targets := 1 }], pairs := [(1,0)], upper := (rows 35 70 292 25 152 33 224 224 480), lower := (rows 35 70 292 25 152 33 64 128 256), losses := [] }

theorem u2282 : Upper (D 8) (R 8) [34,68,288,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2282 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 25 152 96 225 161 417), lower := (rows 35 70 292 25 152 96 64 128 256), losses := [] }

theorem u2283 : Upper (D 8) (R 8) [34,68,288,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2283 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 25 152 160 97 225 353), lower := (rows 35 70 292 25 152 160 64 128 256), losses := [] }

theorem u2284 : Upper (D 8) (R 8) [34,68,288,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2284 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 25 176 33 200 200 456), lower := (rows 35 70 292 25 176 33 64 128 256), losses := [] }

theorem u2285 : Upper (D 8) (R 8) [34,68,288,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2285 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 292 25 176 40 193 193 449), lower := (rows 35 70 292 25 176 40 64 128 256), losses := [] }

theorem u2286 : Upper (D 8) (R 8) [34,68,288,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2286 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 25 176 96 201 137 393), lower := (rows 35 70 292 25 176 96 64 128 256), losses := [] }

theorem u2287 : Upper (D 8) (R 8) [34,68,288,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2287 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 25 176 160 73 201 329), lower := (rows 35 70 292 25 176 160 64 128 256), losses := [] }

theorem u2288 : Upper (D 8) (R 8) [34,68,288,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2288 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 56 145 33 200 200 456), lower := (rows 35 70 292 56 145 33 64 128 256), losses := [] }

theorem u2289 : Upper (D 8) (R 8) [34,68,288,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2289 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 70 292 56 145 40 193 193 449), lower := (rows 35 70 292 56 145 40 64 128 256), losses := [] }

theorem u2290 : Upper (D 8) (R 8) [34,68,288,48,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2290 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 56 145 96 201 137 393), lower := (rows 35 70 292 56 145 96 64 128 256), losses := [] }

theorem u2291 : Upper (D 8) (R 8) [34,68,288,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2291 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 56 145 160 73 201 329), lower := (rows 35 70 292 56 145 160 64 128 256), losses := [] }

theorem u2292 : Upper (D 8) (R 8) [34,68,288,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2292 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 56 152 33 193 193 449), lower := (rows 35 70 292 56 152 33 64 128 256), losses := [] }

theorem u2293 : Upper (D 8) (R 8) [34,68,288,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2293 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 56 152 96 193 129 385), lower := (rows 35 70 292 56 152 96 64 128 256), losses := [] }

theorem u2294 : Upper (D 8) (R 8) [34,68,288,48,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2294 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 70 292 56 152 160 65 193 321), lower := (rows 35 70 292 56 152 160 64 128 256), losses := [] }

theorem u2295 : Upper (D 8) (R 8) [34,68,288,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2295 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 56 208 33 201 137 393), lower := (rows 35 70 292 56 208 33 64 128 256), losses := [] }

theorem u2296 : Upper (D 8) (R 8) [34,68,288,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2296 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 292 56 208 40 193 129 385), lower := (rows 35 70 292 56 208 40 64 128 256), losses := [] }

theorem u2297 : Upper (D 8) (R 8) [34,68,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2297 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 56 208 160 73 137 265), lower := (rows 35 70 292 56 208 160 64 128 256), losses := [] }

theorem u2298 : Upper (D 8) (R 8) [34,68,288,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2298 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 88 145 33 232 168 424), lower := (rows 35 70 292 88 145 33 64 128 256), losses := [] }

theorem u2299 : Upper (D 8) (R 8) [34,68,288,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2299 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2300 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 70 292 88 145 40 225 161 417), lower := (rows 35 70 292 88 145 40 64 128 256), losses := [] }

theorem u2300 : Upper (D 8) (R 8) [34,68,288,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2300 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2301 : Route 9 := (fun mask => (mask,id))

def c2301 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2301 : Upper (D 8) (R 8) [34,68,288,80,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,80,129,128] 13 (by decide) (choices 1) [1,8,32] r2301 c2301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u290
  · exact u291
  · exact u292

def b2302 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 88 176 33 201 137 393), lower := (rows 35 70 292 88 176 33 64 128 256), losses := [] }

theorem u2302 : Upper (D 8) (R 8) [34,68,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2302 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 292 88 176 40 193 129 385), lower := (rows 35 70 292 88 176 40 64 128 256), losses := [] }

theorem u2303 : Upper (D 8) (R 8) [34,68,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2303 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 88 176 160 73 137 265), lower := (rows 35 70 292 88 176 160 64 128 256), losses := [] }

theorem u2304 : Upper (D 8) (R 8) [34,68,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2304 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2305 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 104 145 33 216 152 408), lower := (rows 35 70 292 104 145 33 64 128 256), losses := [] }

theorem u2305 : Upper (D 8) (R 8) [34,68,288,96,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2305 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2306 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 70 292 104 145 40 209 145 401), lower := (rows 35 70 292 104 145 40 64 128 256), losses := [] }

theorem u2306 : Upper (D 8) (R 8) [34,68,288,96,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2306 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2307 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 35 70 292 104 145 48 201 137 393), lower := (rows 35 70 292 104 145 48 64 128 256), losses := [] }

theorem u2307 : Upper (D 8) (R 8) [34,68,288,96,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2307 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2308 : Route 9 := (fun mask => (mask,id))

def c2308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2308 : Upper (D 8) (R 8) [34,68,288,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,96,129,128] 13 (by decide) (choices 1) [1,8,16] r2308 c2308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u293
  · exact u294
  · exact u295

def b2309 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 292 104 152 33 209 145 401), lower := (rows 35 70 292 104 152 33 64 128 256), losses := [] }

theorem u2309 : Upper (D 8) (R 8) [34,68,288,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2309 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 70 292 104 152 48 193 129 385), lower := (rows 35 70 292 104 152 48 64 128 256), losses := [] }

theorem u2310 : Upper (D 8) (R 8) [34,68,288,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2310 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r2311 : Route 9 := (fun mask => (mask,id))

def c2311 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2311 : Upper (D 8) (R 8) [34,68,288,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,68,288,96,136,128] 13 (by decide) (choices 1) [1,16] r2311 c2311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u296
  · exact u297

def b2312 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 137 176 33 88 216 344), lower := (rows 35 70 292 137 176 33 64 128 256), losses := [] }

theorem u2312 : Upper (D 8) (R 8) [34,68,288,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2312 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 70 292 137 176 40 81 209 337), lower := (rows 35 70 292 137 176 40 64 128 256), losses := [] }

theorem u2313 : Upper (D 8) (R 8) [34,68,288,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2313 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 70 292 137 176 48 73 201 329), lower := (rows 35 70 292 137 176 48 64 128 256), losses := [] }

theorem u2314 : Upper (D 8) (R 8) [34,68,288,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2314 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 292 137 176 96 89 153 281), lower := (rows 35 70 292 137 176 96 64 128 256), losses := [] }

theorem u2315 : Upper (D 8) (R 8) [34,68,288,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2315 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 137 208 33 120 184 312), lower := (rows 35 70 292 137 208 33 64 128 256), losses := [] }

theorem u2316 : Upper (D 8) (R 8) [34,68,288,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 70 292 137 208 40 113 177 305), lower := (rows 35 70 292 137 208 40 64 128 256), losses := [] }

theorem u2317 : Upper (D 8) (R 8) [34,68,288,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2317 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 70 292 137 208 48 105 169 297), lower := (rows 35 70 292 137 208 48 64 128 256), losses := [] }

theorem u2318 : Upper (D 8) (R 8) [34,68,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2318 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 292 168 208 33 89 153 281), lower := (rows 35 70 292 168 208 33 64 128 256), losses := [] }

theorem u2319 : Upper (D 8) (R 8) [34,68,288,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 292 168 208 40 81 145 273), lower := (rows 35 70 292 168 208 40 64 128 256), losses := [] }

theorem u2320 : Upper (D 8) (R 8) [34,68,288,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2320 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2321 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 292 168 208 48 73 137 265), lower := (rows 35 70 292 168 208 48 64 128 256), losses := [] }

theorem u2321 : Upper (D 8) (R 8) [34,68,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2321 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2322 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 25 176 33 104 232 360), lower := (rows 35 70 388 25 176 33 64 128 256), losses := [] }

theorem u2322 : Upper (D 8) (R 8) [34,68,384,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2323 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 70 388 25 176 40 97 225 353), lower := (rows 35 70 388 25 176 40 64 128 256), losses := [] }

theorem u2323 : Upper (D 8) (R 8) [34,68,384,17,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2323 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2324 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 388 25 176 96 105 169 297), lower := (rows 35 70 388 25 176 96 64 128 256), losses := [] }

theorem u2324 : Upper (D 8) (R 8) [34,68,384,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2325 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 56 208 33 105 169 297), lower := (rows 35 70 388 56 208 33 64 128 256), losses := [] }

theorem u2325 : Upper (D 8) (R 8) [34,68,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2326 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 388 56 208 40 97 161 289), lower := (rows 35 70 388 56 208 40 64 128 256), losses := [] }

theorem u2326 : Upper (D 8) (R 8) [34,68,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2326 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2327 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 388 88 176 33 105 169 297), lower := (rows 35 70 388 88 176 33 64 128 256), losses := [] }

theorem u2327 : Upper (D 8) (R 8) [34,68,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2327 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2328 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 388 88 176 40 97 161 289), lower := (rows 35 70 388 88 176 40 64 128 256), losses := [] }

theorem u2328 : Upper (D 8) (R 8) [34,68,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2328 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2329 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 152 33 113 177 305), lower := (rows 35 70 388 104 152 33 64 128 256), losses := [] }

theorem u2329 : Upper (D 8) (R 8) [34,68,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2330 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 70 388 104 152 48 97 161 289), lower := (rows 35 70 388 104 152 48 64 128 256), losses := [] }

theorem u2330 : Upper (D 8) (R 8) [34,68,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2330 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2331 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 388 104 176 33 89 153 281), lower := (rows 35 70 388 104 176 33 64 128 256), losses := [] }

theorem u2331 : Upper (D 8) (R 8) [34,68,384,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 70 388 104 176 40 81 145 273), lower := (rows 35 70 388 104 176 40 64 128 256), losses := [] }

theorem u2332 : Upper (D 8) (R 8) [34,68,384,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2332 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 70 388 104 176 48 73 137 265), lower := (rows 35 70 388 104 176 48 64 128 256), losses := [] }

theorem u2333 : Upper (D 8) (R 8) [34,68,384,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2333 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 28 304 33 224 224 480), lower := (rows 35 194 13 28 304 33 64 128 256), losses := [] }

theorem u2334 : Upper (D 8) (R 8) [34,192,9,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2335 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 28 304 96 225 161 417), lower := (rows 35 194 13 28 304 96 64 128 256), losses := [] }

theorem u2335 : Upper (D 8) (R 8) [34,192,9,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2336 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 56 276 33 224 224 480), lower := (rows 35 194 13 56 276 33 64 128 256), losses := [] }

theorem u2336 : Upper (D 8) (R 8) [34,192,9,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 56 276 96 225 161 417), lower := (rows 35 194 13 56 276 96 64 128 256), losses := [] }

theorem u2337 : Upper (D 8) (R 8) [34,192,9,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2337 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 56 336 33 228 164 420), lower := (rows 35 194 13 56 336 33 64 128 256), losses := [] }

theorem u2338 : Upper (D 8) (R 8) [34,192,9,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2339 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 13 56 336 36 225 161 417), lower := (rows 35 194 13 56 336 36 64 128 256), losses := [] }

theorem u2339 : Upper (D 8) (R 8) [34,192,9,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2339 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P08
