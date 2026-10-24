import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0016

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2280 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 1, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 98 100 152 280 421 453 389 389), lower := (rows 35 98 100 152 280 32 64 128 256), losses := [] }

theorem u2280 : Upper (D 10) (R 10) [34,96,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2280 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2281 : PairBound 9 := { available := 332, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 152 304 364 332 460 332), lower := (rows 35 98 133 152 304 32 64 128 256), losses := [] }

theorem u2281 : Upper (D 10) (R 10) [34,96,129,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2281 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2282 : PairBound 9 := { available := 300, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 152 336 300 364 428 300), lower := (rows 35 98 133 152 336 32 64 128 256), losses := [] }

theorem u2282 : Upper (D 10) (R 10) [34,96,129,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2282 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2283 : PairBound 9 := { available := 344, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 168 276 376 344 472 344), lower := (rows 35 98 133 168 276 32 64 128 256), losses := [] }

theorem u2283 : Upper (D 10) (R 10) [34,96,129,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2283 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2284 : PairBound 9 := { available := 340, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 168 280 372 340 468 340), lower := (rows 35 98 133 168 280 32 64 128 256), losses := [] }

theorem u2284 : Upper (D 10) (R 10) [34,96,129,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2284 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2285 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 168 336 316 348 412 284), lower := (rows 35 98 133 168 336 32 64 128 256), losses := [] }

theorem u2285 : Upper (D 10) (R 10) [34,96,129,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2285 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2286 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 200 276 312 376 440 312), lower := (rows 35 98 133 200 276 32 64 128 256), losses := [] }

theorem u2286 : Upper (D 10) (R 10) [34,96,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2286 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2287 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 200 280 308 372 436 308), lower := (rows 35 98 133 200 280 32 64 128 256), losses := [] }

theorem u2287 : Upper (D 10) (R 10) [34,96,129,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2287 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2288 : PairBound 9 := { available := 284, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 200 304 316 348 412 284), lower := (rows 35 98 133 200 304 32 64 128 256), losses := [] }

theorem u2288 : Upper (D 10) (R 10) [34,96,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2288 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2289 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 268 304 248 216 216 472), lower := (rows 35 98 133 268 304 32 64 128 256), losses := [] }

theorem u2289 : Upper (D 10) (R 10) [34,96,129,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2289 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2290 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 268 336 184 248 184 440), lower := (rows 35 98 133 268 336 32 64 128 256), losses := [] }

theorem u2290 : Upper (D 10) (R 10) [34,96,129,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2290 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2291 : PairBound 9 := { available := 120, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 268 400 120 120 248 376), lower := (rows 35 98 133 268 400 32 64 128 256), losses := [] }

theorem u2291 : Upper (D 10) (R 10) [34,96,129,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2291 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2292 : PairBound 9 := { available := 156, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 296 336 188 220 156 412), lower := (rows 35 98 133 296 336 32 64 128 256), losses := [] }

theorem u2292 : Upper (D 10) (R 10) [34,96,129,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2292 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2293 : PairBound 9 := { available := 92, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 296 400 124 92 220 348), lower := (rows 35 98 133 296 400 32 64 128 256), losses := [] }

theorem u2293 : Upper (D 10) (R 10) [34,96,129,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2293 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2294 : PairBound 9 := { available := 60, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 133 328 400 60 124 188 316), lower := (rows 35 98 133 328 400 32 64 128 256), losses := [] }

theorem u2294 : Upper (D 10) (R 10) [34,96,129,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2294 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2295 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 296 208 309 341 405 277), lower := (rows 35 98 140 296 208 32 64 128 256), losses := [] }

theorem u2295 : Upper (D 10) (R 10) [34,96,136,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2295 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2296 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 296 336 181 213 149 405), lower := (rows 35 98 140 296 336 32 64 128 256), losses := [] }

theorem u2296 : Upper (D 10) (R 10) [34,96,136,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2296 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2297 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 296 400 117 85 213 341), lower := (rows 35 98 140 296 400 32 64 128 256), losses := [] }

theorem u2297 : Upper (D 10) (R 10) [34,96,136,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2297 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2298 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 328 176 309 341 405 277), lower := (rows 35 98 140 328 176 32 64 128 256), losses := [] }

theorem u2298 : Upper (D 10) (R 10) [34,96,136,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2298 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2299 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 328 304 181 213 149 405), lower := (rows 35 98 140 328 304 32 64 128 256), losses := [] }

theorem u2299 : Upper (D 10) (R 10) [34,96,136,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2299 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2300 : PairBound 9 := { available := 53, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 140 328 400 53 117 181 309), lower := (rows 35 98 140 328 400 32 64 128 256), losses := [] }

theorem u2300 : Upper (D 10) (R 10) [34,96,136,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2300 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2301 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 164 328 400 61 93 157 285), lower := (rows 35 98 164 328 400 32 64 128 256), losses := [] }

theorem u2301 : Upper (D 10) (R 10) [34,96,160,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2301 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2302 : PairBound 9 := { available := 308, camps := [{ cop := 1, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 35 194 44 200 273 308 372 436 308), lower := (rows 35 194 44 200 273 32 64 128 256), losses := [] }

theorem u2302 : Upper (D 10) (R 10) [34,192,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2302 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2303 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 35 194 44 200 304 309 341 405 277), lower := (rows 35 194 44 200 304 32 64 128 256), losses := [] }

theorem u2303 : Upper (D 10) (R 10) [34,192,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2303 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2304 : PairBound 9 := { available := 308, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7),(3,7)], upper := (rows 35 194 44 328 145 308 372 436 308), lower := (rows 35 194 44 328 145 32 64 128 256), losses := [] }

theorem u2304 : Upper (D 10) (R 10) [34,192,40,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2304 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2305 : Route 9 := (fun mask => (mask,id))

def c2305 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2305 : Upper (D 10) (R 10) [34,192,40,320,132] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,132] 13 (by decide) (choices 1) [1,16,256] r2305 c2305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u971
  · exact u972
  · exact u973

def r2306 : Route 9 := (fun mask => (mask,id))

def c2306 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2306 : Upper (D 10) (R 10) [34,192,40,320,160] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,160] 13 (by decide) (choices 1) [1,4,16,256] r2306 c2306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u974
  · exact u975
  · exact u976
  · exact u977

theorem m2307_4 : Upper (D 10) (R 10) [34,192,40,320,384,4] 13 :=
  permutation_upper _ _ _ [34,192,40,320,384,1] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u978

def r2307 : Route 9 := (fun mask => (mask,id))

def c2307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2307 : Upper (D 10) (R 10) [34,192,40,320,384] 13 := by
  apply FastRouting.sound _ _ [34,192,40,320,384] 13 (by decide) (choices 1) [1,4,16] r2307 c2307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u978
  · exact m2307_4
  · exact u979

def b2308 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 140 280 304 368 432 304), lower := (rows 35 194 69 140 280 32 64 128 256), losses := [] }

theorem u2308 : Upper (D 10) (R 10) [34,192,65,132,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2308 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2309 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 140 304 312 376 440 312), lower := (rows 35 194 69 140 304 32 64 128 256), losses := [] }

theorem u2309 : Upper (D 10) (R 10) [34,192,65,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2309 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2310 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 152 276 296 360 424 296), lower := (rows 35 194 69 152 276 32 64 128 256), losses := [] }

theorem u2310 : Upper (D 10) (R 10) [34,192,65,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2310 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2311 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 69 152 280 292 356 420 292), lower := (rows 35 194 69 152 280 32 64 128 256), losses := [] }

theorem u2311 : Upper (D 10) (R 10) [34,192,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2311 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2312 : PairBound 9 := { available := 300, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 152 304 300 364 428 300), lower := (rows 35 194 69 152 304 32 64 128 256), losses := [] }

theorem u2312 : Upper (D 10) (R 10) [34,192,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2312 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2313 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 168 276 312 376 440 312), lower := (rows 35 194 69 168 276 32 64 128 256), losses := [] }

theorem u2313 : Upper (D 10) (R 10) [34,192,65,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2313 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2314 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 168 280 308 372 436 308), lower := (rows 35 194 69 168 280 32 64 128 256), losses := [] }

theorem u2314 : Upper (D 10) (R 10) [34,192,65,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2314 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2315 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 168 304 316 348 412 284), lower := (rows 35 194 69 168 304 32 64 128 256), losses := [] }

theorem u2315 : Upper (D 10) (R 10) [34,192,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2315 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2316 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 268 304 184 248 184 440), lower := (rows 35 194 69 268 304 32 64 128 256), losses := [] }

theorem u2316 : Upper (D 10) (R 10) [34,192,65,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2316 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2317 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 268 400 56 120 184 312), lower := (rows 35 194 69 268 400 32 64 128 256), losses := [] }

theorem u2317 : Upper (D 10) (R 10) [34,192,65,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2317 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2318 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 35 194 69 296 400 60 124 188 316), lower := (rows 35 194 69 296 400 32 64 128 256), losses := [] }

theorem u2318 : Upper (D 10) (R 10) [34,192,65,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2318 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2319 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 12, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 35 194 76 140 273 304 368 432 304), lower := (rows 35 194 76 140 273 32 64 128 256), losses := [] }

theorem u2319 : Upper (D 10) (R 10) [34,192,72,132,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2319 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2320 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 12, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 35 194 76 140 304 305 369 433 305), lower := (rows 35 194 76 140 304 32 64 128 256), losses := [] }

theorem u2320 : Upper (D 10) (R 10) [34,192,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2320 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2321 : Route 9 := (fun mask => (mask,id))

def c2321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2321 : Upper (D 10) (R 10) [34,192,72,144,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,257] 13 (by decide) (choices 1) [4,256] r2321 c2321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u980
  · exact u981

def b2322 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7)], upper := (rows 35 194 76 152 276 289 353 417 289), lower := (rows 35 194 76 152 276 32 64 128 256), losses := [] }

theorem u2322 : Upper (D 10) (R 10) [34,192,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2322 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2323 : Route 9 := (fun mask => (mask,id))

def c2323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2323 : Upper (D 10) (R 10) [34,192,72,144,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,144,288] 13 (by decide) (choices 1) [1,4,256] r2323 c2323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u982
  · exact u983
  · exact u984

def r2324 : Route 9 := (fun mask => (mask,id))

def c2324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2324 : Upper (D 10) (R 10) [34,192,72,160,257] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257] 13 (by decide) (choices 1) [4,16,256] r2324 c2324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u985
  · exact u986
  · exact u987

def r2325 : Route 9 := (fun mask => (mask,id))

def c2325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2325 : Upper (D 10) (R 10) [34,192,72,160,260] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260] 13 (by decide) (choices 1) [1,16,256] r2325 c2325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u988
  · exact u989
  · exact u990

def r2326 : Route 9 := (fun mask => (mask,id))

def c2326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2326 : Upper (D 10) (R 10) [34,192,72,160,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,288] 13 (by decide) (choices 1) [1,4,16,256] r2326 c2326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u991
  · exact u992
  · exact u993
  · exact u994

def r2327 : Route 9 := (fun mask => (mask,id))

def c2327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2327 : Upper (D 10) (R 10) [34,192,72,257,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,160] 13 (by decide) (choices 1) [4,16,256] r2327 c2327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u995
  · exact u996
  · exact u997

def b2328 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 265 276 176 240 176 432), lower := (rows 35 194 76 265 276 32 64 128 256), losses := [] }

theorem u2328 : Upper (D 10) (R 10) [34,192,72,257,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2328 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2329 : Route 9 := (fun mask => (mask,id))

def c2329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2329 : Upper (D 10) (R 10) [34,192,72,257,288] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,288] 13 (by decide) (choices 1) [4,16,128] r2329 c2329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u998
  · exact u999
  · exact u1000

def r2330 : Route 9 := (fun mask => (mask,id))

def c2330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2330 : Upper (D 10) (R 10) [34,192,72,257,384] 13 := by
  apply FastRouting.sound _ _ [34,192,72,257,384] 13 (by decide) (choices 1) [4,16] r2330 c2330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1001
  · exact u1002

def b2331 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 76 268 176 305 369 433 305), lower := (rows 35 194 76 268 176 32 64 128 256), losses := [] }

theorem u2331 : Upper (D 10) (R 10) [34,192,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2331 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2332 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 76 268 273 176 240 176 432), lower := (rows 35 194 76 268 273 32 64 128 256), losses := [] }

theorem u2332 : Upper (D 10) (R 10) [34,192,72,260,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2332 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2333 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 76 268 304 177 241 177 433), lower := (rows 35 194 76 268 304 32 64 128 256), losses := [] }

theorem u2333 : Upper (D 10) (R 10) [34,192,72,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2333 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2334 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 76 268 400 49 113 177 305), lower := (rows 35 194 76 268 400 32 64 128 256), losses := [] }

theorem u2334 : Upper (D 10) (R 10) [34,192,72,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2334 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2335 : Route 9 := (fun mask => (mask,id))

def c2335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2335 : Upper (D 10) (R 10) [34,192,72,272,160] 13 := by
  apply FastRouting.sound _ _ [34,192,72,272,160] 13 (by decide) (choices 1) [1,4,256] r2335 c2335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1003
  · exact u1004
  · exact u1005

def b2336 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 280 273 164 228 164 420), lower := (rows 35 194 76 280 273 32 64 128 256), losses := [] }

theorem u2336 : Upper (D 10) (R 10) [34,192,72,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2336 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2337 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 280 276 161 225 161 417), lower := (rows 35 194 76 280 276 32 64 128 256), losses := [] }

theorem u2337 : Upper (D 10) (R 10) [34,192,72,272,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2337 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2338 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 280 304 165 229 165 421), lower := (rows 35 194 76 280 304 32 64 128 256), losses := [] }

theorem u2338 : Upper (D 10) (R 10) [34,192,72,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2338 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2339 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 280 400 37 101 165 293), lower := (rows 35 194 76 280 400 32 64 128 256), losses := [] }

theorem u2339 : Upper (D 10) (R 10) [34,192,72,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2339 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2339
end Delivery.IrregularNine14.P10
