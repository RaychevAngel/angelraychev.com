import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2340 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 56 336 160 101 165 293), lower := (rows 35 194 13 56 336 160 64 128 256), losses := [] }

theorem u2340 : Upper (D 8) (R 8) [34,192,9,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2341 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 35 194 13 268 112 33 240 176 432), lower := (rows 35 194 13 268 112 33 64 128 256), losses := [] }

theorem u2341 : Upper (D 8) (R 8) [34,192,9,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2342 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 13 268 112 48 225 161 417), lower := (rows 35 194 13 268 112 48 64 128 256), losses := [] }

theorem u2342 : Upper (D 8) (R 8) [34,192,9,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2342 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2343 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 268 112 160 113 177 305), lower := (rows 35 194 13 268 112 160 64 128 256), losses := [] }

theorem u2343 : Upper (D 8) (R 8) [34,192,9,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2344 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 280 52 33 224 224 480), lower := (rows 35 194 13 280 52 33 64 128 256), losses := [] }

theorem u2344 : Upper (D 8) (R 8) [34,192,9,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2345 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 280 52 96 225 161 417), lower := (rows 35 194 13 280 52 96 64 128 256), losses := [] }

theorem u2345 : Upper (D 8) (R 8) [34,192,9,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2346 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 13 280 112 33 228 164 420), lower := (rows 35 194 13 280 112 33 64 128 256), losses := [] }

theorem u2346 : Upper (D 8) (R 8) [34,192,9,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2347 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 13 280 112 36 225 161 417), lower := (rows 35 194 13 280 112 36 64 128 256), losses := [] }

theorem u2347 : Upper (D 8) (R 8) [34,192,9,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2347 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2348 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 280 112 160 101 165 293), lower := (rows 35 194 13 280 112 160 64 128 256), losses := [] }

theorem u2348 : Upper (D 8) (R 8) [34,192,9,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2349 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 296 52 33 208 208 464), lower := (rows 35 194 13 296 52 33 64 128 256), losses := [] }

theorem u2349 : Upper (D 8) (R 8) [34,192,9,288,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2350 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 194 13 296 52 48 193 193 449), lower := (rows 35 194 13 296 52 48 64 128 256), losses := [] }

theorem u2350 : Upper (D 8) (R 8) [34,192,9,288,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2350 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2351 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 13 296 52 96 209 145 401), lower := (rows 35 194 13 296 52 96 64 128 256), losses := [] }

theorem u2351 : Upper (D 8) (R 8) [34,192,9,288,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2352 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 13 296 84 33 240 176 432), lower := (rows 35 194 13 296 84 33 64 128 256), losses := [] }

theorem u2352 : Upper (D 8) (R 8) [34,192,9,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2353 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 13 296 84 48 225 161 417), lower := (rows 35 194 13 296 84 48 64 128 256), losses := [] }

theorem u2353 : Upper (D 8) (R 8) [34,192,9,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2353 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2354 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 296 84 160 113 177 305), lower := (rows 35 194 13 296 84 160 64 128 256), losses := [] }

theorem u2354 : Upper (D 8) (R 8) [34,192,9,288,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2355 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 13 296 112 33 212 148 404), lower := (rows 35 194 13 296 112 33 64 128 256), losses := [] }

theorem u2355 : Upper (D 8) (R 8) [34,192,9,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2356 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 194 13 296 112 36 209 145 401), lower := (rows 35 194 13 296 112 36 64 128 256), losses := [] }

theorem u2356 : Upper (D 8) (R 8) [34,192,9,288,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2356 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2357 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 194 13 296 112 48 197 133 389), lower := (rows 35 194 13 296 112 48 64 128 256), losses := [] }

theorem u2357 : Upper (D 8) (R 8) [34,192,9,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2357 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2358 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 13 296 112 160 85 149 277), lower := (rows 35 194 13 296 112 160 64 128 256), losses := [] }

theorem u2358 : Upper (D 8) (R 8) [34,192,9,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2359 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 44 273 33 224 224 480), lower := (rows 35 194 28 44 273 33 64 128 256), losses := [] }

theorem u2359 : Upper (D 8) (R 8) [34,192,24,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2360 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 194 28 44 273 96 225 161 417), lower := (rows 35 194 28 44 273 96 64 128 256), losses := [] }

theorem u2360 : Upper (D 8) (R 8) [34,192,24,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2360 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2361 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 28 104 176 33 325 389 261), lower := (rows 35 194 28 104 176 33 64 128 256), losses := [] }

theorem u2361 : Upper (D 8) (R 8) [34,192,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2362 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 194 28 104 176 36 321 385 257), lower := (rows 35 194 28 104 176 36 64 128 256), losses := [] }

theorem u2362 : Upper (D 8) (R 8) [34,192,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2362 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2363 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 28 104 176 288 69 133 261), lower := (rows 35 194 28 104 176 288 64 128 256), losses := [] }

theorem u2363 : Upper (D 8) (R 8) [34,192,24,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2363 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2364 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 28 104 273 33 228 164 420), lower := (rows 35 194 28 104 273 33 64 128 256), losses := [] }

theorem u2364 : Upper (D 8) (R 8) [34,192,24,96,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2364 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2365 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 28 104 273 36 225 161 417), lower := (rows 35 194 28 104 273 36 64 128 256), losses := [] }

theorem u2365 : Upper (D 8) (R 8) [34,192,24,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2365 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2366 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 28 104 273 160 101 165 293), lower := (rows 35 194 28 104 273 160 64 128 256), losses := [] }

theorem u2366 : Upper (D 8) (R 8) [34,192,24,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2367 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 28 104 304 33 197 133 389), lower := (rows 35 194 28 104 304 33 64 128 256), losses := [] }

theorem u2367 : Upper (D 8) (R 8) [34,192,24,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2368 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 28 104 304 36 193 129 385), lower := (rows 35 194 28 104 304 36 64 128 256), losses := [] }

theorem u2368 : Upper (D 8) (R 8) [34,192,24,96,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2368 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2369 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 28 104 304 160 69 133 261), lower := (rows 35 194 28 104 304 160 64 128 256), losses := [] }

theorem u2369 : Upper (D 8) (R 8) [34,192,24,96,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2370 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 28 104 400 33 101 165 293), lower := (rows 35 194 28 104 400 33 64 128 256), losses := [] }

theorem u2370 : Upper (D 8) (R 8) [34,192,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2370 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2371 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 28 104 400 36 97 161 289), lower := (rows 35 194 28 104 400 36 64 128 256), losses := [] }

theorem u2371 : Upper (D 8) (R 8) [34,192,24,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2371 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2372 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 176 33 325 389 261), lower := (rows 35 194 44 88 176 33 64 128 256), losses := [] }

theorem u2372 : Upper (D 8) (R 8) [34,192,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2373 : PairBound 9 := { available := 257, camps := [], pairs := [], upper := (rows 35 194 44 88 176 36 321 385 257), lower := (rows 35 194 44 88 176 36 64 128 256), losses := [] }

theorem u2373 : Upper (D 8) (R 8) [34,192,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2373 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2374 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 44 88 176 288 69 133 261), lower := (rows 35 194 44 88 176 288 64 128 256), losses := [] }

theorem u2374 : Upper (D 8) (R 8) [34,192,40,80,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2374 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2375 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 273 33 228 164 420), lower := (rows 35 194 44 88 273 33 64 128 256), losses := [] }

theorem u2375 : Upper (D 8) (R 8) [34,192,40,80,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2375 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2376 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 44 88 273 36 225 161 417), lower := (rows 35 194 44 88 273 36 64 128 256), losses := [] }

theorem u2376 : Upper (D 8) (R 8) [34,192,40,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2376 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2377 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 88 273 160 101 165 293), lower := (rows 35 194 44 88 273 160 64 128 256), losses := [] }

theorem u2377 : Upper (D 8) (R 8) [34,192,40,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2377 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2378 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 304 33 197 133 389), lower := (rows 35 194 44 88 304 33 64 128 256), losses := [] }

theorem u2378 : Upper (D 8) (R 8) [34,192,40,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2378 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2379 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 44 88 304 36 193 129 385), lower := (rows 35 194 44 88 304 36 64 128 256), losses := [] }

theorem u2379 : Upper (D 8) (R 8) [34,192,40,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2379 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2380 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 88 304 160 69 133 261), lower := (rows 35 194 44 88 304 160 64 128 256), losses := [] }

theorem u2380 : Upper (D 8) (R 8) [34,192,40,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2380 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2381 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 88 400 33 101 165 293), lower := (rows 35 194 44 88 400 33 64 128 256), losses := [] }

theorem u2381 : Upper (D 8) (R 8) [34,192,40,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2381 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2382 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 44 88 400 36 97 161 289), lower := (rows 35 194 44 88 400 36 64 128 256), losses := [] }

theorem u2382 : Upper (D 8) (R 8) [34,192,40,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2382 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2383 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 265 84 33 240 176 432), lower := (rows 35 194 44 265 84 33 64 128 256), losses := [] }

theorem u2383 : Upper (D 8) (R 8) [34,192,40,257,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2383 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2384 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 194 44 265 84 48 225 161 417), lower := (rows 35 194 44 265 84 48 64 128 256), losses := [] }

theorem u2384 : Upper (D 8) (R 8) [34,192,40,257,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2384 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2385 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 265 84 160 113 177 305), lower := (rows 35 194 44 265 84 160 64 128 256), losses := [] }

theorem u2385 : Upper (D 8) (R 8) [34,192,40,257,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2385 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2386 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 44 265 112 33 212 148 404), lower := (rows 35 194 44 265 112 33 64 128 256), losses := [] }

theorem u2386 : Upper (D 8) (R 8) [34,192,40,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2386 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2387 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 194 44 265 112 36 209 145 401), lower := (rows 35 194 44 265 112 36 64 128 256), losses := [] }

theorem u2387 : Upper (D 8) (R 8) [34,192,40,257,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2387 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2388 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 194 44 265 112 48 197 133 389), lower := (rows 35 194 44 265 112 48 64 128 256), losses := [] }

theorem u2388 : Upper (D 8) (R 8) [34,192,40,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2388 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2389 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 265 112 160 85 149 277), lower := (rows 35 194 44 265 112 160 64 128 256), losses := [] }

theorem u2389 : Upper (D 8) (R 8) [34,192,40,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2389 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2390 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 44 268 112 33 209 145 401), lower := (rows 35 194 44 268 112 33 64 128 256), losses := [] }

theorem u2390 : Upper (D 8) (R 8) [34,192,40,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2390 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2391 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 44 268 112 48 193 129 385), lower := (rows 35 194 44 268 112 48 64 128 256), losses := [] }

theorem u2391 : Upper (D 8) (R 8) [34,192,40,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2391 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2392 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 268 112 160 81 145 273), lower := (rows 35 194 44 268 112 160 64 128 256), losses := [] }

theorem u2392 : Upper (D 8) (R 8) [34,192,40,260,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2392 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2393 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 194 44 280 112 33 197 133 389), lower := (rows 35 194 44 280 112 33 64 128 256), losses := [] }

theorem u2393 : Upper (D 8) (R 8) [34,192,40,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2393 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2394 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 194 44 280 112 36 193 129 385), lower := (rows 35 194 44 280 112 36 64 128 256), losses := [] }

theorem u2394 : Upper (D 8) (R 8) [34,192,40,272,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2394 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2395 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 348, targets := 128 }], pairs := [(2,7)], upper := (rows 35 194 44 280 112 160 69 133 261), lower := (rows 35 194 44 280 112 160 64 128 256), losses := [] }

theorem u2395 : Upper (D 8) (R 8) [34,192,40,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2395 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2396 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 148 33 113 177 305), lower := (rows 35 194 44 328 148 33 64 128 256), losses := [] }

theorem u2396 : Upper (D 8) (R 8) [34,192,40,320,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2396 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2397 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 44 328 148 48 97 161 289), lower := (rows 35 194 44 328 148 48 64 128 256), losses := [] }

theorem u2397 : Upper (D 8) (R 8) [34,192,40,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2397 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2398 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 44 328 176 33 85 149 277), lower := (rows 35 194 44 328 176 33 64 128 256), losses := [] }

theorem u2398 : Upper (D 8) (R 8) [34,192,40,320,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2398 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2399 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 44 328 176 36 81 145 273), lower := (rows 35 194 44 328 176 36 64 128 256), losses := [] }

theorem u2399 : Upper (D 8) (R 8) [34,192,40,320,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2399 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2399
end Delivery.IrregularNine14.P08
