import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 266 336 40 65 144 400), lower := (rows 97 7 164 266 336 40 65 128 256), losses := [] }

theorem u2400 : Upper (D 9) (R 9) [96,5,160,258,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2400 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 7 164 266 336 40 80 129 385), lower := (rows 97 7 164 266 336 40 80 128 256), losses := [] }

theorem u2401 : Upper (D 9) (R 9) [96,5,160,258,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2401 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(3,5),(4,5)], upper := (rows 97 7 164 266 336 40 192 145 273), lower := (rows 97 7 164 266 336 40 192 128 256), losses := [] }

theorem u2402 : Upper (D 9) (R 9) [96,5,160,258,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2402 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 266 400 40 65 208 336), lower := (rows 97 7 164 266 400 40 65 128 256), losses := [] }

theorem u2403 : Upper (D 9) (R 9) [96,5,160,258,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2403 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5)], upper := (rows 97 7 164 266 400 40 80 193 321), lower := (rows 97 7 164 266 400 40 80 128 256), losses := [] }

theorem u2404 : Upper (D 9) (R 9) [96,5,160,258,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2404 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 164 328 400 34 65 152 280), lower := (rows 97 7 164 328 400 34 65 128 256), losses := [] }

theorem u2405 : Upper (D 9) (R 9) [96,5,160,320,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2405 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 7 164 328 400 34 72 145 273), lower := (rows 97 7 164 328 400 34 72 128 256), losses := [] }

theorem u2406 : Upper (D 9) (R 9) [96,5,160,320,384,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2406 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 164 328 400 34 80 137 265), lower := (rows 97 7 164 328 400 34 80 128 256), losses := [] }

theorem u2407 : Upper (D 9) (R 9) [96,5,160,320,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2407 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 26 145 40 96 448 320), lower := (rows 97 7 388 26 145 40 96 128 256), losses := [] }

theorem u2408 : Upper (D 9) (R 9) [96,5,384,18,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2408 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2409 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 388, targets := 1 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(3,8),(4,8)], upper := (rows 97 7 388 26 145 40 320 224 352), lower := (rows 97 7 388 26 145 40 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 10 19 42 64 129 0), good := (rows 241 191 132 58 145 40 64 128 0) }] }

theorem u2409 : Upper (D 9) (R 9) [96,5,384,18,129,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2409 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 388 26 145 96 320 168 296), lower := (rows 97 7 388 26 145 96 320 128 256), losses := [] }

theorem u2410 : Upper (D 9) (R 9) [96,5,384,18,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2410 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 388 26 176 33 72 448 320), lower := (rows 97 7 388 26 176 33 72 128 256), losses := [] }

theorem u2411 : Upper (D 9) (R 9) [96,5,384,18,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2411 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2412 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 452, targets := 33 },{ cop := 6, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(2,0),(2,5)], upper := (rows 97 7 388 26 176 33 320 200 328), lower := (rows 97 7 388 26 176 33 320 128 256), losses := [] }

theorem u2412 : Upper (D 9) (R 9) [96,5,384,18,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2412 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 388 26 176 40 65 448 320), lower := (rows 97 7 388 26 176 40 65 128 256), losses := [] }

theorem u2413 : Upper (D 9) (R 9) [96,5,384,18,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2413 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,8)], upper := (rows 97 7 388 26 176 40 320 193 321), lower := (rows 97 7 388 26 176 40 320 128 256), losses := [] }

theorem u2414 : Upper (D 9) (R 9) [96,5,384,18,160,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2414 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2415 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 388 42 145 48 72 448 320), lower := (rows 97 7 388 42 145 48 72 128 256), losses := [] }

theorem u2415 : Upper (D 9) (R 9) [96,5,384,34,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2415 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2416 : Route 9 := (fun mask => (mask,id))

def c2416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2416 : Upper (D 9) (R 9) [96,5,384,34,129,16,256] 13 := by
  apply FastRouting.sound _ _ [96,5,384,34,129,16,256] 13 (by decide) (choices 1) [8,64] r2416 c2416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u140
  · exact u141

def b2417 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 388 56 145 34 72 448 320), lower := (rows 97 7 388 56 145 34 72 128 256), losses := [] }

theorem u2417 : Upper (D 9) (R 9) [96,5,384,48,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2417 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 152, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,8),(4,8)], upper := (rows 97 7 388 56 145 34 320 200 328), lower := (rows 97 7 388 56 145 34 320 128 256), losses := [] }

theorem u2418 : Upper (D 9) (R 9) [96,5,384,48,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2418 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 152, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,8),(4,8)], upper := (rows 97 7 388 56 145 288 66 200 328), lower := (rows 97 7 388 56 145 288 66 128 256), losses := [] }

theorem u2419 : Upper (D 9) (R 9) [96,5,384,48,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2419 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 388 56 145 288 72 194 322), lower := (rows 97 7 388 56 145 288 72 128 256), losses := [] }

theorem u2420 : Upper (D 9) (R 9) [96,5,384,48,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2420 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2421 : Route 9 := (fun mask => (mask,id))

def c2421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2421 : Upper (D 9) (R 9) [96,5,384,48,130,256,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,130,256,1] 13 (by decide) (choices 1) [8,64] r2421 c2421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u142
  · exact u143

def b2422 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(4,5)], upper := (rows 97 7 388 56 146 288 72 193 321), lower := (rows 97 7 388 56 146 288 72 128 256), losses := [] }

theorem u2422 : Upper (D 9) (R 9) [96,5,384,48,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2422 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 388 56 208 33 66 392 264), lower := (rows 97 7 388 56 208 33 66 128 256), losses := [] }

theorem u2423 : Upper (D 9) (R 9) [96,5,384,48,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2423 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 388 56 208 33 72 386 258), lower := (rows 97 7 388 56 208 33 72 128 256), losses := [] }

theorem u2424 : Upper (D 9) (R 9) [96,5,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2424 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 41, targets := 384 },{ cop := 2, region := 80, targets := 1 }], pairs := [(0,7),(0,8),(3,7),(3,8),(4,0)], upper := (rows 97 7 388 56 208 33 320 138 266), lower := (rows 97 7 388 56 208 33 320 128 256), losses := [] }

theorem u2425 : Upper (D 9) (R 9) [96,5,384,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2425 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 97 7 388 56 208 34 65 392 264), lower := (rows 97 7 388 56 208 34 65 128 256), losses := [] }

theorem u2426 : Upper (D 9) (R 9) [96,5,384,48,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2426 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 388 56 208 34 72 385 257), lower := (rows 97 7 388 56 208 34 72 128 256), losses := [] }

theorem u2427 : Upper (D 9) (R 9) [96,5,384,48,192,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2427 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 256 },{ cop := 2, region := 80, targets := 33 }], pairs := [(3,8),(4,0),(4,5),(4,8)], upper := (rows 97 7 388 56 208 34 320 137 265), lower := (rows 97 7 388 56 208 34 320 128 256), losses := [] }

theorem u2428 : Upper (D 9) (R 9) [96,5,384,48,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2428 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2429 : Route 9 := (fun mask => (mask,id))

def c2429 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2429 : Upper (D 9) (R 9) [96,5,384,48,192,256,1] 13 := by
  apply FastRouting.sound _ _ [96,5,384,48,192,256,1] 13 (by decide) (choices 1) [2,8] r2429 c2429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u144
  · exact u145

def b2430 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(3,8),(4,8)], upper := (rows 97 7 388 56 208 288 66 137 265), lower := (rows 97 7 388 56 208 288 66 128 256), losses := [] }

theorem u2430 : Upper (D 9) (R 9) [96,5,384,48,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2430 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,5),(1,6),(2,5),(4,5)], upper := (rows 97 7 388 56 208 288 72 131 259), lower := (rows 97 7 388 56 208 288 72 128 256), losses := [] }

theorem u2431 : Upper (D 9) (R 9) [96,5,384,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2431 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 233, targets := 256 },{ cop := 0, region := 388, targets := 1 }], pairs := [(0,8),(2,0),(3,8)], upper := (rows 97 7 388 137 274 40 80 224 352), lower := (rows 97 7 388 137 274 40 80 128 256), losses := [] }

theorem u2432 : Upper (D 9) (R 9) [96,5,384,129,258,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2432 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 137 274 40 96 208 336), lower := (rows 97 7 388 137 274 40 96 128 256), losses := [] }

theorem u2433 : Upper (D 9) (R 9) [96,5,384,129,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2433 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 137 274 48 96 200 328), lower := (rows 97 7 388 137 274 48 96 128 256), losses := [] }

theorem u2434 : Upper (D 9) (R 9) [96,5,384,129,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2434 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 388, targets := 1 },{ cop := 0, region := 136, targets := 256 }], pairs := [(2,0),(3,8),(4,0)], upper := (rows 97 7 388 137 280 34 80 224 352), lower := (rows 97 7 388 137 280 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 34 88 129 257), good := (rows 484 422 388 476 348 38 80 128 256) }] }

theorem u2435 : Upper (D 9) (R 9) [96,5,384,129,264,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2435 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 137 280 34 96 208 336), lower := (rows 97 7 388 137 280 34 96 128 256), losses := [] }

theorem u2436 : Upper (D 9) (R 9) [96,5,384,129,264,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2436 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 137 280 48 96 194 322), lower := (rows 97 7 388 137 280 48 96 128 256), losses := [] }

theorem u2437 : Upper (D 9) (R 9) [96,5,384,129,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2437 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2438 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 388 137 304 34 72 208 336), lower := (rows 97 7 388 137 304 34 72 128 256), losses := [] }

theorem u2438 : Upper (D 9) (R 9) [96,5,384,129,288,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2438 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 7 388 137 304 34 80 200 328), lower := (rows 97 7 388 137 304 34 80 128 256), losses := [] }

theorem u2439 : Upper (D 9) (R 9) [96,5,384,129,288,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2439 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 97 7 388 137 304 40 66 208 336), lower := (rows 97 7 388 137 304 40 66 128 256), losses := [] }

theorem u2440 : Upper (D 9) (R 9) [96,5,384,129,288,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2440 [(5,3),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 7 388 137 304 40 80 194 322), lower := (rows 97 7 388 137 304 40 80 128 256), losses := [] }

theorem u2441 : Upper (D 9) (R 9) [96,5,384,129,288,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2441 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 369, targets := 128 },{ cop := 0, region := 388, targets := 1 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(2,0),(4,7)], upper := (rows 97 7 388 138 280 33 80 224 352), lower := (rows 97 7 388 138 280 33 80 128 256), losses := [] }

theorem u2442 : Upper (D 9) (R 9) [96,5,384,130,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2442 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2443 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 388 138 280 33 96 208 336), lower := (rows 97 7 388 138 280 33 96 128 256), losses := [] }

theorem u2443 : Upper (D 9) (R 9) [96,5,384,130,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2443 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 404, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 97 7 388 138 304 33 72 208 336), lower := (rows 97 7 388 138 304 33 72 128 256), losses := [] }

theorem u2444 : Upper (D 9) (R 9) [96,5,384,130,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2444 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 7 388 138 304 33 80 200 328), lower := (rows 97 7 388 138 304 33 80 128 256), losses := [] }

theorem u2445 : Upper (D 9) (R 9) [96,5,384,130,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2445 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2446 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 404, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8)], upper := (rows 97 7 388 138 304 40 65 208 336), lower := (rows 97 7 388 138 304 40 65 128 256), losses := [] }

theorem u2446 : Upper (D 9) (R 9) [96,5,384,130,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2446 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 7 388 138 304 40 80 193 321), lower := (rows 97 7 388 138 304 40 80 128 256), losses := [] }

theorem u2447 : Upper (D 9) (R 9) [96,5,384,130,288,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2447 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 7 388 152 304 33 66 200 328), lower := (rows 97 7 388 152 304 33 66 128 256), losses := [] }

theorem u2448 : Upper (D 9) (R 9) [96,5,384,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2448 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2449 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 3, region := 97, targets := 384 }], pairs := [(0,7),(0,8),(1,5),(2,5)], upper := (rows 97 7 388 152 304 33 72 194 322), lower := (rows 97 7 388 152 304 33 72 128 256), losses := [] }

theorem u2449 : Upper (D 9) (R 9) [96,5,384,144,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2449 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2450 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 7 388 152 304 34 65 200 328), lower := (rows 97 7 388 152 304 34 65 128 256), losses := [] }

theorem u2450 : Upper (D 9) (R 9) [96,5,384,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2450 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 390, targets := 32 },{ cop := 4, region := 201, targets := 256 }], pairs := [(0,8),(1,5),(2,5)], upper := (rows 97 7 388 152 304 34 72 193 321), lower := (rows 97 7 388 152 304 34 72 128 256), losses := [] }

theorem u2451 : Upper (D 9) (R 9) [96,5,384,144,288,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2451 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 97 7 388 168 336 33 66 152 280), lower := (rows 97 7 388 168 336 33 66 128 256), losses := [] }

theorem u2452 : Upper (D 9) (R 9) [96,5,384,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2452 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2453 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 2, region := 105, targets := 256 }], pairs := [(0,8),(1,5),(2,5),(4,5)], upper := (rows 97 7 388 168 336 33 72 146 274), lower := (rows 97 7 388 168 336 33 72 128 256), losses := [] }

theorem u2453 : Upper (D 9) (R 9) [96,5,384,160,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2453 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 113, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6)], upper := (rows 97 7 388 168 336 33 80 138 266), lower := (rows 97 7 388 168 336 33 80 128 256), losses := [] }

theorem u2454 : Upper (D 9) (R 9) [96,5,384,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2454 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 97 7 388 168 336 34 72 145 273), lower := (rows 97 7 388 168 336 34 72 128 256), losses := [] }

theorem u2455 : Upper (D 9) (R 9) [96,5,384,160,320,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2455 [(5,1),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 7 388 168 336 34 80 137 265), lower := (rows 97 7 388 168 336 34 80 128 256), losses := [] }

theorem u2456 : Upper (D 9) (R 9) [96,5,384,160,320,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2456 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 14 22 137 176 288 65 448 320), lower := (rows 97 14 22 137 176 288 65 128 256), losses := [] }

theorem u2457 : Upper (D 9) (R 9) [96,12,18,129,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 0, region := 136, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 14 22 137 176 288 320 193 321), lower := (rows 97 14 22 137 176 288 320 128 256), losses := [] }

theorem u2458 : Upper (D 9) (R 9) [96,12,18,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 14 22 137 273 96 192 416 288), lower := (rows 97 14 22 137 273 96 192 128 256), losses := [] }

theorem u2459 : Upper (D 9) (R 9) [96,12,18,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P09
