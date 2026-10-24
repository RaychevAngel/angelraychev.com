import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0200
import IrregularNine14P07C0201
import IrregularNine14P07C0202

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b30300 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 28 74 208 417 481 417 417), lower := (rows 7 35 28 74 208 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 28 508 208 32 64 128 256) }] }

theorem u30300 : Upper (D 7) (R 7) [6,33,24,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30301 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 232, targets := 1 },{ cop := 0, region := 496, targets := 2 }], pairs := [(2,0),(2,1),(3,0),(4,1)], upper := (rows 7 35 28 74 273 224 224 224 480), lower := (rows 7 35 28 74 273 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 511 511 511 511), good := (rows 494 490 508 490 508 480 480 480 480) },{ target := 1, region := (rows 1 0 12 8 19 511 511 511 511), good := (rows 501 497 508 508 497 480 480 480 480) }] }

theorem u30301 : Upper (D 7) (R 7) [6,33,24,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30302 : Route 9 := (fun mask => (mask,id))

def c30302 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30302 : Upper (D 7) (R 7) [6,33,24,66,288] 13 := by
  apply FastRouting.sound _ _ [6,33,24,66,288] 13 (by decide) (choices 1) [1,64,128] r30302 c30302
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12055
  · exact u12056
  · exact u12057

def b30303 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 28 74 336 161 225 161 417), lower := (rows 7 35 28 74 336 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 28 508 336 32 64 128 256) }] }

theorem u30303 : Upper (D 7) (R 7) [6,33,24,66,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30304 : Route 9 := (fun mask => (mask,id))

def c30304 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30304 : Upper (D 7) (R 7) [6,33,24,66,384] 13 := by
  apply FastRouting.sound _ _ [6,33,24,66,384] 13 (by decide) (choices 1) [1,64,128] r30304 c30304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12058
  · exact u12059
  · exact u12060

def r30305 : Route 9 := (fun mask => (mask,id))

def c30305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30305 : Upper (D 7) (R 7) [6,33,24,96,192] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,192] 13 (by decide) (choices 1) [1,2,128,256] r30305 c30305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12061
  · exact u12062
  · exact u12063
  · exact u12064

def r30306 : Route 9 := (fun mask => (mask,id))

def c30306 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30306 : Upper (D 7) (R 7) [6,33,24,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,257] 13 (by decide) (choices 1) [2,64,128] r30306 c30306
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12065
  · exact u12066
  · exact u12067

def r30307 : Route 9 := (fun mask => (mask,id))

def c30307 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30307 : Upper (D 7) (R 7) [6,33,24,96,258] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,258] 13 (by decide) (choices 1) [1,64,128] r30307 c30307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12068
  · exact u12069
  · exact u12070

def r30308 : Route 9 := (fun mask => (mask,id))

def c30308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30308 : Upper (D 7) (R 7) [6,33,24,96,320] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,320] 13 (by decide) (choices 1) [1,2,128] r30308 c30308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12071
  · exact u12072
  · exact u12073

def r30309 : Route 9 := (fun mask => (mask,id))

def c30309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30309 : Upper (D 7) (R 7) [6,33,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,24,96,384] 13 (by decide) (choices 1) [1,2,64,128] r30309 c30309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12074
  · exact u12075
  · exact u12076
  · exact u12077

def b30310 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 20, targets := 35 }], pairs := [(2,0),(2,1),(2,5),(4,0)], upper := (rows 7 35 28 200 208 291 355 419 291), lower := (rows 7 35 28 200 208 32 64 128 256), losses := [] }

theorem u30310 : Upper (D 7) (R 7) [6,33,24,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30311 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30311 : Upper (D 7) (R 7) [6,33,24,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192,257] 13 (by decide) (choices 1) [2,64] r30311 c30311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12078
  · exact u12079

def r30312 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30312 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30312 : Upper (D 7) (R 7) [6,33,24,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192,258] 13 (by decide) (choices 1) [1,64] r30312 c30312
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12080
  · exact u12081

def r30313 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c30313 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30313 : Upper (D 7) (R 7) [6,33,24,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192,288] 13 (by decide) (choices 1) [1,2,64] r30313 c30313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12082
  · exact u12083
  · exact u12084

def r30314 : Route 9 := (fun mask => (mask,id))

def c30314 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30314 : Upper (D 7) (R 7) [6,33,24,192,320] 13 := by
  apply FastRouting.sound _ _ [6,33,24,192,320] 13 (by decide) (choices 1) [1,2,128] r30314 c30314
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12085
  · exact u12086
  · exact u12087

def b30315 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 69 26 56 480 448 448 448), lower := (rows 7 35 69 26 56 32 64 128 256), losses := [] }

theorem u30315 : Upper (D 7) (R 7) [6,33,65,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30316 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 7 35 69 26 88 416 480 416 416), lower := (rows 7 35 69 26 88 32 64 128 256), losses := [] }

theorem u30316 : Upper (D 7) (R 7) [6,33,65,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30317 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 69 26 112 424 456 392 392), lower := (rows 7 35 69 26 112 32 64 128 256), losses := [] }

theorem u30317 : Upper (D 7) (R 7) [6,33,65,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30318 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 484, targets := 2 },{ cop := 3, region := 496, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 35 69 26 152 480 480 480 480), lower := (rows 7 35 69 26 152 32 64 128 256), losses := [] }

theorem u30318 : Upper (D 7) (R 7) [6,33,65,18,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30319 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 26 176 488 456 456 456), lower := (rows 7 35 69 26 176 32 64 128 256), losses := [] }

theorem u30319 : Upper (D 7) (R 7) [6,33,65,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30320 : Route 9 := (fun mask => (mask,id))

def c30320 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30320 : Upper (D 7) (R 7) [6,33,65,18,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,192] 13 (by decide) (choices 1) [8,128,256] r30320 c30320
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12088
  · exact u12089
  · exact u12090

def b30321 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 0, region := 228, targets := 2 },{ cop := 3, region := 496, targets := 2 }], pairs := [(2,1),(3,0),(4,0),(4,1)], upper := (rows 7 35 69 26 280 224 224 224 480), lower := (rows 7 35 69 26 280 32 64 128 256), losses := [] }

theorem u30321 : Upper (D 7) (R 7) [6,33,65,18,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30322 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 26 304 232 200 200 456), lower := (rows 7 35 69 26 304 32 64 128 256), losses := [] }

theorem u30322 : Upper (D 7) (R 7) [6,33,65,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30323 : Route 9 := (fun mask => (mask,id))

def c30323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30323 : Upper (D 7) (R 7) [6,33,65,18,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,320] 13 (by decide) (choices 1) [8,128] r30323 c30323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12091
  · exact u12092

def r30324 : Route 9 := (fun mask => (mask,id))

def c30324 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30324 : Upper (D 7) (R 7) [6,33,65,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,18,384] 13 (by decide) (choices 1) [8,64,128] r30324 c30324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12093
  · exact u12094
  · exact u12095

def b30325 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 88 432 464 400 400), lower := (rows 7 35 69 42 88 32 64 128 256), losses := [] }

theorem u30325 : Upper (D 7) (R 7) [6,33,65,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30326 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 152 496 464 464 464), lower := (rows 7 35 69 42 152 32 64 128 256), losses := [] }

theorem u30326 : Upper (D 7) (R 7) [6,33,65,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30327 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 208 440 472 408 408), lower := (rows 7 35 69 42 208 32 64 128 256), losses := [] }

theorem u30327 : Upper (D 7) (R 7) [6,33,65,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30328 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 280 240 208 208 464), lower := (rows 7 35 69 42 280 32 64 128 256), losses := [] }

theorem u30328 : Upper (D 7) (R 7) [6,33,65,34,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30329 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 336 184 216 152 408), lower := (rows 7 35 69 42 336 32 64 128 256), losses := [] }

theorem u30329 : Upper (D 7) (R 7) [6,33,65,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30330 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 469, targets := 32 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 69 42 400 248 216 216 472), lower := (rows 7 35 69 42 400 32 64 128 256), losses := [] }

theorem u30330 : Upper (D 7) (R 7) [6,33,65,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30330 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30331 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 56 82 424 456 392 392), lower := (rows 7 35 69 56 82 32 64 128 256), losses := [] }

theorem u30331 : Upper (D 7) (R 7) [6,33,65,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30332 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 56 88 418 450 386 386), lower := (rows 7 35 69 56 88 32 64 128 256), losses := [] }

theorem u30332 : Upper (D 7) (R 7) [6,33,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30333 : Route 9 := (fun mask => (mask,id))

def c30333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u30333 : Upper (D 7) (R 7) [6,33,65,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,130] 13 (by decide) (choices 1) [8,64,128,256] r30333 c30333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12096
  · exact u12097
  · exact u12098
  · exact u12099

def b30334 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 56 152 482 450 450 450), lower := (rows 7 35 69 56 152 32 64 128 256), losses := [] }

theorem u30334 : Upper (D 7) (R 7) [6,33,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30335 : Route 9 := (fun mask => (mask,id))

def c30335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30335 : Upper (D 7) (R 7) [6,33,65,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192] 13 (by decide) (choices 1) [2,8,128,256] r30335 c30335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12100
  · exact u12101
  · exact u12102
  · exact u12103

def r30336 : Route 9 := (fun mask => (mask,id))

def c30336 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30336 : Upper (D 7) (R 7) [6,33,65,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,258] 13 (by decide) (choices 1) [8,64,128] r30336 c30336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12104
  · exact u12105
  · exact u12106

def b30337 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 56 280 226 194 194 450), lower := (rows 7 35 69 56 280 32 64 128 256), losses := [] }

theorem u30337 : Upper (D 7) (R 7) [6,33,65,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30338 : Route 9 := (fun mask => (mask,id))

def c30338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30338 : Upper (D 7) (R 7) [6,33,65,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,320] 13 (by decide) (choices 1) [2,8,128] r30338 c30338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12107
  · exact u12108
  · exact u12109

def r30339 : Route 9 := (fun mask => (mask,id))

def c30339 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30339 : Upper (D 7) (R 7) [6,33,65,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,384] 13 (by decide) (choices 1) [2,8,64,128] r30339 c30339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12110
  · exact u12111
  · exact u12112
  · exact u12113

def b30340 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 74 152 432 496 432 432), lower := (rows 7 35 69 74 152 32 64 128 256), losses := [] }

theorem u30340 : Upper (D 7) (R 7) [6,33,65,66,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30341 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 74 176 440 472 408 408), lower := (rows 7 35 69 74 176 32 64 128 256), losses := [] }

theorem u30341 : Upper (D 7) (R 7) [6,33,65,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30341 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30342 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 74 280 176 240 176 432), lower := (rows 7 35 69 74 280 32 64 128 256), losses := [] }

theorem u30342 : Upper (D 7) (R 7) [6,33,65,66,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30342 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30343 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 74 304 184 216 152 408), lower := (rows 7 35 69 74 304 32 64 128 256), losses := [] }

theorem u30343 : Upper (D 7) (R 7) [6,33,65,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30344 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 69 74 400 184 248 184 440), lower := (rows 7 35 69 74 400 32 64 128 256), losses := [] }

theorem u30344 : Upper (D 7) (R 7) [6,33,65,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30345 : Route 9 := (fun mask => (mask,id))

def c30345 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30345 : Upper (D 7) (R 7) [6,33,65,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,130] 13 (by decide) (choices 1) [8,128,256] r30345 c30345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12114
  · exact u12115
  · exact u12116

def b30346 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 7 35 69 88 152 418 482 418 418), lower := (rows 7 35 69 88 152 32 64 128 256), losses := [] }

theorem u30346 : Upper (D 7) (R 7) [6,33,65,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30347 : Route 9 := (fun mask => (mask,id))

def c30347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30347 : Upper (D 7) (R 7) [6,33,65,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,160] 13 (by decide) (choices 1) [2,8,128,256] r30347 c30347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12117
  · exact u12118
  · exact u12119
  · exact u12120

def r30348 : Route 9 := (fun mask => (mask,id))

def c30348 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30348 : Upper (D 7) (R 7) [6,33,65,80,258] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,258] 13 (by decide) (choices 1) [8,128] r30348 c30348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12121
  · exact u12122

def b30349 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(3,0),(4,0)], upper := (rows 7 35 69 88 280 162 226 162 418), lower := (rows 7 35 69 88 280 32 64 128 256), losses := [] }

theorem u30349 : Upper (D 7) (R 7) [6,33,65,80,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30349 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30350 : Route 9 := (fun mask => (mask,id))

def c30350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30350 : Upper (D 7) (R 7) [6,33,65,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,288] 13 (by decide) (choices 1) [2,8,128] r30350 c30350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12123
  · exact u12124
  · exact u12125

def r30351 : Route 9 := (fun mask => (mask,id))

def c30351 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30351 : Upper (D 7) (R 7) [6,33,65,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,80,384] 13 (by decide) (choices 1) [2,8,128] r30351 c30351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12126
  · exact u12127
  · exact u12128

def b30352 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 104 146 440 472 408 408), lower := (rows 7 35 69 104 146 32 64 128 256), losses := [] }

theorem u30352 : Upper (D 7) (R 7) [6,33,65,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30353 : PairBound 9 := { available := 402, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 104 152 434 466 402 402), lower := (rows 7 35 69 104 152 32 64 128 256), losses := [] }

theorem u30353 : Upper (D 7) (R 7) [6,33,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30354 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 104 274 184 216 152 408), lower := (rows 7 35 69 104 274 32 64 128 256), losses := [] }

theorem u30354 : Upper (D 7) (R 7) [6,33,65,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30355 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 104 280 178 210 146 402), lower := (rows 7 35 69 104 280 32 64 128 256), losses := [] }

theorem u30355 : Upper (D 7) (R 7) [6,33,65,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30356 : PairBound 9 := { available := 154, camps := [{ cop := 3, region := 7, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 104 400 186 218 154 410), lower := (rows 7 35 69 104 400 32 64 128 256), losses := [] }

theorem u30356 : Upper (D 7) (R 7) [6,33,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30357 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 359, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 35 69 138 152 368 368 496 368), lower := (rows 7 35 69 138 152 32 64 128 256), losses := [] }

theorem u30357 : Upper (D 7) (R 7) [6,33,65,130,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30358 : Route 9 := (fun mask => (mask,id))

def c30358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u30358 : Upper (D 7) (R 7) [6,33,65,130,160] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,160] 13 (by decide) (choices 1) [8,16,64,256] r30358 c30358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12129
  · exact u12130
  · exact u12131
  · exact u12132

def r30359 : Route 9 := (fun mask => (mask,id))

def c30359 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30359 : Upper (D 7) (R 7) [6,33,65,130,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,192] 13 (by decide) (choices 1) [8,16,256] r30359 c30359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12133
  · exact u12134
  · exact u12135

#print axioms u30359
end Delivery.IrregularNine14.P07
