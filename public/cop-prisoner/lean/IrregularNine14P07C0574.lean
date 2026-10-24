import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0318
import IrregularNine14P07C0319

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r34440 : Route 9 := (fun mask => (mask,id))

def c34440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34440 : Upper (D 7) (R 7) [34,68,40,272,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272,130] 13 (by decide) (choices 1) [1,64,128] r34440 c34440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19115
  · exact u19116
  · exact u19117

def r34441 : Route 9 := (fun mask => (mask,id))

def c34441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34441 : Upper (D 7) (R 7) [34,68,40,272,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,272,192] 13 (by decide) (choices 1) [1,2,128] r34441 c34441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19118
  · exact u19119
  · exact u19120

def b34442 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 16, targets := 192 }], pairs := [(3,5),(4,5),(4,6),(4,7)], upper := (rows 35 70 44 392 19 241 209 209 465), lower := (rows 35 70 44 392 19 32 64 128 256), losses := [] }

theorem u34442 : Upper (D 7) (R 7) [34,68,40,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34443 : Route 9 := (fun mask => (mask,id))

def c34443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34443 : Upper (D 7) (R 7) [34,68,40,384,65] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,65] 13 (by decide) (choices 1) [1,2,16,128] r34443 c34443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19121
  · exact u19122
  · exact u19123
  · exact u19124

def b34444 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 44 392 82 177 209 145 401), lower := (rows 35 70 44 392 82 32 64 128 256), losses := [] }

theorem u34444 : Upper (D 7) (R 7) [34,68,40,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34445 : Route 9 := (fun mask => (mask,id))

def c34445 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34445 : Upper (D 7) (R 7) [34,68,40,384,129] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,129] 13 (by decide) (choices 1) [1,2,16,64] r34445 c34445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19125
  · exact u19126
  · exact u19127
  · exact u19128

def r34446 : Route 9 := (fun mask => (mask,id))

def c34446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34446 : Upper (D 7) (R 7) [34,68,40,384,130] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,130] 13 (by decide) (choices 1) [1,16,64] r34446 c34446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19129
  · exact u19130
  · exact u19131

def r34447 : Route 9 := (fun mask => (mask,id))

def c34447 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34447 : Upper (D 7) (R 7) [34,68,40,384,192] 13 := by
  apply FastRouting.sound _ _ [34,68,40,384,192] 13 (by decide) (choices 1) [1,2,16] r34447 c34447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19132
  · exact u19133
  · exact u19134

def b34448 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 133 11 56 496 464 464 464), lower := (rows 35 70 133 11 56 32 64 128 256), losses := [] }

theorem u34448 : Upper (D 7) (R 7) [34,68,129,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34449 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 88 432 496 432 432), lower := (rows 35 70 133 11 88 32 64 128 256), losses := [] }

theorem u34449 : Upper (D 7) (R 7) [34,68,129,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34450 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 112 440 472 408 408), lower := (rows 35 70 133 11 112 32 64 128 256), losses := [] }

theorem u34450 : Upper (D 7) (R 7) [34,68,129,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34451 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 152 368 368 496 368), lower := (rows 35 70 133 11 152 32 64 128 256), losses := [] }

theorem u34451 : Upper (D 7) (R 7) [34,68,129,3,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34452 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 176 376 344 472 344), lower := (rows 35 70 133 11 176 32 64 128 256), losses := [] }

theorem u34452 : Upper (D 7) (R 7) [34,68,129,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34453 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 208 312 376 440 312), lower := (rows 35 70 133 11 208 32 64 128 256), losses := [] }

theorem u34453 : Upper (D 7) (R 7) [34,68,129,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34454 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 280 240 240 240 496), lower := (rows 35 70 133 11 280 32 64 128 256), losses := [] }

theorem u34454 : Upper (D 7) (R 7) [34,68,129,3,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34455 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 304 248 216 216 472), lower := (rows 35 70 133 11 304 32 64 128 256), losses := [] }

theorem u34455 : Upper (D 7) (R 7) [34,68,129,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34456 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 336 184 248 184 440), lower := (rows 35 70 133 11 336 32 64 128 256), losses := [] }

theorem u34456 : Upper (D 7) (R 7) [34,68,129,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34457 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 8, targets := 224 },{ cop := 3, region := 500, targets := 2 }], pairs := [(2,1),(3,5),(3,6),(3,7)], upper := (rows 35 70 133 11 400 120 120 248 376), lower := (rows 35 70 133 11 400 32 64 128 256), losses := [] }

theorem u34457 : Upper (D 7) (R 7) [34,68,129,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34458 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 224 }], pairs := [(3,5),(3,6),(3,7),(4,5)], upper := (rows 35 70 133 25 26 480 480 480 480), lower := (rows 35 70 133 25 26 32 64 128 256), losses := [] }

theorem u34458 : Upper (D 7) (R 7) [34,68,129,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34459 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 133 25 50 488 456 456 456), lower := (rows 35 70 133 25 50 32 64 128 256), losses := [] }

theorem u34459 : Upper (D 7) (R 7) [34,68,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34460 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 35 70 133 25 56 482 450 450 450), lower := (rows 35 70 133 25 56 32 64 128 256), losses := [] }

theorem u34460 : Upper (D 7) (R 7) [34,68,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34460 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34461 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 425, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 133 25 82 424 488 424 424), lower := (rows 35 70 133 25 82 32 64 128 256), losses := [] }

theorem u34461 : Upper (D 7) (R 7) [34,68,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34462 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 2, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 35 70 133 25 88 418 482 418 418), lower := (rows 35 70 133 25 88 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 39 71 135 263), good := (rows 482 486 486 504 88 32 64 128 256) }] }

theorem u34462 : Upper (D 7) (R 7) [34,68,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34463 : Route 9 := (fun mask => (mask,id))

def c34463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34463 : Upper (D 7) (R 7) [34,68,129,17,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,96] 13 (by decide) (choices 1) [2,8,128,256] r34463 c34463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19135
  · exact u19136
  · exact u19137
  · exact u19138

def r34464 : Route 9 := (fun mask => (mask,id))

def c34464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34464 : Upper (D 7) (R 7) [34,68,129,17,130] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,130] 13 (by decide) (choices 1) [8,64,256] r34464 c34464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19139
  · exact u19140
  · exact u19141

def b34465 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 24, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 35 70 133 25 152 354 354 482 354), lower := (rows 35 70 133 25 152 32 64 128 256), losses := [] }

theorem u34465 : Upper (D 7) (R 7) [34,68,129,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34466 : Route 9 := (fun mask => (mask,id))

def c34466 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34466 : Upper (D 7) (R 7) [34,68,129,17,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,160] 13 (by decide) (choices 1) [2,8,64,256] r34466 c34466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19142
  · exact u19143
  · exact u19144
  · exact u19145

def r34467 : Route 9 := (fun mask => (mask,id))

def c34467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34467 : Upper (D 7) (R 7) [34,68,129,17,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,192] 13 (by decide) (choices 1) [2,8,256] r34467 c34467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19146
  · exact u19147
  · exact u19148

def r34468 : Route 9 := (fun mask => (mask,id))

def c34468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34468 : Upper (D 7) (R 7) [34,68,129,17,258] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,258] 13 (by decide) (choices 1) [8,64,128] r34468 c34468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19149
  · exact u19150
  · exact u19151

def r34469 : Route 9 := (fun mask => (mask,id))

def c34469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34469 : Upper (D 7) (R 7) [34,68,129,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,264] 13 (by decide) (choices 1) [2,64,128] r34469 c34469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19152
  · exact u19153
  · exact u19154

def r34470 : Route 9 := (fun mask => (mask,id))

def c34470 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34470 : Upper (D 7) (R 7) [34,68,129,17,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,288] 13 (by decide) (choices 1) [2,8,64,128] r34470 c34470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19155
  · exact u19156
  · exact u19157
  · exact u19158

def r34471 : Route 9 := (fun mask => (mask,id))

def c34471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34471 : Upper (D 7) (R 7) [34,68,129,17,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,320] 13 (by decide) (choices 1) [2,8,128] r34471 c34471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19159
  · exact u19160
  · exact u19161

def r34472 : Route 9 := (fun mask => (mask,id))

def c34472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34472 : Upper (D 7) (R 7) [34,68,129,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384] 13 (by decide) (choices 1) [2,8,64] r34472 c34472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19162
  · exact u19163
  · exact u19164

def b34473 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 133 26 49 488 456 456 456), lower := (rows 35 70 133 26 49 32 64 128 256), losses := [] }

theorem u34473 : Upper (D 7) (R 7) [34,68,129,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34474 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 35 70 133 26 56 481 449 449 449), lower := (rows 35 70 133 26 56 32 64 128 256), losses := [] }

theorem u34474 : Upper (D 7) (R 7) [34,68,129,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34475 : Route 9 := (fun mask => (mask,id))

def c34475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34475 : Upper (D 7) (R 7) [34,68,129,18,65] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,65] 13 (by decide) (choices 1) [8,128,256] r34475 c34475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19165
  · exact u19166
  · exact u19167

def b34476 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 161 }], pairs := [(3,0),(3,5),(3,7),(4,0)], upper := (rows 35 70 133 26 88 417 481 417 417), lower := (rows 35 70 133 26 88 32 64 128 256), losses := [] }

theorem u34476 : Upper (D 7) (R 7) [34,68,129,18,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34476 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34477 : Route 9 := (fun mask => (mask,id))

def c34477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u34477 : Upper (D 7) (R 7) [34,68,129,18,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,96] 13 (by decide) (choices 1) [1,8,128,256] r34477 c34477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19168
  · exact u19169
  · exact u19170
  · exact u19171

def b34478 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 16, targets := 98 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5),(4,6)], upper := (rows 35 70 133 26 145 360 360 488 360), lower := (rows 35 70 133 26 145 32 64 128 256), losses := [] }

theorem u34478 : Upper (D 7) (R 7) [34,68,129,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r34479 : Route 9 := (fun mask => (mask,id))

def c34479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34479 : Upper (D 7) (R 7) [34,68,129,18,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,136] 13 (by decide) (choices 1) [1,64,256] r34479 c34479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19172
  · exact u19173
  · exact u19174

def r34480 : Route 9 := (fun mask => (mask,id))

def c34480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | _ => 0)

theorem u34480 : Upper (D 7) (R 7) [34,68,129,18,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,160] 13 (by decide) (choices 1) [1,8,64,256] r34480 c34480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19175
  · exact u19176
  · exact u19177
  · exact u19178

def r34481 : Route 9 := (fun mask => (mask,id))

def c34481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u34481 : Upper (D 7) (R 7) [34,68,129,18,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,192] 13 (by decide) (choices 1) [1,8,256] r34481 c34481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19179
  · exact u19180
  · exact u19181

def r34482 : Route 9 := (fun mask => (mask,id))

def c34482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34482 : Upper (D 7) (R 7) [34,68,129,18,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,257] 13 (by decide) (choices 1) [8,64,128] r34482 c34482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19182
  · exact u19183
  · exact u19184

def r34483 : Route 9 := (fun mask => (mask,id))

def c34483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34483 : Upper (D 7) (R 7) [34,68,129,18,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,264] 13 (by decide) (choices 1) [1,64,128] r34483 c34483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19185
  · exact u19186
  · exact u19187

def r34484 : Route 9 := (fun mask => (mask,id))

def c34484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u34484 : Upper (D 7) (R 7) [34,68,129,18,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,288] 13 (by decide) (choices 1) [1,8,64,128] r34484 c34484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u19188
  · exact u19189
  · exact u19190
  · exact u19191

def r34485 : Route 9 := (fun mask => (mask,id))

def c34485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u34485 : Upper (D 7) (R 7) [34,68,129,18,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,320] 13 (by decide) (choices 1) [1,8,128] r34485 c34485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19192
  · exact u19193
  · exact u19194

def r34486 : Route 9 := (fun mask => (mask,id))

def c34486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u34486 : Upper (D 7) (R 7) [34,68,129,18,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,18,384] 13 (by decide) (choices 1) [1,8,64] r34486 c34486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u19195
  · exact u19196
  · exact u19197

def b34487 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 88 434 466 402 402), lower := (rows 35 70 133 41 88 32 64 128 256), losses := [] }

theorem u34487 : Upper (D 7) (R 7) [34,68,129,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34487 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34488 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 146 376 344 472 344), lower := (rows 35 70 133 41 146 32 64 128 256), losses := [] }

theorem u34488 : Upper (D 7) (R 7) [34,68,129,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34489 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 152 370 338 466 338), lower := (rows 35 70 133 41 152 32 64 128 256), losses := [] }

theorem u34489 : Upper (D 7) (R 7) [34,68,129,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34489 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34490 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 208 314 346 410 282), lower := (rows 35 70 133 41 208 32 64 128 256), losses := [] }

theorem u34490 : Upper (D 7) (R 7) [34,68,129,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34490 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34491 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 274 248 216 216 472), lower := (rows 35 70 133 41 274 32 64 128 256), losses := [] }

theorem u34491 : Upper (D 7) (R 7) [34,68,129,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34492 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 280 242 210 210 466), lower := (rows 35 70 133 41 280 32 64 128 256), losses := [] }

theorem u34492 : Upper (D 7) (R 7) [34,68,129,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34493 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 336 186 218 154 410), lower := (rows 35 70 133 41 336 32 64 128 256), losses := [] }

theorem u34493 : Upper (D 7) (R 7) [34,68,129,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34494 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 8, targets := 194 },{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(3,7)], upper := (rows 35 70 133 41 400 122 90 218 346), lower := (rows 35 70 133 41 400 32 64 128 256), losses := [] }

theorem u34494 : Upper (D 7) (R 7) [34,68,129,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34494 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34495 : PairBound 9 := { available := 408, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 81 440 472 408 408), lower := (rows 35 70 133 42 81 32 64 128 256), losses := [] }

theorem u34495 : Upper (D 7) (R 7) [34,68,129,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34496 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 88 433 465 401 401), lower := (rows 35 70 133 42 88 32 64 128 256), losses := [] }

theorem u34496 : Upper (D 7) (R 7) [34,68,129,34,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34496 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34497 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 152 369 337 465 337), lower := (rows 35 70 133 42 152 32 64 128 256), losses := [] }

theorem u34497 : Upper (D 7) (R 7) [34,68,129,34,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34497 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34498 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 208 313 345 409 281), lower := (rows 35 70 133 42 208 32 64 128 256), losses := [] }

theorem u34498 : Upper (D 7) (R 7) [34,68,129,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34498 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34499 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 8, targets := 192 },{ cop := 3, region := 1, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 70 133 42 273 248 216 216 472), lower := (rows 35 70 133 42 273 32 64 128 256), losses := [] }

theorem u34499 : Upper (D 7) (R 7) [34,68,129,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34499 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u34499
end Delivery.IrregularNine14.P07
