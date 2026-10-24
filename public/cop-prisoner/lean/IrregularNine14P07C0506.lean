import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0202
import IrregularNine14P07C0203
import IrregularNine14P07C0204

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r30360 : Route 9 := (fun mask => (mask,id))

def c30360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30360 : Upper (D 7) (R 7) [6,33,65,130,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,264] 13 (by decide) (choices 1) [16,64,128] r30360 c30360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12136
  · exact u12137
  · exact u12138

def r30361 : Route 9 := (fun mask => (mask,id))

def c30361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u30361 : Upper (D 7) (R 7) [6,33,65,130,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,288] 13 (by decide) (choices 1) [8,16,64,128] r30361 c30361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12139
  · exact u12140
  · exact u12141
  · exact u12142

def r30362 : Route 9 := (fun mask => (mask,id))

def c30362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30362 : Upper (D 7) (R 7) [6,33,65,130,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,320] 13 (by decide) (choices 1) [8,16,128] r30362 c30362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12143
  · exact u12144
  · exact u12145

def r30363 : Route 9 := (fun mask => (mask,id))

def c30363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30363 : Upper (D 7) (R 7) [6,33,65,130,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,130,384] 13 (by decide) (choices 1) [8,16,64] r30363 c30363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12146
  · exact u12147
  · exact u12148

def b30364 : PairBound 9 := { available := 354, camps := [{ cop := 7, region := 24, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 69 152 152 354 354 482 354), lower := (rows 7 35 69 152 152 32 64 128 256), losses := [] }

theorem u30364 : Upper (D 7) (R 7) [6,33,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30365 : PairBound 9 := { available := 330, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 69 152 176 362 330 458 330), lower := (rows 7 35 69 152 176 32 64 128 256), losses := [] }

theorem u30365 : Upper (D 7) (R 7) [6,33,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30366 : PairBound 9 := { available := 298, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 69 152 208 298 362 426 298), lower := (rows 7 35 69 152 208 32 64 128 256), losses := [] }

theorem u30366 : Upper (D 7) (R 7) [6,33,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30367 : Route 9 := (fun mask => (mask,id))

def c30367 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30367 : Upper (D 7) (R 7) [6,33,65,144,258] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,258] 13 (by decide) (choices 1) [8,64,128] r30367 c30367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12149
  · exact u12150
  · exact u12151

def r30368 : Route 9 := (fun mask => (mask,id))

def c30368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30368 : Upper (D 7) (R 7) [6,33,65,144,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,264] 13 (by decide) (choices 1) [2,64,128] r30368 c30368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12152
  · exact u12153
  · exact u12154

def r30369 : Route 9 := (fun mask => (mask,id))

def c30369 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30369 : Upper (D 7) (R 7) [6,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288] 13 (by decide) (choices 1) [2,8,64,128] r30369 c30369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12155
  · exact u12156
  · exact u12157
  · exact u12158

def r30370 : Route 9 := (fun mask => (mask,id))

def c30370 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30370 : Upper (D 7) (R 7) [6,33,65,144,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,320] 13 (by decide) (choices 1) [2,8,128] r30370 c30370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12159
  · exact u12160
  · exact u12161

def b30371 : PairBound 9 := { available := 106, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 7 35 69 152 400 106 106 234 362), lower := (rows 7 35 69 152 400 32 64 128 256), losses := [] }

theorem u30371 : Upper (D 7) (R 7) [6,33,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30372 : Route 9 := (fun mask => (mask,id))

def c30372 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30372 : Upper (D 7) (R 7) [6,33,65,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,192] 13 (by decide) (choices 1) [2,8,16,256] r30372 c30372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12162
  · exact u12163
  · exact u12164
  · exact u12165

def r30373 : Route 9 := (fun mask => (mask,id))

def c30373 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u30373 : Upper (D 7) (R 7) [6,33,65,160,258] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,258] 13 (by decide) (choices 1) [8,16,64,128] r30373 c30373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12166
  · exact u12167
  · exact u12168
  · exact u12169

def r30374 : Route 9 := (fun mask => (mask,id))

def c30374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30374 : Upper (D 7) (R 7) [6,33,65,160,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,264] 13 (by decide) (choices 1) [2,16,64,128] r30374 c30374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12170
  · exact u12171
  · exact u12172
  · exact u12173

def r30375 : Route 9 := (fun mask => (mask,id))

def c30375 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30375 : Upper (D 7) (R 7) [6,33,65,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,320] 13 (by decide) (choices 1) [2,8,16,128] r30375 c30375
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12174
  · exact u12175
  · exact u12176
  · exact u12177

def r30376 : Route 9 := (fun mask => (mask,id))

def c30376 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30376 : Upper (D 7) (R 7) [6,33,65,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,384] 13 (by decide) (choices 1) [2,8,16,64] r30376 c30376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12178
  · exact u12179
  · exact u12180
  · exact u12181

def r30377 : Route 9 := (fun mask => (mask,id))

def c30377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30377 : Upper (D 7) (R 7) [6,33,65,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,258] 13 (by decide) (choices 1) [8,16,128] r30377 c30377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12182
  · exact u12183
  · exact u12184

def r30378 : Route 9 := (fun mask => (mask,id))

def c30378 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30378 : Upper (D 7) (R 7) [6,33,65,192,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,264] 13 (by decide) (choices 1) [2,16,128] r30378 c30378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12185
  · exact u12186
  · exact u12187

def r30379 : Route 9 := (fun mask => (mask,id))

def c30379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30379 : Upper (D 7) (R 7) [6,33,65,192,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,288] 13 (by decide) (choices 1) [2,8,16,128] r30379 c30379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12188
  · exact u12189
  · exact u12190
  · exact u12191

def r30380 : Route 9 := (fun mask => (mask,id))

def c30380 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u30380 : Upper (D 7) (R 7) [6,33,65,192,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,192,384] 13 (by decide) (choices 1) [2,8,16] r30380 c30380
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12192
  · exact u12193
  · exact u12194

def b30381 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 76 25 50 480 448 448 448), lower := (rows 7 35 76 25 50 32 64 128 256), losses := [] }

theorem u30381 : Upper (D 7) (R 7) [6,33,72,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30382 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 13, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 35 76 25 82 416 480 416 416), lower := (rows 7 35 76 25 82 32 64 128 256), losses := [] }

theorem u30382 : Upper (D 7) (R 7) [6,33,72,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30383 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 25 112 418 450 386 386), lower := (rows 7 35 76 25 112 32 64 128 256), losses := [] }

theorem u30383 : Upper (D 7) (R 7) [6,33,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30384 : Route 9 := (fun mask => (mask,id))

def c30384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30384 : Upper (D 7) (R 7) [6,33,72,17,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,130] 13 (by decide) (choices 1) [64,128,256] r30384 c30384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12195
  · exact u12196
  · exact u12197

def r30385 : Route 9 := (fun mask => (mask,id))

def c30385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30385 : Upper (D 7) (R 7) [6,33,72,17,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,160] 13 (by decide) (choices 1) [2,64,128,256] r30385 c30385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12198
  · exact u12199
  · exact u12200
  · exact u12201

def b30386 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 25 208 418 482 418 418), lower := (rows 7 35 76 25 208 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 92 508 208 32 64 128 256) }] }

theorem u30386 : Upper (D 7) (R 7) [6,33,72,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30387 : Route 9 := (fun mask => (mask,id))

def c30387 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30387 : Upper (D 7) (R 7) [6,33,72,17,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,258] 13 (by decide) (choices 1) [64,128] r30387 c30387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12202
  · exact u12203

def r30388 : Route 9 := (fun mask => (mask,id))

def c30388 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30388 : Upper (D 7) (R 7) [6,33,72,17,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,288] 13 (by decide) (choices 1) [2,64,128] r30388 c30388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12204
  · exact u12205
  · exact u12206

def b30389 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 76 25 336 162 226 162 418), lower := (rows 7 35 76 25 336 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 35 67 131 259), good := (rows 502 498 92 508 336 32 64 128 256) }] }

theorem u30389 : Upper (D 7) (R 7) [6,33,72,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30390 : Route 9 := (fun mask => (mask,id))

def c30390 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30390 : Upper (D 7) (R 7) [6,33,72,17,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,384] 13 (by decide) (choices 1) [2,64,128] r30390 c30390
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12207
  · exact u12208
  · exact u12209

def b30391 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 76 26 49 480 448 448 448), lower := (rows 7 35 76 26 49 32 64 128 256), losses := [] }

theorem u30391 : Upper (D 7) (R 7) [6,33,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30392 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 3, region := 484, targets := 3 }], pairs := [(0,6),(1,6),(2,0),(2,1)], upper := (rows 7 35 76 26 81 416 480 416 416), lower := (rows 7 35 76 26 81 32 64 128 256), losses := [] }

theorem u30392 : Upper (D 7) (R 7) [6,33,72,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30393 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 76 26 112 417 449 385 385), lower := (rows 7 35 76 26 112 32 64 128 256), losses := [] }

theorem u30393 : Upper (D 7) (R 7) [6,33,72,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30394 : Route 9 := (fun mask => (mask,id))

def c30394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30394 : Upper (D 7) (R 7) [6,33,72,18,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,129] 13 (by decide) (choices 1) [64,128,256] r30394 c30394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12210
  · exact u12211
  · exact u12212

def b30395 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 453, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 35 76 26 176 481 449 449 449), lower := (rows 7 35 76 26 176 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 92 508 176 32 64 128 256) }] }

theorem u30395 : Upper (D 7) (R 7) [6,33,72,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30396 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 76 26 208 417 481 417 417), lower := (rows 7 35 76 26 208 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 92 508 208 32 64 128 256) }] }

theorem u30396 : Upper (D 7) (R 7) [6,33,72,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30397 : Route 9 := (fun mask => (mask,id))

def c30397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30397 : Upper (D 7) (R 7) [6,33,72,18,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,257] 13 (by decide) (choices 1) [64,128] r30397 c30397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12213
  · exact u12214

def b30398 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 197, targets := 32 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 35 76 26 304 225 193 193 449), lower := (rows 7 35 76 26 304 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 92 508 304 32 64 128 256) }] }

theorem u30398 : Upper (D 7) (R 7) [6,33,72,18,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30399 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 496, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(4,1)], upper := (rows 7 35 76 26 336 161 225 161 417), lower := (rows 7 35 76 26 336 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 27 35 67 131 259), good := (rows 501 497 92 508 336 32 64 128 256) }] }

theorem u30399 : Upper (D 7) (R 7) [6,33,72,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30400 : Route 9 := (fun mask => (mask,id))

def c30400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30400 : Upper (D 7) (R 7) [6,33,72,18,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,384] 13 (by decide) (choices 1) [1,64,128] r30400 c30400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12215
  · exact u12216
  · exact u12217

def b30401 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7),(4,6),(4,7)], upper := (rows 7 35 76 56 19 480 448 448 448), lower := (rows 7 35 76 56 19 32 64 128 256), losses := [] }

theorem u30401 : Upper (D 7) (R 7) [6,33,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30402 : PairBound 9 := { available := 386, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 4, region := 426, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,5)], upper := (rows 7 35 76 56 81 418 450 386 386), lower := (rows 7 35 76 56 81 32 64 128 256), losses := [] }

theorem u30402 : Upper (D 7) (R 7) [6,33,72,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30403 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(1,6),(2,1),(4,5)], upper := (rows 7 35 76 56 82 417 449 385 385), lower := (rows 7 35 76 56 82 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 35 67 131 259), good := (rows 485 481 76 60 508 32 64 128 256) }] }

theorem u30403 : Upper (D 7) (R 7) [6,33,72,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30404 : Route 9 := (fun mask => (mask,id))

def c30404 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30404 : Upper (D 7) (R 7) [6,33,72,48,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,129] 13 (by decide) (choices 1) [2,64,128,256] r30404 c30404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12218
  · exact u12219
  · exact u12220
  · exact u12221

def r30405 : Route 9 := (fun mask => (mask,id))

def c30405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u30405 : Upper (D 7) (R 7) [6,33,72,48,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,130] 13 (by decide) (choices 1) [1,64,128,256] r30405 c30405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12222
  · exact u12223
  · exact u12224
  · exact u12225

def r30406 : Route 9 := (fun mask => (mask,id))

def c30406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u30406 : Upper (D 7) (R 7) [6,33,72,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,192] 13 (by decide) (choices 1) [1,2,128,256] r30406 c30406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12226
  · exact u12227
  · exact u12228
  · exact u12229

def r30407 : Route 9 := (fun mask => (mask,id))

def c30407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30407 : Upper (D 7) (R 7) [6,33,72,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,257] 13 (by decide) (choices 1) [2,64,128] r30407 c30407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12230
  · exact u12231
  · exact u12232

def r30408 : Route 9 := (fun mask => (mask,id))

def c30408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30408 : Upper (D 7) (R 7) [6,33,72,48,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,258] 13 (by decide) (choices 1) [1,64,128] r30408 c30408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12233
  · exact u12234
  · exact u12235

def r30409 : Route 9 := (fun mask => (mask,id))

def c30409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30409 : Upper (D 7) (R 7) [6,33,72,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,320] 13 (by decide) (choices 1) [1,2,128] r30409 c30409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12236
  · exact u12237
  · exact u12238

def r30410 : Route 9 := (fun mask => (mask,id))

def c30410 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u30410 : Upper (D 7) (R 7) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [1,2,64,128] r30410 c30410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12239
  · exact u12240
  · exact u12241
  · exact u12242

def b30411 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 461, targets := 32 },{ cop := 1, region := 16, targets := 64 }], pairs := [(0,5),(2,5),(3,5),(4,6)], upper := (rows 7 35 76 137 50 496 464 464 464), lower := (rows 7 35 76 137 50 32 64 128 256), losses := [] }

theorem u30411 : Upper (D 7) (R 7) [6,33,72,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r30412 : Route 9 := (fun mask => (mask,id))

def c30412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30412 : Upper (D 7) (R 7) [6,33,72,129,66] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,66] 13 (by decide) (choices 1) [16,128,256] r30412 c30412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12243
  · exact u12244
  · exact u12245

def r30413 : Route 9 := (fun mask => (mask,id))

def c30413 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u30413 : Upper (D 7) (R 7) [6,33,72,129,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,96] 13 (by decide) (choices 1) [2,16,128,256] r30413 c30413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12246
  · exact u12247
  · exact u12248
  · exact u12249

def r30414 : Route 9 := (fun mask => (mask,id))

def c30414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30414 : Upper (D 7) (R 7) [6,33,72,129,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,130] 13 (by decide) (choices 1) [16,64,256] r30414 c30414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12250
  · exact u12251
  · exact u12252

def r30415 : Route 9 := (fun mask => (mask,id))

def c30415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u30415 : Upper (D 7) (R 7) [6,33,72,129,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,160] 13 (by decide) (choices 1) [2,16,64,256] r30415 c30415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12253
  · exact u12254
  · exact u12255
  · exact u12256

def r30416 : Route 9 := (fun mask => (mask,id))

def c30416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u30416 : Upper (D 7) (R 7) [6,33,72,129,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,192] 13 (by decide) (choices 1) [2,16,256] r30416 c30416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12257
  · exact u12258
  · exact u12259

def r30417 : Route 9 := (fun mask => (mask,id))

def c30417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30417 : Upper (D 7) (R 7) [6,33,72,129,258] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,258] 13 (by decide) (choices 1) [16,64,128] r30417 c30417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12260
  · exact u12261
  · exact u12262

def r30418 : Route 9 := (fun mask => (mask,id))

def c30418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u30418 : Upper (D 7) (R 7) [6,33,72,129,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,288] 13 (by decide) (choices 1) [2,16,64,128] r30418 c30418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u12263
  · exact u12264
  · exact u12265
  · exact u12266

def r30419 : Route 9 := (fun mask => (mask,id))

def c30419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u30419 : Upper (D 7) (R 7) [6,33,72,129,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320] 13 (by decide) (choices 1) [2,16,128] r30419 c30419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u12267
  · exact u12268
  · exact u12269

#print axioms u30419
end Delivery.IrregularNine14.P07
