import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0402
import IrregularNine14P06C0403

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38340 : Route 9 := (fun mask => (mask,id))

def c38340 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38340 : Upper (D 6) (R 6) [34,136,257,65,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,68] 13 (by decide) (choices 1) [2,4,16] r38340 c38340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24141
  · exact u24142
  · exact u24143

def r38341 : Route 9 := (fun mask => (mask,id))

def c38341 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38341 : Upper (D 6) (R 6) [34,136,257,65,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,65,96] 13 (by decide) (choices 1) [2,4,16] r38341 c38341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24144
  · exact u24145
  · exact u24146

def b38342 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 16, targets := 32 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 35 138 261 74 21 116 116 244 372), lower := (rows 35 138 261 74 21 32 64 128 256), losses := [] }

theorem u38342 : Upper (D 6) (R 6) [34,136,257,66,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38343 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 261 74 49 116 84 212 340), lower := (rows 35 138 261 74 49 32 64 128 256), losses := [] }

theorem u38343 : Upper (D 6) (R 6) [34,136,257,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38343 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38344 : Route 9 := (fun mask => (mask,id))

def c38344 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38344 : Upper (D 6) (R 6) [34,136,257,66,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66,36] 13 (by decide) (choices 1) [1,4,16,64] r38344 c38344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24147
  · exact u24148
  · exact u24149
  · exact u24150

def b38345 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 138 261 74 81 52 116 180 308), lower := (rows 35 138 261 74 81 32 64 128 256), losses := [] }

theorem u38345 : Upper (D 6) (R 6) [34,136,257,66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38345 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38346 : Route 9 := (fun mask => (mask,id))

def c38346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38346 : Upper (D 6) (R 6) [34,136,257,66,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66,68] 13 (by decide) (choices 1) [1,4,16] r38346 c38346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24151
  · exact u24152
  · exact u24153

def r38347 : Route 9 := (fun mask => (mask,id))

def c38347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38347 : Upper (D 6) (R 6) [34,136,257,66,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,66,96] 13 (by decide) (choices 1) [1,4,16] r38347 c38347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24154
  · exact u24155
  · exact u24156

def b38348 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 261 76 19 116 116 244 372), lower := (rows 35 138 261 76 19 32 64 128 256), losses := [] }

theorem u38348 : Upper (D 6) (R 6) [34,136,257,68,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38348 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38349 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 261 76 21 114 114 242 370), lower := (rows 35 138 261 76 21 32 64 128 256), losses := [] }

theorem u38349 : Upper (D 6) (R 6) [34,136,257,68,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38349 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38350 : Route 9 := (fun mask => (mask,id))

def c38350 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38350 : Upper (D 6) (R 6) [34,136,257,68,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,6] 13 (by decide) (choices 1) [1,16,64] r38350 c38350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24157
  · exact u24158
  · exact u24159

def b38351 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 261 76 49 118 86 214 342), lower := (rows 35 138 261 76 49 32 64 128 256), losses := [] }

theorem u38351 : Upper (D 6) (R 6) [34,136,257,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38351 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38352 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 261 76 50 117 85 213 341), lower := (rows 35 138 261 76 50 32 64 128 256), losses := [] }

theorem u38352 : Upper (D 6) (R 6) [34,136,257,68,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38352 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38353 : Route 9 := (fun mask => (mask,id))

def c38353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38353 : Upper (D 6) (R 6) [34,136,257,68,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,36] 13 (by decide) (choices 1) [1,2,16,64] r38353 c38353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24160
  · exact u24161
  · exact u24162
  · exact u24163

def r38354 : Route 9 := (fun mask => (mask,id))

def c38354 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38354 : Upper (D 6) (R 6) [34,136,257,68,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,65] 13 (by decide) (choices 1) [2,4,16] r38354 c38354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24164
  · exact u24165
  · exact u24166

def r38355 : Route 9 := (fun mask => (mask,id))

def c38355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38355 : Upper (D 6) (R 6) [34,136,257,68,66] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,66] 13 (by decide) (choices 1) [1,4,16] r38355 c38355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24167
  · exact u24168
  · exact u24169

def b38356 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 261 76 84 51 115 179 307), lower := (rows 35 138 261 76 84 32 64 128 256), losses := [] }

theorem u38356 : Upper (D 6) (R 6) [34,136,257,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38357 : Route 9 := (fun mask => (mask,id))

def c38357 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38357 : Upper (D 6) (R 6) [34,136,257,68,96] 13 := by
  apply FastRouting.sound _ _ [34,136,257,68,96] 13 (by decide) (choices 1) [1,2,4,16] r38357 c38357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24170
  · exact u24171
  · exact u24172
  · exact u24173

def b38358 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 261 88 19 100 100 228 356), lower := (rows 35 138 261 88 19 32 64 128 256), losses := [] }

theorem u38358 : Upper (D 6) (R 6) [34,136,257,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38358 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38359 : PairBound 9 := { available := 102, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 261 88 21 102 102 230 358), lower := (rows 35 138 261 88 21 32 64 128 256), losses := [] }

theorem u38359 : Upper (D 6) (R 6) [34,136,257,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38359 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38360 : Route 9 := (fun mask => (mask,id))

def c38360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38360 : Upper (D 6) (R 6) [34,136,257,80,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,80,6] 13 (by decide) (choices 1) [1,4,64] r38360 c38360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24174
  · exact u24175
  · exact u24176

def b38361 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 261 88 49 102 70 198 326), lower := (rows 35 138 261 88 49 32 64 128 256), losses := [] }

theorem u38361 : Upper (D 6) (R 6) [34,136,257,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38362 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 261 88 50 101 69 197 325), lower := (rows 35 138 261 88 50 32 64 128 256), losses := [] }

theorem u38362 : Upper (D 6) (R 6) [34,136,257,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38363 : Route 9 := (fun mask => (mask,id))

def c38363 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38363 : Upper (D 6) (R 6) [34,136,257,80,36] 13 := by
  apply FastRouting.sound _ _ [34,136,257,80,36] 13 (by decide) (choices 1) [1,2,4,64] r38363 c38363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24177
  · exact u24178
  · exact u24179
  · exact u24180

def b38364 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 261 88 81 38 102 166 294), lower := (rows 35 138 261 88 81 32 64 128 256), losses := [] }

theorem u38364 : Upper (D 6) (R 6) [34,136,257,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38365 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 261 88 82 37 101 165 293), lower := (rows 35 138 261 88 82 32 64 128 256), losses := [] }

theorem u38365 : Upper (D 6) (R 6) [34,136,257,80,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38366 : PairBound 9 := { available := 39, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 261 88 84 39 103 167 295), lower := (rows 35 138 261 88 84 32 64 128 256), losses := [] }

theorem u38366 : Upper (D 6) (R 6) [34,136,257,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38367 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 138 261 88 112 39 71 135 263), lower := (rows 35 138 261 88 112 32 64 128 256), losses := [] }

theorem u38367 : Upper (D 6) (R 6) [34,136,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38368 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 261 104 19 116 84 212 340), lower := (rows 35 138 261 104 19 32 64 128 256), losses := [] }

theorem u38368 : Upper (D 6) (R 6) [34,136,257,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38369 : PairBound 9 := { available := 86, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 35 138 261 104 21 118 86 214 342), lower := (rows 35 138 261 104 21 32 64 128 256), losses := [] }

theorem u38369 : Upper (D 6) (R 6) [34,136,257,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38370 : Route 9 := (fun mask => (mask,id))

def c38370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38370 : Upper (D 6) (R 6) [34,136,257,96,6] 13 := by
  apply FastRouting.sound _ _ [34,136,257,96,6] 13 (by decide) (choices 1) [1,4,16,64] r38370 c38370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24181
  · exact u24182
  · exact u24183
  · exact u24184

def r38371 : Route 9 := (fun mask => (mask,id))

def c38371 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38371 : Upper (D 6) (R 6) [34,136,257,96,65] 13 := by
  apply FastRouting.sound _ _ [34,136,257,96,65] 13 (by decide) (choices 1) [2,4,16] r38371 c38371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24185
  · exact u24186
  · exact u24187

def b38372 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 293, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 138 261 104 82 53 85 149 277), lower := (rows 35 138 261 104 82 32 64 128 256), losses := [] }

theorem u38372 : Upper (D 6) (R 6) [34,136,257,96,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38373 : Route 9 := (fun mask => (mask,id))

def c38373 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38373 : Upper (D 6) (R 6) [34,136,257,96,68] 13 := by
  apply FastRouting.sound _ _ [34,136,257,96,68] 13 (by decide) (choices 1) [1,2,4,16] r38373 c38373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24188
  · exact u24189
  · exact u24190
  · exact u24191

def b38374 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5),(4,5),(4,6)], upper := (rows 35 138 262 13 21 112 112 240 368), lower := (rows 35 138 262 13 21 32 64 128 256), losses := [] }

theorem u38374 : Upper (D 6) (R 6) [34,136,258,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38375 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 262 13 49 116 84 212 340), lower := (rows 35 138 262 13 49 32 64 128 256), losses := [] }

theorem u38375 : Upper (D 6) (R 6) [34,136,258,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38376 : Route 9 := (fun mask => (mask,id))

def c38376 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38376 : Upper (D 6) (R 6) [34,136,258,5,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,36] 13 (by decide) (choices 1) [1,16,64] r38376 c38376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24192
  · exact u24193
  · exact u24194

def r38377 : Route 9 := (fun mask => (mask,id))

def c38377 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38377 : Upper (D 6) (R 6) [34,136,258,5,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,65] 13 (by decide) (choices 1) [4,16,64] r38377 c38377
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24195
  · exact u24196
  · exact u24197

def r38378 : Route 9 := (fun mask => (mask,id))

def c38378 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38378 : Upper (D 6) (R 6) [34,136,258,5,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,68] 13 (by decide) (choices 1) [1,16,64] r38378 c38378
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24198
  · exact u24199
  · exact u24200

def r38379 : Route 9 := (fun mask => (mask,id))

def c38379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38379 : Upper (D 6) (R 6) [34,136,258,5,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,5,96] 13 (by decide) (choices 1) [1,4,16,64] r38379 c38379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24201
  · exact u24202
  · exact u24203
  · exact u24204

def b38380 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 262 25 21 100 100 228 356), lower := (rows 35 138 262 25 21 32 64 128 256), losses := [] }

theorem u38380 : Upper (D 6) (R 6) [34,136,258,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38381 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 262 25 49 100 68 196 324), lower := (rows 35 138 262 25 49 32 64 128 256), losses := [] }

theorem u38381 : Upper (D 6) (R 6) [34,136,258,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38382 : Route 9 := (fun mask => (mask,id))

def c38382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38382 : Upper (D 6) (R 6) [34,136,258,17,36] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17,36] 13 (by decide) (choices 1) [1,4,64] r38382 c38382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24205
  · exact u24206
  · exact u24207

def b38383 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 262 25 81 100 100 228 356), lower := (rows 35 138 262 25 81 32 64 128 256), losses := [] }

theorem u38383 : Upper (D 6) (R 6) [34,136,258,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38383 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38384 : Route 9 := (fun mask => (mask,id))

def c38384 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38384 : Upper (D 6) (R 6) [34,136,258,17,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17,68] 13 (by decide) (choices 1) [1,4,64] r38384 c38384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24208
  · exact u24209
  · exact u24210

def r38385 : Route 9 := (fun mask => (mask,id))

def c38385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38385 : Upper (D 6) (R 6) [34,136,258,17,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,17,96] 13 (by decide) (choices 1) [1,4,64] r38385 c38385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24211
  · exact u24212
  · exact u24213

def b38386 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 35 138 262 28 21 97 97 225 353), lower := (rows 35 138 262 28 21 32 64 128 256), losses := [] }

theorem u38386 : Upper (D 6) (R 6) [34,136,258,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38387 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 262 28 49 101 69 197 325), lower := (rows 35 138 262 28 49 32 64 128 256), losses := [] }

theorem u38387 : Upper (D 6) (R 6) [34,136,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38388 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 262 28 52 97 65 193 321), lower := (rows 35 138 262 28 52 32 64 128 256), losses := [] }

theorem u38388 : Upper (D 6) (R 6) [34,136,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38389 : Route 9 := (fun mask => (mask,id))

def c38389 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38389 : Upper (D 6) (R 6) [34,136,258,20,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,20,65] 13 (by decide) (choices 1) [1,4,64] r38389 c38389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24214
  · exact u24215
  · exact u24216

def b38390 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 262 28 84 97 97 225 353), lower := (rows 35 138 262 28 84 32 64 128 256), losses := [] }

theorem u38390 : Upper (D 6) (R 6) [34,136,258,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38391 : Route 9 := (fun mask => (mask,id))

def c38391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38391 : Upper (D 6) (R 6) [34,136,258,20,96] 13 := by
  apply FastRouting.sound _ _ [34,136,258,20,96] 13 (by decide) (choices 1) [1,4,64] r38391 c38391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24217
  · exact u24218
  · exact u24219

def b38392 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 262 44 21 113 81 209 337), lower := (rows 35 138 262 44 21 32 64 128 256), losses := [] }

theorem u38392 : Upper (D 6) (R 6) [34,136,258,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38393 : Route 9 := (fun mask => (mask,id))

def c38393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38393 : Upper (D 6) (R 6) [34,136,258,36,65] 13 := by
  apply FastRouting.sound _ _ [34,136,258,36,65] 13 (by decide) (choices 1) [1,4,16,64] r38393 c38393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24220
  · exact u24221
  · exact u24222
  · exact u24223

def r38394 : Route 9 := (fun mask => (mask,id))

def c38394 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38394 : Upper (D 6) (R 6) [34,136,258,36,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,36,68] 13 (by decide) (choices 1) [1,16,64] r38394 c38394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24224
  · exact u24225
  · exact u24226

def b38395 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 104, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 35 138 262 56 21 101 69 197 325), lower := (rows 35 138 262 56 21 32 64 128 256), losses := [] }

theorem u38395 : Upper (D 6) (R 6) [34,136,258,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38396 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 138 262 56 81 101 69 197 325), lower := (rows 35 138 262 56 81 32 64 128 256), losses := [{ target := 5, region := (rows 1 10 13 8 17 0 81 145 273), good := (rows 471 142 262 478 469 0 64 128 256) }] }

theorem u38396 : Upper (D 6) (R 6) [34,136,258,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38397 : Route 9 := (fun mask => (mask,id))

def c38397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38397 : Upper (D 6) (R 6) [34,136,258,48,68] 13 := by
  apply FastRouting.sound _ _ [34,136,258,48,68] 13 (by decide) (choices 1) [1,4,64] r38397 c38397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24227
  · exact u24228
  · exact u24229

def r38398 : Route 9 := (fun mask => (mask,id))

def c38398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38398 : Upper (D 6) (R 6) [34,136,258,65,5] 13 := by
  apply FastRouting.sound _ _ [34,136,258,65,5] 13 (by decide) (choices 1) [4,16,64] r38398 c38398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24230
  · exact u24231
  · exact u24232

def b38399 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 262 73 49 116 84 212 340), lower := (rows 35 138 262 73 49 32 64 128 256), losses := [] }

theorem u38399 : Upper (D 6) (R 6) [34,136,258,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38399
end Delivery.IrregularNine14.P06
