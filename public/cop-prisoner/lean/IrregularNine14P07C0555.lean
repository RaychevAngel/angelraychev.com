import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0286
import IrregularNine14P07C0287
import IrregularNine14P07C0288

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r33300 : Route 9 := (fun mask => (mask,id))

def c33300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33300 : Upper (D 7) (R 7) [12,96,130,384,3] 13 := by
  apply FastRouting.sound _ _ [12,96,130,384,3] 13 (by decide) (choices 1) [1,16,64] r33300 c33300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17173
  · exact u17174
  · exact u17175

def r33301 : Route 9 := (fun mask => (mask,id))

def c33301 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33301 : Upper (D 7) (R 7) [12,96,130,384,33] 13 := by
  apply FastRouting.sound _ _ [12,96,130,384,33] 13 (by decide) (choices 1) [1,2,16,64] r33301 c33301
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17176
  · exact u17177
  · exact u17178
  · exact u17179

def b33302 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 134 392 50 113 81 209 337), lower := (rows 13 98 134 392 50 32 64 128 256), losses := [] }

theorem u33302 : Upper (D 7) (R 7) [12,96,130,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33303 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 13 98 134 392 112 51 83 147 275), lower := (rows 13 98 134 392 112 32 64 128 256), losses := [] }

theorem u33303 : Upper (D 7) (R 7) [12,96,130,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33304 : Route 9 := (fun mask => (mask,id))

def c33304 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u33304 : Upper (D 7) (R 7) [12,96,144,160,3] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,3] 13 (by decide) (choices 1) [1,2,64,256] r33304 c33304
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17180
  · exact u17181
  · exact u17182
  · exact u17183

def r33305 : Route 9 := (fun mask => (mask,id))

def c33305 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u33305 : Upper (D 7) (R 7) [12,96,144,160,65] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,65] 13 (by decide) (choices 1) [1,2,256] r33305 c33305
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17184
  · exact u17185
  · exact u17186

def b33306 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 148 168 82 291 323 387 259), lower := (rows 13 98 148 168 82 32 64 128 256), losses := [] }

theorem u33306 : Upper (D 7) (R 7) [12,96,144,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33307 : Route 9 := (fun mask => (mask,id))

def c33307 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33307 : Upper (D 7) (R 7) [12,96,144,160,257] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,257] 13 (by decide) (choices 1) [1,2,64] r33307 c33307
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17187
  · exact u17188
  · exact u17189

def r33308 : Route 9 := (fun mask => (mask,id))

def c33308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33308 : Upper (D 7) (R 7) [12,96,144,160,258] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,258] 13 (by decide) (choices 1) [1,2,64] r33308 c33308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17190
  · exact u17191
  · exact u17192

def r33309 : Route 9 := (fun mask => (mask,id))

def c33309 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33309 : Upper (D 7) (R 7) [12,96,144,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160,320] 13 (by decide) (choices 1) [1,2] r33309 c33309
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17193
  · exact u17194

def r33310 : Route 9 := (fun mask => (mask,id))

def c33310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33310 : Upper (D 7) (R 7) [12,96,144,257,3] 13 := by
  apply FastRouting.sound _ _ [12,96,144,257,3] 13 (by decide) (choices 1) [2,64,128] r33310 c33310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17195
  · exact u17196
  · exact u17197

def r33311 : Route 9 := (fun mask => (mask,id))

def c33311 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33311 : Upper (D 7) (R 7) [12,96,144,257,33] 13 := by
  apply FastRouting.sound _ _ [12,96,144,257,33] 13 (by decide) (choices 1) [2,64,128] r33311 c33311
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17198
  · exact u17199
  · exact u17200

def b33312 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 148 265 50 227 195 195 451), lower := (rows 13 98 148 265 50 32 64 128 256), losses := [] }

theorem u33312 : Upper (D 7) (R 7) [12,96,144,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33312 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33313 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 148 265 112 163 195 131 387), lower := (rows 13 98 148 265 112 32 64 128 256), losses := [] }

theorem u33313 : Upper (D 7) (R 7) [12,96,144,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33313 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33314 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 363, targets := 128 },{ cop := 4, region := 4, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 13 98 148 265 145 98 98 226 354), lower := (rows 13 98 148 265 145 32 64 128 256), losses := [] }

theorem u33314 : Upper (D 7) (R 7) [12,96,144,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33315 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 265 146 99 99 227 355), lower := (rows 13 98 148 265 146 32 64 128 256), losses := [] }

theorem u33315 : Upper (D 7) (R 7) [12,96,144,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33316 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 265 176 99 67 195 323), lower := (rows 13 98 148 265 176 32 64 128 256), losses := [] }

theorem u33316 : Upper (D 7) (R 7) [12,96,144,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33316 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33317 : Route 9 := (fun mask => (mask,id))

def c33317 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33317 : Upper (D 7) (R 7) [12,96,144,258,3] 13 := by
  apply FastRouting.sound _ _ [12,96,144,258,3] 13 (by decide) (choices 1) [1,64,128] r33317 c33317
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17201
  · exact u17202
  · exact u17203

def r33318 : Route 9 := (fun mask => (mask,id))

def c33318 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33318 : Upper (D 7) (R 7) [12,96,144,258,33] 13 := by
  apply FastRouting.sound _ _ [12,96,144,258,33] 13 (by decide) (choices 1) [1,2,64,128] r33318 c33318
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17204
  · exact u17205
  · exact u17206
  · exact u17207

def b33319 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 148 266 50 225 193 193 449), lower := (rows 13 98 148 266 50 32 64 128 256), losses := [] }

theorem u33319 : Upper (D 7) (R 7) [12,96,144,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33319 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33320 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 129 },{ cop := 4, region := 2, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 98 148 266 112 163 195 131 387), lower := (rows 13 98 148 266 112 32 64 128 256), losses := [] }

theorem u33320 : Upper (D 7) (R 7) [12,96,144,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33321 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 266 145 99 99 227 355), lower := (rows 13 98 148 266 145 32 64 128 256), losses := [] }

theorem u33321 : Upper (D 7) (R 7) [12,96,144,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33322 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 266 146 97 97 225 353), lower := (rows 13 98 148 266 146 32 64 128 256), losses := [] }

theorem u33322 : Upper (D 7) (R 7) [12,96,144,258,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33322 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33323 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 266 176 99 67 195 323), lower := (rows 13 98 148 266 176 32 64 128 256), losses := [] }

theorem u33323 : Upper (D 7) (R 7) [12,96,144,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33324 : Route 9 := (fun mask => (mask,id))

def c33324 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33324 : Upper (D 7) (R 7) [12,96,144,288,3] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,3] 13 (by decide) (choices 1) [1,2,64,128] r33324 c33324
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17208
  · exact u17209
  · exact u17210
  · exact u17211

def r33325 : Route 9 := (fun mask => (mask,id))

def c33325 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33325 : Upper (D 7) (R 7) [12,96,144,288,65] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288,65] 13 (by decide) (choices 1) [1,2,128] r33325 c33325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17212
  · exact u17213
  · exact u17214

def b33326 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 148 296 82 163 195 131 387), lower := (rows 13 98 148 296 82 32 64 128 256), losses := [] }

theorem u33326 : Upper (D 7) (R 7) [12,96,144,288,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33327 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 296 145 99 67 195 323), lower := (rows 13 98 148 296 145 32 64 128 256), losses := [] }

theorem u33327 : Upper (D 7) (R 7) [12,96,144,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33328 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 296 146 99 67 195 323), lower := (rows 13 98 148 296 146 32 64 128 256), losses := [] }

theorem u33328 : Upper (D 7) (R 7) [12,96,144,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33329 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 4, targets := 99 }], pairs := [(2,0),(2,1),(2,5),(2,6)], upper := (rows 13 98 148 296 208 35 67 131 259), lower := (rows 13 98 148 296 208 32 64 128 256), losses := [] }

theorem u33329 : Upper (D 7) (R 7) [12,96,144,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33330 : Route 9 := (fun mask => (mask,id))

def c33330 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33330 : Upper (D 7) (R 7) [12,96,144,384,3] 13 := by
  apply FastRouting.sound _ _ [12,96,144,384,3] 13 (by decide) (choices 1) [1,2,64] r33330 c33330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17215
  · exact u17216
  · exact u17217

def r33331 : Route 9 := (fun mask => (mask,id))

def c33331 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33331 : Upper (D 7) (R 7) [12,96,144,384,33] 13 := by
  apply FastRouting.sound _ _ [12,96,144,384,33] 13 (by decide) (choices 1) [1,2,64] r33331 c33331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17218
  · exact u17219
  · exact u17220

def b33332 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 16, targets := 193 },{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 13 98 148 392 50 99 67 195 323), lower := (rows 13 98 148 392 50 32 64 128 256), losses := [] }

theorem u33332 : Upper (D 7) (R 7) [12,96,144,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33333 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 16, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 13 98 148 392 112 35 67 131 259), lower := (rows 13 98 148 392 112 32 64 128 256), losses := [] }

theorem u33333 : Upper (D 7) (R 7) [12,96,144,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33334 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 456, targets := 32 },{ cop := 4, region := 420, targets := 64 }], pairs := [(1,7),(2,6),(3,5),(4,7)], upper := (rows 13 98 164 200 19 307 339 403 275), lower := (rows 13 98 164 200 19 32 64 128 256), losses := [] }

theorem u33334 : Upper (D 7) (R 7) [12,96,160,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33335 : Route 9 := (fun mask => (mask,id))

def c33335 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33335 : Upper (D 7) (R 7) [12,96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [12,96,160,192,257] 13 (by decide) (choices 1) [1,2,16] r33335 c33335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17221
  · exact u17222
  · exact u17223

def r33336 : Route 9 := (fun mask => (mask,id))

def c33336 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33336 : Upper (D 7) (R 7) [12,96,160,192,258] 13 := by
  apply FastRouting.sound _ _ [12,96,160,192,258] 13 (by decide) (choices 1) [1,2,16] r33336 c33336
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17224
  · exact u17225
  · exact u17226

def r33337 : Route 9 := (fun mask => (mask,id))

def c33337 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33337 : Upper (D 7) (R 7) [12,96,160,257,3] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,3] 13 (by decide) (choices 1) [2,16,64,128] r33337 c33337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17227
  · exact u17228
  · exact u17229
  · exact u17230

def r33338 : Route 9 := (fun mask => (mask,id))

def c33338 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33338 : Upper (D 7) (R 7) [12,96,160,257,65] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,65] 13 (by decide) (choices 1) [2,16,128] r33338 c33338
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17231
  · exact u17232
  · exact u17233

def b33339 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 164 265 82 179 211 147 403), lower := (rows 13 98 164 265 82 32 64 128 256), losses := [] }

theorem u33339 : Upper (D 7) (R 7) [12,96,160,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33340 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 102, targets := 1 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 164 265 145 114 82 210 338), lower := (rows 13 98 164 265 145 32 64 128 256), losses := [] }

theorem u33340 : Upper (D 7) (R 7) [12,96,160,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33340 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33341 : Route 9 := (fun mask => (mask,id))

def c33341 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33341 : Upper (D 7) (R 7) [12,96,160,257,130] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,130] 13 (by decide) (choices 1) [1,2,16,64] r33341 c33341
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17234
  · exact u17235
  · exact u17236
  · exact u17237

def r33342 : Route 9 := (fun mask => (mask,id))

def c33342 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33342 : Upper (D 7) (R 7) [12,96,160,257,192] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257,192] 13 (by decide) (choices 1) [1,2,16] r33342 c33342
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17238
  · exact u17239
  · exact u17240

def r33343 : Route 9 := (fun mask => (mask,id))

def c33343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u33343 : Upper (D 7) (R 7) [12,96,160,258,3] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,3] 13 (by decide) (choices 1) [1,16,64,128] r33343 c33343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17241
  · exact u17242
  · exact u17243
  · exact u17244

def r33344 : Route 9 := (fun mask => (mask,id))

def c33344 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33344 : Upper (D 7) (R 7) [12,96,160,258,65] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,65] 13 (by decide) (choices 1) [1,2,16,128] r33344 c33344
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17245
  · exact u17246
  · exact u17247
  · exact u17248

def b33345 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 164 266 82 177 209 145 401), lower := (rows 13 98 164 266 82 32 64 128 256), losses := [] }

theorem u33345 : Upper (D 7) (R 7) [12,96,160,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33345 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33346 : Route 9 := (fun mask => (mask,id))

def c33346 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33346 : Upper (D 7) (R 7) [12,96,160,258,129] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,129] 13 (by decide) (choices 1) [1,2,16,64] r33346 c33346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17249
  · exact u17250
  · exact u17251
  · exact u17252

def r33347 : Route 9 := (fun mask => (mask,id))

def c33347 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33347 : Upper (D 7) (R 7) [12,96,160,258,130] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,130] 13 (by decide) (choices 1) [1,16,64] r33347 c33347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17253
  · exact u17254
  · exact u17255

def r33348 : Route 9 := (fun mask => (mask,id))

def c33348 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33348 : Upper (D 7) (R 7) [12,96,160,258,192] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258,192] 13 (by decide) (choices 1) [1,2,16] r33348 c33348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17256
  · exact u17257
  · exact u17258

def r33349 : Route 9 := (fun mask => (mask,id))

def c33349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u33349 : Upper (D 7) (R 7) [12,96,160,272,3] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,3] 13 (by decide) (choices 1) [1,2,64,128] r33349 c33349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17259
  · exact u17260
  · exact u17261
  · exact u17262

def r33350 : Route 9 := (fun mask => (mask,id))

def c33350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33350 : Upper (D 7) (R 7) [12,96,160,272,65] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,65] 13 (by decide) (choices 1) [1,2,128] r33350 c33350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17263
  · exact u17264
  · exact u17265

def b33351 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 429, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 13 98 164 280 82 163 195 131 387), lower := (rows 13 98 164 280 82 32 64 128 256), losses := [] }

theorem u33351 : Upper (D 7) (R 7) [12,96,160,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r33352 : Route 9 := (fun mask => (mask,id))

def c33352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33352 : Upper (D 7) (R 7) [12,96,160,272,129] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,129] 13 (by decide) (choices 1) [1,2,64] r33352 c33352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17266
  · exact u17267
  · exact u17268

def r33353 : Route 9 := (fun mask => (mask,id))

def c33353 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33353 : Upper (D 7) (R 7) [12,96,160,272,130] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,130] 13 (by decide) (choices 1) [1,2,64] r33353 c33353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17269
  · exact u17270
  · exact u17271

def r33354 : Route 9 := (fun mask => (mask,id))

def c33354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33354 : Upper (D 7) (R 7) [12,96,160,272,192] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272,192] 13 (by decide) (choices 1) [1,2] r33354 c33354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17272
  · exact u17273

def r33355 : Route 9 := (fun mask => (mask,id))

def c33355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u33355 : Upper (D 7) (R 7) [12,96,160,320,3] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,3] 13 (by decide) (choices 1) [1,2,16,128] r33355 c33355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17274
  · exact u17275
  · exact u17276
  · exact u17277

def r33356 : Route 9 := (fun mask => (mask,id))

def c33356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33356 : Upper (D 7) (R 7) [12,96,160,320,129] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,129] 13 (by decide) (choices 1) [1,2,16] r33356 c33356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17278
  · exact u17279
  · exact u17280

def r33357 : Route 9 := (fun mask => (mask,id))

def c33357 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33357 : Upper (D 7) (R 7) [12,96,160,320,130] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320,130] 13 (by decide) (choices 1) [1,2,16] r33357 c33357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17281
  · exact u17282
  · exact u17283

def r33358 : Route 9 := (fun mask => (mask,id))

def c33358 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33358 : Upper (D 7) (R 7) [12,96,160,384,3] 13 := by
  apply FastRouting.sound _ _ [12,96,160,384,3] 13 (by decide) (choices 1) [1,2,16,64] r33358 c33358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u17284
  · exact u17285
  · exact u17286
  · exact u17287

def r33359 : Route 9 := (fun mask => (mask,id))

def c33359 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33359 : Upper (D 7) (R 7) [12,96,160,384,65] 13 := by
  apply FastRouting.sound _ _ [12,96,160,384,65] 13 (by decide) (choices 1) [1,2,16] r33359 c33359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u17288
  · exact u17289
  · exact u17290

#print axioms u33359
end Delivery.IrregularNine14.P07
