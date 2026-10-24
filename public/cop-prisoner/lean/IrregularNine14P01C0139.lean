import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0086
import IrregularNine14P01C0087

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8340 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 140 42 211 243 211 211 467), lower := (rows 277 98 140 42 16 32 64 128 256), losses := [] }

theorem u8340 : Upper (D 1) (R 1) [276,96,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8340
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8341 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 277 98 140 56 211 227 195 195 451), lower := (rows 277 98 140 56 16 32 64 128 256), losses := [] }

theorem u8341 : Upper (D 1) (R 1) [276,96,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8341
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8342 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 140 104 147 179 211 147 403), lower := (rows 277 98 140 104 16 32 64 128 256), losses := [] }

theorem u8342 : Upper (D 1) (R 1) [276,96,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8342
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8343 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 140 137 114 114 114 242 370), lower := (rows 277 98 140 137 16 32 64 128 256), losses := [] }

theorem u8343 : Upper (D 1) (R 1) [276,96,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8343
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8344 : PairBound 9 := { available := 115, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 140 138 115 115 115 243 371), lower := (rows 277 98 140 138 16 32 64 128 256), losses := [] }

theorem u8344 : Upper (D 1) (R 1) [276,96,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8344
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8345 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 140 152 115 99 99 227 355), lower := (rows 277 98 140 152 16 32 64 128 256), losses := [] }

theorem u8345 : Upper (D 1) (R 1) [276,96,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8345
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8346 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 277 98 140 168 83 115 83 211 339), lower := (rows 277 98 140 168 16 32 64 128 256), losses := [] }

theorem u8346 : Upper (D 1) (R 1) [276,96,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8346
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8347 : Route 9 := (fun mask => (mask,id))

def c8347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8347 : Upper (D 1) (R 1) [276,96,160,3] 13 := by
  apply FastRouting.sound _ _ [276,96,160,3] 13 (by decide) (choices 1) [2,8,64,128] r8347 c8347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5177
  · exact u5178
  · exact u5179
  · exact u5180

def b8348 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 277 98 164 25 218 234 202 202 458), lower := (rows 277 98 164 25 16 32 64 128 256), losses := [] }

theorem u8348 : Upper (D 1) (R 1) [276,96,160,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8348
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8349 : Route 9 := (fun mask => (mask,id))

def c8349 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8349 : Upper (D 1) (R 1) [276,96,160,18] 13 := by
  apply FastRouting.sound _ _ [276,96,160,18] 13 (by decide) (choices 1) [1,2,8,64,128] r8349 c8349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5181
  · exact u5182
  · exact u5183
  · exact u5184
  · exact u5185

def r8350 : Route 9 := (fun mask => (mask,id))

def c8350 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8350 : Upper (D 1) (R 1) [276,96,160,65] 13 := by
  apply FastRouting.sound _ _ [276,96,160,65] 13 (by decide) (choices 1) [2,8,128] r8350 c8350
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5186
  · exact u5187
  · exact u5188

def b8351 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 277 98 164 74 155 187 219 155 411), lower := (rows 277 98 164 74 16 32 64 128 256), losses := [] }

theorem u8351 : Upper (D 1) (R 1) [276,96,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8351
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8352 : Route 9 := (fun mask => (mask,id))

def c8352 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8352 : Upper (D 1) (R 1) [276,96,160,80] 13 := by
  apply FastRouting.sound _ _ [276,96,160,80] 13 (by decide) (choices 1) [1,2,8,128] r8352 c8352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5189
  · exact u5190
  · exact u5191
  · exact u5192

def b8353 : PairBound 9 := { available := 90, camps := [{ cop := 3, region := 114, targets := 128 }], pairs := [(1,7)], upper := (rows 277 98 164 137 90 122 90 218 346), lower := (rows 277 98 164 137 16 32 64 128 256), losses := [] }

theorem u8353 : Upper (D 1) (R 1) [276,96,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8353
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8354 : Route 9 := (fun mask => (mask,id))

def c8354 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8354 : Upper (D 1) (R 1) [276,96,160,130] 13 := by
  apply FastRouting.sound _ _ [276,96,160,130] 13 (by decide) (choices 1) [1,2,8,64] r8354 c8354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5193
  · exact u5194
  · exact u5195
  · exact u5196

def r8355 : Route 9 := (fun mask => (mask,id))

def c8355 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8355 : Upper (D 1) (R 1) [276,96,160,144] 13 := by
  apply FastRouting.sound _ _ [276,96,160,144] 13 (by decide) (choices 1) [1,2,8,64] r8355 c8355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5197
  · exact u5198
  · exact u5199
  · exact u5200

def r8356 : Route 9 := (fun mask => (mask,id))

def c8356 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8356 : Upper (D 1) (R 1) [276,96,160,192] 13 := by
  apply FastRouting.sound _ _ [276,96,160,192] 13 (by decide) (choices 1) [1,2,8] r8356 c8356
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5201
  · exact u5202
  · exact u5203

def b8357 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 26 240 224 224 224 480), lower := (rows 305 7 14 26 16 32 64 128 256), losses := [] }

theorem u8357 : Upper (D 1) (R 1) [304,5,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8357
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8358 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 14 56 210 226 194 194 450), lower := (rows 305 7 14 56 16 32 64 128 256), losses := [] }

theorem u8358 : Upper (D 1) (R 1) [304,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8358
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8359 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 7 14 74 240 240 240 240 496), lower := (rows 305 7 14 74 16 32 64 128 256), losses := [] }

theorem u8359 : Upper (D 1) (R 1) [304,5,10,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8359
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8360 : Route 9 := (fun mask => (mask,id))

def c8360 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8360 : Upper (D 1) (R 1) [304,5,10,80] 13 := by
  apply FastRouting.sound _ _ [304,5,10,80] 13 (by decide) (choices 1) [2,32,64,128] r8360 c8360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5204
  · exact u5205
  · exact u5206
  · exact u5207

def r8361 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8361 : Upper (D 1) (R 1) [304,5,10,192] 13 := by
  apply FastRouting.sound _ _ [304,5,10,192] 13 (by decide) (choices 1) [2,32,64] r8361 c8361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5208
  · exact u5209
  · exact u5210

def b8362 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 481, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 26 248 232 232 232 488), lower := (rows 305 7 70 26 16 32 64 128 256), losses := [] }

theorem u8362 : Upper (D 1) (R 1) [304,5,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8362
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8363 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 70 56 218 234 202 202 458), lower := (rows 305 7 70 56 16 32 64 128 256), losses := [] }

theorem u8363 : Upper (D 1) (R 1) [304,5,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8363
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8364 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 70 74 184 184 248 184 440), lower := (rows 305 7 70 74 16 32 64 128 256), losses := [] }

theorem u8364 : Upper (D 1) (R 1) [304,5,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8364
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8365 : Route 9 := (fun mask => (mask,id))

def c8365 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8365 : Upper (D 1) (R 1) [304,5,66,80] 13 := by
  apply FastRouting.sound _ _ [304,5,66,80] 13 (by decide) (choices 1) [2,8,32,128] r8365 c8365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5211
  · exact u5212
  · exact u5213
  · exact u5214

def b8366 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 369, targets := 2 }], pairs := [(0,1)], upper := (rows 305 7 70 138 248 248 248 248 504), lower := (rows 305 7 70 138 16 32 64 128 256), losses := [] }

theorem u8366 : Upper (D 1) (R 1) [304,5,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8366
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8367 : Route 9 := (fun mask => (mask,id))

def c8367 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u8367 : Upper (D 1) (R 1) [304,5,66,144] 13 := by
  apply FastRouting.sound _ _ [304,5,66,144] 13 (by decide) (choices 1) [2,8,32,64,128] r8367 c8367
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u5215
  · exact u5216
  · exact u5217
  · exact u5218
  · exact u5219

def r8368 : Route 9 := (fun mask => (mask,id))

def c8368 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8368 : Upper (D 1) (R 1) [304,5,66,192] 13 := by
  apply FastRouting.sound _ _ [304,5,66,192] 13 (by decide) (choices 1) [2,8,32,128] r8368 c8368
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5220
  · exact u5221
  · exact u5222
  · exact u5223

def b8369 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 305 7 76 26 242 226 226 226 482), lower := (rows 305 7 76 26 16 32 64 128 256), losses := [] }

theorem u8369 : Upper (D 1) (R 1) [304,5,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8369
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8370 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 76 56 210 226 194 194 450), lower := (rows 305 7 76 56 16 32 64 128 256), losses := [] }

theorem u8370 : Upper (D 1) (R 1) [304,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8370
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8371 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 76 74 178 178 242 178 434), lower := (rows 305 7 76 74 16 32 64 128 256), losses := [] }

theorem u8371 : Upper (D 1) (R 1) [304,5,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8371
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8372 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 76 88 178 162 226 162 418), lower := (rows 305 7 76 88 16 32 64 128 256), losses := [] }

theorem u8372 : Upper (D 1) (R 1) [304,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8372
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8373 : Route 9 := (fun mask => (mask,id))

def c8373 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8373 : Upper (D 1) (R 1) [304,5,72,130] 13 := by
  apply FastRouting.sound _ _ [304,5,72,130] 13 (by decide) (choices 1) [2,32,64,128] r8373 c8373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5224
  · exact u5225
  · exact u5226
  · exact u5227

def r8374 : Route 9 := (fun mask => (mask,id))

def c8374 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8374 : Upper (D 1) (R 1) [304,5,72,144] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144] 13 (by decide) (choices 1) [2,32,64,128] r8374 c8374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5228
  · exact u5229
  · exact u5230
  · exact u5231

def b8375 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 7 76 200 178 178 242 178 434), lower := (rows 305 7 76 200 16 32 64 128 256), losses := [] }

theorem u8375 : Upper (D 1) (R 1) [304,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8375
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8376 : PairBound 9 := { available := 234, camps := [{ cop := 3, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 305 7 196 26 250 234 234 234 490), lower := (rows 305 7 196 26 16 32 64 128 256), losses := [] }

theorem u8376 : Upper (D 1) (R 1) [304,5,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8376
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8377 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 196 56 218 234 202 202 458), lower := (rows 305 7 196 56 16 32 64 128 256), losses := [] }

theorem u8377 : Upper (D 1) (R 1) [304,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8377
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8378 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 196 74 186 186 250 186 442), lower := (rows 305 7 196 74 16 32 64 128 256), losses := [] }

theorem u8378 : Upper (D 1) (R 1) [304,5,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8378
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8379 : Route 9 := (fun mask => (mask,id))

def c8379 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8379 : Upper (D 1) (R 1) [304,5,192,80] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80] 13 (by decide) (choices 1) [2,8,32,128] r8379 c8379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5232
  · exact u5233
  · exact u5234
  · exact u5235

def b8380 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 305 7 196 200 58 58 122 186 314), lower := (rows 305 7 196 200 16 32 64 128 256), losses := [] }

theorem u8380 : Upper (D 1) (R 1) [304,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8380
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8381 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 7 26 240 224 224 224 480), lower := (rows 305 14 7 26 16 32 64 128 256), losses := [] }

theorem u8381 : Upper (D 1) (R 1) [304,12,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8381
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8382 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 14 7 56 210 226 194 194 450), lower := (rows 305 14 7 56 16 32 64 128 256), losses := [] }

theorem u8382 : Upper (D 1) (R 1) [304,12,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8382
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8383 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 7 74 240 240 240 240 496), lower := (rows 305 14 7 74 16 32 64 128 256), losses := [] }

theorem u8383 : Upper (D 1) (R 1) [304,12,3,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8383
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8384 : Route 9 := (fun mask => (mask,id))

def c8384 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8384 : Upper (D 1) (R 1) [304,12,3,80] 13 := by
  apply FastRouting.sound _ _ [304,12,3,80] 13 (by decide) (choices 1) [2,32,64,128] r8384 c8384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5236
  · exact u5237
  · exact u5238
  · exact u5239

def r8385 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8385 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8385 : Upper (D 1) (R 1) [304,12,3,192] 13 := by
  apply FastRouting.sound _ _ [304,12,3,192] 13 (by decide) (choices 1) [2,32,64] r8385 c8385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5240
  · exact u5241
  · exact u5242

def b8386 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 14 21 42 210 226 194 194 450), lower := (rows 305 14 21 42 16 32 64 128 256), losses := [] }

theorem u8386 : Upper (D 1) (R 1) [304,12,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8386
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8387 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 21 74 242 226 226 226 482), lower := (rows 305 14 21 74 16 32 64 128 256), losses := [] }

theorem u8387 : Upper (D 1) (R 1) [304,12,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8387
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8388 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 21 104 210 226 194 194 450), lower := (rows 305 14 21 104 16 32 64 128 256), losses := [] }

theorem u8388 : Upper (D 1) (R 1) [304,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8388
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8389 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 21 200 242 226 226 226 482), lower := (rows 305 14 21 200 16 32 64 128 256), losses := [] }

theorem u8389 : Upper (D 1) (R 1) [304,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8389
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8390 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 14 22 42 209 225 193 193 449), lower := (rows 305 14 22 42 16 32 64 128 256), losses := [] }

theorem u8390 : Upper (D 1) (R 1) [304,12,18,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8390
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8391 : Route 9 := (fun mask => (mask,id))

def c8391 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8391 : Upper (D 1) (R 1) [304,12,18,65] 13 := by
  apply FastRouting.sound _ _ [304,12,18,65] 13 (by decide) (choices 1) [2,32,64,128] r8391 c8391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5243
  · exact u5244
  · exact u5245
  · exact u5246

def b8392 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 497, targets := 2 }], pairs := [(0,1)], upper := (rows 305 14 22 74 241 225 225 225 481), lower := (rows 305 14 22 74 16 32 64 128 256), losses := [] }

theorem u8392 : Upper (D 1) (R 1) [304,12,18,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8392
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8393 : Route 9 := (fun mask => (mask,id))

def c8393 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8393 : Upper (D 1) (R 1) [304,12,18,96] 13 := by
  apply FastRouting.sound _ _ [304,12,18,96] 13 (by decide) (choices 1) [1,2,64,128] r8393 c8393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5247
  · exact u5248
  · exact u5249
  · exact u5250

def r8394 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8394 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8394 : Upper (D 1) (R 1) [304,12,18,192] 13 := by
  apply FastRouting.sound _ _ [304,12,18,192] 13 (by decide) (choices 1) [1,2,32,64] r8394 c8394
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5251
  · exact u5252
  · exact u5253
  · exact u5254

def b8395 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 52 73 210 226 194 194 450), lower := (rows 305 14 52 73 16 32 64 128 256), losses := [] }

theorem u8395 : Upper (D 1) (R 1) [304,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8395
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8396 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 52 74 211 227 195 195 451), lower := (rows 305 14 52 74 16 32 64 128 256), losses := [] }

theorem u8396 : Upper (D 1) (R 1) [304,12,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8396
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8397 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 52 200 211 227 195 195 451), lower := (rows 305 14 52 200 16 32 64 128 256), losses := [] }

theorem u8397 : Upper (D 1) (R 1) [304,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8397
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8398 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 10, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 69 74 178 178 242 178 434), lower := (rows 305 14 69 74 16 32 64 128 256), losses := [] }

theorem u8398 : Upper (D 1) (R 1) [304,12,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8398
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8399 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 14 69 88 178 162 226 162 418), lower := (rows 305 14 69 88 16 32 64 128 256), losses := [] }

theorem u8399 : Upper (D 1) (R 1) [304,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8399
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u8399
end Delivery.IrregularNine14.P01
