import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0005
import IrregularNine14P10C0006

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 26 196 200 304 289 353 417 289), lower := (rows 7 26 196 200 304 32 64 128 256), losses := [] }

theorem u1200 : Upper (D 10) (R 10) [6,24,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1200 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 229, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 26 196 265 304 224 224 224 480), lower := (rows 7 26 196 265 304 32 64 128 256), losses := [] }

theorem u1201 : Upper (D 10) (R 10) [6,24,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1201 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 229, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 26 196 265 336 160 224 160 416), lower := (rows 7 26 196 265 336 32 64 128 256), losses := [] }

theorem u1202 : Upper (D 10) (R 10) [6,24,192,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1202 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 18, targets := 192 }], pairs := [(1,6),(1,7)], upper := (rows 7 26 196 296 304 225 225 225 481), lower := (rows 7 26 196 296 304 32 64 128 256), losses := [] }

theorem u1203 : Upper (D 10) (R 10) [6,24,192,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1203 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 229, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 26 196 296 336 161 225 161 417), lower := (rows 7 26 196 296 336 32 64 128 256), losses := [] }

theorem u1204 : Upper (D 10) (R 10) [6,24,192,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1204 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 229, targets := 256 }], pairs := [(0,8),(2,8)], upper := (rows 7 26 196 328 400 33 97 161 289), lower := (rows 7 26 196 328 400 32 64 128 256), losses := [] }

theorem u1205 : Upper (D 10) (R 10) [6,24,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1205 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 56 208 480 448 448 448), lower := (rows 7 35 44 56 208 32 64 128 256), losses := [] }

theorem u1206 : Upper (D 10) (R 10) [6,33,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1206 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 88 176 480 448 448 448), lower := (rows 7 35 44 88 176 32 64 128 256), losses := [] }

theorem u1207 : Upper (D 10) (R 10) [6,33,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1207 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 88 400 480 480 480 480), lower := (rows 7 35 44 88 400 32 64 128 256), losses := [] }

theorem u1208 : Upper (D 10) (R 10) [6,33,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1208 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 104 208 432 464 400 400), lower := (rows 7 35 44 104 208 32 64 128 256), losses := [] }

theorem u1209 : Upper (D 10) (R 10) [6,33,40,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1209 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 7, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 104 400 496 464 464 464), lower := (rows 7 35 44 104 400 32 64 128 256), losses := [] }

theorem u1210 : Upper (D 10) (R 10) [6,33,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1210 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 200 112 432 464 400 400), lower := (rows 7 35 44 200 112 32 64 128 256), losses := [] }

theorem u1211 : Upper (D 10) (R 10) [6,33,40,192,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1211 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 200 304 496 464 464 464), lower := (rows 7 35 44 200 304 32 64 128 256), losses := [] }

theorem u1212 : Upper (D 10) (R 10) [6,33,40,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1212 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 44 200 336 432 496 432 432), lower := (rows 7 35 44 200 336 32 64 128 256), losses := [] }

theorem u1213 : Upper (D 10) (R 10) [6,33,40,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1213 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 56 112 416 448 384 384), lower := (rows 7 35 76 56 112 32 64 128 256), losses := [] }

theorem u1214 : Upper (D 10) (R 10) [6,33,72,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1214 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 35 76 56 176 480 448 448 448), lower := (rows 7 35 76 56 176 32 64 128 256), losses := [] }

theorem u1215 : Upper (D 10) (R 10) [6,33,72,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1215 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1216 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 56 208 416 480 416 416), lower := (rows 7 35 76 56 208 32 64 128 256), losses := [] }

theorem u1216 : Upper (D 10) (R 10) [6,33,72,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1216 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1217 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1217 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1217 : Upper (D 10) (R 10) [6,33,72,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,48,384] 13 (by decide) (choices 1) [64,128] r1217 c1217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u354
  · exact u355

def b1218 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 88 176 416 480 416 416), lower := (rows 7 35 76 88 176 32 64 128 256), losses := [] }

theorem u1218 : Upper (D 10) (R 10) [6,33,72,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1218 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 88 400 416 480 416 416), lower := (rows 7 35 76 88 400 32 64 128 256), losses := [] }

theorem u1219 : Upper (D 10) (R 10) [6,33,72,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1219 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 104 176 432 464 400 400), lower := (rows 7 35 76 104 176 32 64 128 256), losses := [] }

theorem u1220 : Upper (D 10) (R 10) [6,33,72,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1220 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 104 400 432 496 432 432), lower := (rows 7 35 76 104 400 32 64 128 256), losses := [] }

theorem u1221 : Upper (D 10) (R 10) [6,33,72,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1221 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 152 112 416 480 416 416), lower := (rows 7 35 76 152 112 32 64 128 256), losses := [] }

theorem u1222 : Upper (D 10) (R 10) [6,33,72,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1222 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 152 176 352 352 480 352), lower := (rows 7 35 76 152 176 32 64 128 256), losses := [] }

theorem u1223 : Upper (D 10) (R 10) [6,33,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1223 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 12, targets := 288 }], pairs := [(2,5),(2,8)], upper := (rows 7 35 76 152 208 288 352 416 288), lower := (rows 7 35 76 152 208 32 64 128 256), losses := [] }

theorem u1224 : Upper (D 10) (R 10) [6,33,72,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1224 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1225 : Route 9 := (fun mask => (mask,id))

def c1225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1225 : Upper (D 10) (R 10) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [64,128,256] r1225 c1225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u356
  · exact u357
  · exact u358

def b1226 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 152 336 416 480 416 416), lower := (rows 7 35 76 152 336 32 64 128 256), losses := [] }

theorem u1226 : Upper (D 10) (R 10) [6,33,72,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1226 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 152 400 352 352 480 352), lower := (rows 7 35 76 152 400 32 64 128 256), losses := [] }

theorem u1227 : Upper (D 10) (R 10) [6,33,72,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1227 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1228 : Route 9 := (fun mask => (mask,id))

def c1228 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1228 : Upper (D 10) (R 10) [6,33,72,160,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,96] 13 (by decide) (choices 1) [16,128,256] r1228 c1228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u359
  · exact u360
  · exact u361

def b1229 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 35 76 168 176 368 336 464 336), lower := (rows 7 35 76 168 176 32 64 128 256), losses := [] }

theorem u1229 : Upper (D 10) (R 10) [6,33,72,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1229 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1230 : Route 9 := (fun mask => (mask,id))

def c1230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1230 : Upper (D 10) (R 10) [6,33,72,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,192] 13 (by decide) (choices 1) [16,256] r1230 c1230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u362
  · exact u363

def r1231 : Route 9 := (fun mask => (mask,id))

def c1231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1231 : Upper (D 10) (R 10) [6,33,72,160,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,288] 13 (by decide) (choices 1) [16,64,128,256] r1231 c1231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u364
  · exact u365
  · exact u366
  · exact u367

def r1232 : Route 9 := (fun mask => (mask,id))

def c1232 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1232 : Upper (D 10) (R 10) [6,33,72,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,320] 13 (by decide) (choices 1) [16,128,256] r1232 c1232
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u368
  · exact u369
  · exact u370

def r1233 : Route 9 := (fun mask => (mask,id))

def c1233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1233 : Upper (D 10) (R 10) [6,33,72,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,160,384] 13 (by decide) (choices 1) [16,64,256] r1233 c1233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u371
  · exact u372
  · exact u373

def b1234 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 200 176 304 368 432 304), lower := (rows 7 35 76 200 176 32 64 128 256), losses := [] }

theorem u1234 : Upper (D 10) (R 10) [6,33,72,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1234 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 200 304 432 496 432 432), lower := (rows 7 35 76 200 304 32 64 128 256), losses := [] }

theorem u1235 : Upper (D 10) (R 10) [6,33,72,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1235 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 200 400 304 368 432 304), lower := (rows 7 35 76 200 400 32 64 128 256), losses := [] }

theorem u1236 : Upper (D 10) (R 10) [6,33,72,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1236 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1237 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1237 : Upper (D 10) (R 10) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [16,128] r1237 c1237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u374
  · exact u375

def r1238 : Route 9 := (fun mask => (mask,id))

def c1238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1238 : Upper (D 10) (R 10) [6,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,160] 13 (by decide) (choices 1) [16,64,256] r1238 c1238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u376
  · exact u377
  · exact u378

def r1239 : Route 9 := (fun mask => (mask,id))

def c1239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1239 : Upper (D 10) (R 10) [6,33,72,384,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192] 13 (by decide) (choices 1) [16,256] r1239 c1239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u379
  · exact u380

def b1240 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 35 76 392 400 112 112 240 368), lower := (rows 7 35 76 392 400 32 64 128 256), losses := [] }

theorem u1240 : Upper (D 10) (R 10) [6,33,72,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1240 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 100 56 88 416 448 384 384), lower := (rows 7 35 100 56 88 32 64 128 256), losses := [] }

theorem u1241 : Upper (D 10) (R 10) [6,33,96,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1241 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 56 152 480 448 448 448), lower := (rows 7 35 100 56 152 32 64 128 256), losses := [] }

theorem u1242 : Upper (D 10) (R 10) [6,33,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1242 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 56 208 424 456 392 392), lower := (rows 7 35 100 56 208 32 64 128 256), losses := [] }

theorem u1243 : Upper (D 10) (R 10) [6,33,96,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1243 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 56 400 488 456 456 456), lower := (rows 7 35 100 56 400 32 64 128 256), losses := [] }

theorem u1244 : Upper (D 10) (R 10) [6,33,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1244 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 100 88 152 416 480 416 416), lower := (rows 7 35 100 88 152 32 64 128 256), losses := [] }

theorem u1245 : Upper (D 10) (R 10) [6,33,96,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1245 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 88 176 424 456 392 392), lower := (rows 7 35 100 88 176 32 64 128 256), losses := [] }

theorem u1246 : Upper (D 10) (R 10) [6,33,96,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1246 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 88 400 424 488 424 424), lower := (rows 7 35 100 88 400 32 64 128 256), losses := [] }

theorem u1247 : Upper (D 10) (R 10) [6,33,96,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1247 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 100 104 152 432 464 400 400), lower := (rows 7 35 100 104 152 32 64 128 256), losses := [] }

theorem u1248 : Upper (D 10) (R 10) [6,33,96,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1248 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 100 104 400 440 472 408 408), lower := (rows 7 35 100 104 400 32 64 128 256), losses := [] }

theorem u1249 : Upper (D 10) (R 10) [6,33,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1249 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 152 280 480 480 480 480), lower := (rows 7 35 100 152 280 32 64 128 256), losses := [] }

theorem u1250 : Upper (D 10) (R 10) [6,33,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1250 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 456, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 152 304 488 456 456 456), lower := (rows 7 35 100 152 304 32 64 128 256), losses := [] }

theorem u1251 : Upper (D 10) (R 10) [6,33,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1251 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1252 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 152 336 424 488 424 424), lower := (rows 7 35 100 152 336 32 64 128 256), losses := [] }

theorem u1252 : Upper (D 10) (R 10) [6,33,96,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1252 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 168 208 312 344 408 280), lower := (rows 7 35 100 168 208 32 64 128 256), losses := [] }

theorem u1253 : Upper (D 10) (R 10) [6,33,96,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1253 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 168 336 440 472 408 408), lower := (rows 7 35 100 168 336 32 64 128 256), losses := [] }

theorem u1254 : Upper (D 10) (R 10) [6,33,96,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1254 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 168 400 376 344 472 344), lower := (rows 7 35 100 168 400 32 64 128 256), losses := [] }

theorem u1255 : Upper (D 10) (R 10) [6,33,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1255 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 7 35 100 200 400 312 376 440 312), lower := (rows 7 35 100 200 400 32 64 128 256), losses := [] }

theorem u1256 : Upper (D 10) (R 10) [6,33,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1256 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 35 196 56 56 480 448 448 448), lower := (rows 7 35 196 56 56 32 64 128 256), losses := [] }

theorem u1257 : Upper (D 10) (R 10) [6,33,192,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1257 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 56 88 416 480 416 416), lower := (rows 7 35 196 56 88 32 64 128 256), losses := [] }

theorem u1258 : Upper (D 10) (R 10) [6,33,192,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1258 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 392, camps := [{ cop := 4, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 35 196 56 112 424 456 392 392), lower := (rows 7 35 196 56 112 32 64 128 256), losses := [] }

theorem u1259 : Upper (D 10) (R 10) [6,33,192,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1259 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P10
