import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0005

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 69 137 48 496 464 464 464), lower := (rows 51 14 69 137 48 32 64 128 256), losses := [] }

theorem u1200 : Upper (D 0) (R 0) [50,12,65,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1200
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 69 137 80 432 496 432 432), lower := (rows 51 14 69 137 80 32 64 128 256), losses := [] }

theorem u1201 : Upper (D 0) (R 0) [50,12,65,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1201
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 14 69 137 272 240 240 240 496), lower := (rows 51 14 69 137 272 32 64 128 256), losses := [] }

theorem u1202 : Upper (D 0) (R 0) [50,12,65,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1202
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 69 265 48 240 208 208 464), lower := (rows 51 14 69 265 48 32 64 128 256), losses := [] }

theorem u1203 : Upper (D 0) (R 0) [50,12,65,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1203
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 69 265 80 176 240 176 432), lower := (rows 51 14 69 265 80 32 64 128 256), losses := [] }

theorem u1204 : Upper (D 0) (R 0) [50,12,65,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1204
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1205_16 : Upper (D 0) (R 0) [50,12,65,257,128,16] 13 :=
  permutation_upper _ _ _ [50,12,65,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u319

theorem m1205_64 : Upper (D 0) (R 0) [50,12,65,257,128,64] 13 :=
  permutation_upper _ _ _ [50,12,65,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u320

def r1205 : Route 9 := (fun mask => (mask,id))

def c1205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1205 : Upper (D 0) (R 0) [50,12,65,257,128] 13 := by
  apply FastRouting.sound _ _ [50,12,65,257,128] 13 (by decide) (choices 1) [16,64,128] r1205 c1205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1205_16
  · exact m1205_64
  · exact u321

def b1206 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 51 14 69 392 17 240 240 240 496), lower := (rows 51 14 69 392 17 32 64 128 256), losses := [] }

theorem u1206 : Upper (D 0) (R 0) [50,12,65,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1206
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 69 392 48 241 209 209 465), lower := (rows 51 14 69 392 48 32 64 128 256), losses := [] }

theorem u1207 : Upper (D 0) (R 0) [50,12,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1207
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1208 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 69 392 80 177 241 177 433), lower := (rows 51 14 69 392 80 32 64 128 256), losses := [] }

theorem u1208 : Upper (D 0) (R 0) [50,12,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1208
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1209 : PairBound 9 := { available := 113, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 51 14 69 392 144 113 113 241 369), lower := (rows 51 14 69 392 144 32 64 128 256), losses := [] }

theorem u1209 : Upper (D 0) (R 0) [50,12,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1209
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1210 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 51 14 196 265 17 240 240 240 496), lower := (rows 51 14 196 265 17 32 64 128 256), losses := [] }

theorem u1210 : Upper (D 0) (R 0) [50,12,192,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1210
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1211 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 196 265 48 241 209 209 465), lower := (rows 51 14 196 265 48 32 64 128 256), losses := [] }

theorem u1211 : Upper (D 0) (R 0) [50,12,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1211
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 196 265 80 177 241 177 433), lower := (rows 51 14 196 265 80 32 64 128 256), losses := [] }

theorem u1212 : Upper (D 0) (R 0) [50,12,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1212
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1213 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 19, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 28 104 17 420 452 388 388), lower := (rows 51 67 28 104 17 32 64 128 256), losses := [] }

theorem u1213 : Upper (D 0) (R 0) [50,65,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1213
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1214 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 51 67 28 104 20 417 449 385 385), lower := (rows 51 67 28 104 20 32 64 128 256), losses := [] }

theorem u1214 : Upper (D 0) (R 0) [50,65,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1214
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1215 : Route 9 := (fun mask => (mask,id))

def c1215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u1215 : Upper (D 0) (R 0) [50,65,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,96,128] 13 (by decide) (choices 1) [1,4,128,256] r1215 c1215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u322
  · exact u323
  · exact u324
  · exact u325

def b1216 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 67 28 104 272 165 197 133 389), lower := (rows 51 67 28 104 272 32 64 128 256), losses := [] }

theorem u1216 : Upper (D 0) (R 0) [50,65,24,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1216
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1217 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 168 17 484 452 452 452), lower := (rows 51 67 28 168 17 32 64 128 256), losses := [] }

theorem u1217 : Upper (D 0) (R 0) [50,65,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1217
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 449, camps := [], pairs := [], upper := (rows 51 67 28 168 20 481 449 449 449), lower := (rows 51 67 28 168 20 32 64 128 256), losses := [] }

theorem u1218 : Upper (D 0) (R 0) [50,65,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1218
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 168 80 421 453 389 389), lower := (rows 51 67 28 168 80 32 64 128 256), losses := [] }

theorem u1219 : Upper (D 0) (R 0) [50,65,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1219
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 168 144 357 325 453 325), lower := (rows 51 67 28 168 144 32 64 128 256), losses := [] }

theorem u1220 : Upper (D 0) (R 0) [50,65,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1220
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 51 67 28 168 272 229 197 197 453), lower := (rows 51 67 28 168 272 32 64 128 256), losses := [] }

theorem u1221 : Upper (D 0) (R 0) [50,65,24,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1221
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 200 17 420 484 420 420), lower := (rows 51 67 28 200 17 32 64 128 256), losses := [] }

theorem u1222 : Upper (D 0) (R 0) [50,65,24,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1222
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 51 67 28 200 20 417 481 417 417), lower := (rows 51 67 28 200 20 32 64 128 256), losses := [] }

theorem u1223 : Upper (D 0) (R 0) [50,65,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1223
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 200 48 421 453 389 389), lower := (rows 51 67 28 200 48 32 64 128 256), losses := [] }

theorem u1224 : Upper (D 0) (R 0) [50,65,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1224
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 200 144 293 357 421 293), lower := (rows 51 67 28 200 144 32 64 128 256), losses := [] }

theorem u1225 : Upper (D 0) (R 0) [50,65,24,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1225
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 67 28 200 272 165 229 165 421), lower := (rows 51 67 28 200 272 32 64 128 256), losses := [] }

theorem u1226 : Upper (D 0) (R 0) [50,65,24,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1226
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 296 17 228 196 196 452), lower := (rows 51 67 28 296 17 32 64 128 256), losses := [] }

theorem u1227 : Upper (D 0) (R 0) [50,65,24,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1227
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 67 28 296 20 225 193 193 449), lower := (rows 51 67 28 296 20 32 64 128 256), losses := [] }

theorem u1228 : Upper (D 0) (R 0) [50,65,24,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1228
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 296 80 165 197 133 389), lower := (rows 51 67 28 296 80 32 64 128 256), losses := [] }

theorem u1229 : Upper (D 0) (R 0) [50,65,24,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1229
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1230 : Route 9 := (fun mask => (mask,id))

def c1230 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1230 : Upper (D 0) (R 0) [50,65,24,288,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,288,128] 13 (by decide) (choices 1) [1,4,64,128] r1230 c1230
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u326
  · exact u327
  · exact u328
  · exact u329

def b1231 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 328 17 164 228 164 420), lower := (rows 51 67 28 328 17 32 64 128 256), losses := [] }

theorem u1231 : Upper (D 0) (R 0) [50,65,24,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1231
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 28 328 20 161 225 161 417), lower := (rows 51 67 28 328 20 32 64 128 256), losses := [] }

theorem u1232 : Upper (D 0) (R 0) [50,65,24,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1232
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 328 48 165 197 133 389), lower := (rows 51 67 28 328 48 32 64 128 256), losses := [] }

theorem u1233 : Upper (D 0) (R 0) [50,65,24,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1233
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1234 : Route 9 := (fun mask => (mask,id))

def c1234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1234 : Upper (D 0) (R 0) [50,65,24,320,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,320,128] 13 (by decide) (choices 1) [1,4,128] r1234 c1234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u330
  · exact u331
  · exact u332

def b1235 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 392 17 228 228 228 484), lower := (rows 51 67 28 392 17 32 64 128 256), losses := [] }

theorem u1235 : Upper (D 0) (R 0) [50,65,24,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1235
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 67 28 392 20 225 225 225 481), lower := (rows 51 67 28 392 20 32 64 128 256), losses := [] }

theorem u1236 : Upper (D 0) (R 0) [50,65,24,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1236
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 28 392 48 229 197 197 453), lower := (rows 51 67 28 392 48 32 64 128 256), losses := [] }

theorem u1237 : Upper (D 0) (R 0) [50,65,24,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1237
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 392 80 165 229 165 421), lower := (rows 51 67 28 392 80 32 64 128 256), losses := [] }

theorem u1238 : Upper (D 0) (R 0) [50,65,24,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1238
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1239 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 392 144 101 101 229 357), lower := (rows 51 67 28 392 144 32 64 128 256), losses := [] }

theorem u1239 : Upper (D 0) (R 0) [50,65,24,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1239
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1240 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 152 17 420 484 420 420), lower := (rows 51 67 76 152 17 32 64 128 256), losses := [] }

theorem u1240 : Upper (D 0) (R 0) [50,65,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1240
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 51 67 76 152 20 417 481 417 417), lower := (rows 51 67 76 152 20 32 64 128 256), losses := [] }

theorem u1241 : Upper (D 0) (R 0) [50,65,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1241
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 152 48 421 453 389 389), lower := (rows 51 67 76 152 48 32 64 128 256), losses := [] }

theorem u1242 : Upper (D 0) (R 0) [50,65,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1242
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 76 152 144 293 357 421 293), lower := (rows 51 67 76 152 144 32 64 128 256), losses := [] }

theorem u1243 : Upper (D 0) (R 0) [50,65,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1243
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1244 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 67 76 152 272 165 229 165 421), lower := (rows 51 67 76 152 272 32 64 128 256), losses := [] }

theorem u1244 : Upper (D 0) (R 0) [50,65,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1244
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1245 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 280 17 164 228 164 420), lower := (rows 51 67 76 280 17 32 64 128 256), losses := [] }

theorem u1245 : Upper (D 0) (R 0) [50,65,72,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1245
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 76 280 20 161 225 161 417), lower := (rows 51 67 76 280 20 32 64 128 256), losses := [] }

theorem u1246 : Upper (D 0) (R 0) [50,65,72,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1246
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 280 48 165 197 133 389), lower := (rows 51 67 76 280 48 32 64 128 256), losses := [] }

theorem u1247 : Upper (D 0) (R 0) [50,65,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1247
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1248 : Route 9 := (fun mask => (mask,id))

def c1248 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1248 : Upper (D 0) (R 0) [50,65,72,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,72,272,128] 13 (by decide) (choices 1) [1,4,128] r1248 c1248
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u333
  · exact u334
  · exact u335

def b1249 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 392 17 180 244 180 436), lower := (rows 51 67 76 392 17 32 64 128 256), losses := [] }

theorem u1249 : Upper (D 0) (R 0) [50,65,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1249
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 67 76 392 20 177 241 177 433), lower := (rows 51 67 76 392 20 32 64 128 256), losses := [] }

theorem u1250 : Upper (D 0) (R 0) [50,65,72,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1250
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1251 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 76 392 48 181 213 149 405), lower := (rows 51 67 76 392 48 32 64 128 256), losses := [] }

theorem u1251 : Upper (D 0) (R 0) [50,65,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1251
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1252_1 : Upper (D 0) (R 0) [50,65,72,384,128,1] 13 :=
  permutation_upper _ _ _ [50,65,72,384,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u336

theorem m1252_4 : Upper (D 0) (R 0) [50,65,72,384,128,4] 13 :=
  permutation_upper _ _ _ [50,65,72,384,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u337

theorem m1252_16 : Upper (D 0) (R 0) [50,65,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,65,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u338

def r1252 : Route 9 := (fun mask => (mask,id))

def c1252 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1252 : Upper (D 0) (R 0) [50,65,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,65,72,384,128] 13 (by decide) (choices 1) [1,4,16] r1252 c1252
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1252_1
  · exact m1252_4
  · exact m1252_16

def b1253 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 140 17 424 488 424 424), lower := (rows 51 67 84 140 17 32 64 128 256), losses := [] }

theorem u1253 : Upper (D 0) (R 0) [50,65,80,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1253
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 417, camps := [], pairs := [], upper := (rows 51 67 84 140 24 417 481 417 417), lower := (rows 51 67 84 140 24 32 64 128 256), losses := [] }

theorem u1254 : Upper (D 0) (R 0) [50,65,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1254
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 140 48 425 457 393 393), lower := (rows 51 67 84 140 48 32 64 128 256), losses := [] }

theorem u1255 : Upper (D 0) (R 0) [50,65,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1255
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1256 : Route 9 := (fun mask => (mask,id))

def c1256 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1256 : Upper (D 0) (R 0) [50,65,80,132,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,132,128] 13 (by decide) (choices 1) [1,8,256] r1256 c1256
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u339
  · exact u340
  · exact u341

def b1257 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 67 84 140 272 169 233 169 425), lower := (rows 51 67 84 140 272 32 64 128 256), losses := [] }

theorem u1257 : Upper (D 0) (R 0) [50,65,80,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1257
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1258 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 168 17 428 460 396 396), lower := (rows 51 67 84 168 17 32 64 128 256), losses := [] }

theorem u1258 : Upper (D 0) (R 0) [50,65,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1258
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1259 : PairBound 9 := { available := 393, camps := [], pairs := [], upper := (rows 51 67 84 168 20 425 457 393 393), lower := (rows 51 67 84 168 20 32 64 128 256), losses := [] }

theorem u1259 : Upper (D 0) (R 0) [50,65,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1259
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P00
