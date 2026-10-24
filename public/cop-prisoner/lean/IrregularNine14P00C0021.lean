import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0005
import IrregularNine14P00C0006

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1260 : PairBound 9 := { available := 389, camps := [], pairs := [], upper := (rows 51 67 84 168 24 421 453 389 389), lower := (rows 51 67 84 168 24 32 64 128 256), losses := [] }

theorem u1260 : Upper (D 0) (R 0) [50,65,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1260
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1261 : Route 9 := (fun mask => (mask,id))

def c1261 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1261 : Upper (D 0) (R 0) [50,65,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,160,128] 13 (by decide) (choices 1) [1,4,8,256] r1261 c1261
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u342
  · exact u343
  · exact u344
  · exact u345

def b1262 : PairBound 9 := { available := 141, camps := [], pairs := [], upper := (rows 51 67 84 168 272 173 205 141 397), lower := (rows 51 67 84 168 272 32 64 128 256), losses := [] }

theorem u1262 : Upper (D 0) (R 0) [50,65,80,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1262
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 268 17 168 232 168 424), lower := (rows 51 67 84 268 17 32 64 128 256), losses := [] }

theorem u1263 : Upper (D 0) (R 0) [50,65,80,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1263
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 67 84 268 24 161 225 161 417), lower := (rows 51 67 84 268 24 32 64 128 256), losses := [] }

theorem u1264 : Upper (D 0) (R 0) [50,65,80,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1264
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 268 48 169 201 137 393), lower := (rows 51 67 84 268 48 32 64 128 256), losses := [] }

theorem u1265 : Upper (D 0) (R 0) [50,65,80,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1265
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1266 : Route 9 := (fun mask => (mask,id))

def c1266 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1266 : Upper (D 0) (R 0) [50,65,80,260,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,260,128] 13 (by decide) (choices 1) [1,8,128] r1266 c1266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u346
  · exact u347
  · exact u348

def b1267 : PairBound 9 := { available := 140, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 296 17 172 204 140 396), lower := (rows 51 67 84 296 17 32 64 128 256), losses := [] }

theorem u1267 : Upper (D 0) (R 0) [50,65,80,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1267
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 67 84 296 20 169 201 137 393), lower := (rows 51 67 84 296 20 32 64 128 256), losses := [] }

theorem u1268 : Upper (D 0) (R 0) [50,65,80,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1268
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 67 84 296 24 165 197 133 389), lower := (rows 51 67 84 296 24 32 64 128 256), losses := [] }

theorem u1269 : Upper (D 0) (R 0) [50,65,80,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1269
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1270 : Route 9 := (fun mask => (mask,id))

def c1270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1270 : Upper (D 0) (R 0) [50,65,80,288,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,288,128] 13 (by decide) (choices 1) [1,4,8,128] r1270 c1270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u349
  · exact u350
  · exact u351
  · exact u352

def b1271 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 84 392 17 172 236 172 428), lower := (rows 51 67 84 392 17 32 64 128 256), losses := [] }

theorem u1271 : Upper (D 0) (R 0) [50,65,80,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1271
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 67 84 392 20 169 233 169 425), lower := (rows 51 67 84 392 20 32 64 128 256), losses := [] }

theorem u1272 : Upper (D 0) (R 0) [50,65,80,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1272
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 67 84 392 24 165 229 165 421), lower := (rows 51 67 84 392 24 32 64 128 256), losses := [] }

theorem u1273 : Upper (D 0) (R 0) [50,65,80,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1273
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 84 392 48 173 205 141 397), lower := (rows 51 67 84 392 48 32 64 128 256), losses := [] }

theorem u1274 : Upper (D 0) (R 0) [50,65,80,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1274
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1275 : Route 9 := (fun mask => (mask,id))

def c1275 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1275 : Upper (D 0) (R 0) [50,65,80,384,128] 13 := by
  apply FastRouting.sound _ _ [50,65,80,384,128] 13 (by decide) (choices 1) [1,4,8] r1275 c1275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u353
  · exact u354
  · exact u355

def b1276 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 268 17 240 240 240 496), lower := (rows 51 67 140 268 17 32 64 128 256), losses := [] }

theorem u1276 : Upper (D 0) (R 0) [50,65,136,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1276
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 268 48 241 209 209 465), lower := (rows 51 67 140 268 48 32 64 128 256), losses := [] }

theorem u1277 : Upper (D 0) (R 0) [50,65,136,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1277
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 268 80 177 241 177 433), lower := (rows 51 67 140 268 80 32 64 128 256), losses := [] }

theorem u1278 : Upper (D 0) (R 0) [50,65,136,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1278
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 140 268 144 113 113 241 369), lower := (rows 51 67 140 268 144 32 64 128 256), losses := [] }

theorem u1279 : Upper (D 0) (R 0) [50,65,136,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1279
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 280 17 228 228 228 484), lower := (rows 51 67 140 280 17 32 64 128 256), losses := [] }

theorem u1280 : Upper (D 0) (R 0) [50,65,136,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1280
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1281 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 67 140 280 20 225 225 225 481), lower := (rows 51 67 140 280 20 32 64 128 256), losses := [] }

theorem u1281 : Upper (D 0) (R 0) [50,65,136,272,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1281
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1282 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 280 48 229 197 197 453), lower := (rows 51 67 140 280 48 32 64 128 256), losses := [] }

theorem u1282 : Upper (D 0) (R 0) [50,65,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1282
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 140 280 80 165 229 165 421), lower := (rows 51 67 140 280 80 32 64 128 256), losses := [] }

theorem u1283 : Upper (D 0) (R 0) [50,65,136,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1283
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1284 : Route 9 := (fun mask => (mask,id))

def c1284 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1284 : Upper (D 0) (R 0) [50,65,136,272,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,272,128] 13 (by decide) (choices 1) [1,4,64] r1284 c1284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u356
  · exact u357
  · exact u358

def b1285 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 140 328 17 180 244 180 436), lower := (rows 51 67 140 328 17 32 64 128 256), losses := [] }

theorem u1285 : Upper (D 0) (R 0) [50,65,136,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1285
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 67 140 328 20 177 241 177 433), lower := (rows 51 67 140 328 20 32 64 128 256), losses := [] }

theorem u1286 : Upper (D 0) (R 0) [50,65,136,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1286
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 328 48 181 213 149 405), lower := (rows 51 67 140 328 48 32 64 128 256), losses := [] }

theorem u1287 : Upper (D 0) (R 0) [50,65,136,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1287
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1288_1 : Upper (D 0) (R 0) [50,65,136,320,128,1] 13 :=
  permutation_upper _ _ _ [50,65,136,320,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u359

theorem m1288_4 : Upper (D 0) (R 0) [50,65,136,320,128,4] 13 :=
  permutation_upper _ _ _ [50,65,136,320,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u360

theorem m1288_16 : Upper (D 0) (R 0) [50,65,136,320,128,16] 13 :=
  permutation_upper _ _ _ [50,65,136,320,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u361

def r1288 : Route 9 := (fun mask => (mask,id))

def c1288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1288 : Upper (D 0) (R 0) [50,65,136,320,128] 13 := by
  apply FastRouting.sound _ _ [50,65,136,320,128] 13 (by decide) (choices 1) [1,4,16] r1288 c1288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1288_1
  · exact m1288_4
  · exact m1288_16

def b1289 : PairBound 9 := { available := 332, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 168 17 364 332 460 332), lower := (rows 51 67 148 168 17 32 64 128 256), losses := [] }

theorem u1289 : Upper (D 0) (R 0) [50,65,144,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1289
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 329, camps := [], pairs := [], upper := (rows 51 67 148 168 20 361 329 457 329), lower := (rows 51 67 148 168 20 32 64 128 256), losses := [] }

theorem u1290 : Upper (D 0) (R 0) [50,65,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1290
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 325, camps := [], pairs := [], upper := (rows 51 67 148 168 24 357 325 453 325), lower := (rows 51 67 148 168 24 32 64 128 256), losses := [] }

theorem u1291 : Upper (D 0) (R 0) [50,65,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1291
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 168 80 301 333 397 269), lower := (rows 51 67 148 168 80 32 64 128 256), losses := [] }

theorem u1292 : Upper (D 0) (R 0) [50,65,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1292
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 77, camps := [], pairs := [], upper := (rows 51 67 148 168 272 109 77 205 333), lower := (rows 51 67 148 168 272 32 64 128 256), losses := [] }

theorem u1293 : Upper (D 0) (R 0) [50,65,144,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1293
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 200 17 300 364 428 300), lower := (rows 51 67 148 200 17 32 64 128 256), losses := [] }

theorem u1294 : Upper (D 0) (R 0) [50,65,144,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1294
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 297, camps := [], pairs := [], upper := (rows 51 67 148 200 20 297 361 425 297), lower := (rows 51 67 148 200 20 32 64 128 256), losses := [] }

theorem u1295 : Upper (D 0) (R 0) [50,65,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1295
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 293, camps := [], pairs := [], upper := (rows 51 67 148 200 24 293 357 421 293), lower := (rows 51 67 148 200 24 32 64 128 256), losses := [] }

theorem u1296 : Upper (D 0) (R 0) [50,65,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1296
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 200 48 301 333 397 269), lower := (rows 51 67 148 200 48 32 64 128 256), losses := [] }

theorem u1297 : Upper (D 0) (R 0) [50,65,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1297
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 45, camps := [], pairs := [], upper := (rows 51 67 148 200 272 45 109 173 301), lower := (rows 51 67 148 200 272 32 64 128 256), losses := [] }

theorem u1298 : Upper (D 0) (R 0) [50,65,144,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1298
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 268 17 232 232 232 488), lower := (rows 51 67 148 268 17 32 64 128 256), losses := [] }

theorem u1299 : Upper (D 0) (R 0) [50,65,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1299
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 67 148 268 24 225 225 225 481), lower := (rows 51 67 148 268 24 32 64 128 256), losses := [] }

theorem u1300 : Upper (D 0) (R 0) [50,65,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1300
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 268 48 233 201 201 457), lower := (rows 51 67 148 268 48 32 64 128 256), losses := [] }

theorem u1301 : Upper (D 0) (R 0) [50,65,144,260,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1301
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 268 80 169 233 169 425), lower := (rows 51 67 148 268 80 32 64 128 256), losses := [] }

theorem u1302 : Upper (D 0) (R 0) [50,65,144,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1302
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 268 144 105 105 233 361), lower := (rows 51 67 148 268 144 32 64 128 256), losses := [] }

theorem u1303 : Upper (D 0) (R 0) [50,65,144,260,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1303
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 296 17 236 204 204 460), lower := (rows 51 67 148 296 17 32 64 128 256), losses := [] }

theorem u1304 : Upper (D 0) (R 0) [50,65,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1304
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 201, camps := [], pairs := [], upper := (rows 51 67 148 296 20 233 201 201 457), lower := (rows 51 67 148 296 20 32 64 128 256), losses := [] }

theorem u1305 : Upper (D 0) (R 0) [50,65,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1305
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 197, camps := [], pairs := [], upper := (rows 51 67 148 296 24 229 197 197 453), lower := (rows 51 67 148 296 24 32 64 128 256), losses := [] }

theorem u1306 : Upper (D 0) (R 0) [50,65,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1306
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 296 80 173 205 141 397), lower := (rows 51 67 148 296 80 32 64 128 256), losses := [] }

theorem u1307 : Upper (D 0) (R 0) [50,65,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1307
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1308 : PairBound 9 := { available := 77, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 296 144 109 77 205 333), lower := (rows 51 67 148 296 144 32 64 128 256), losses := [] }

theorem u1308 : Upper (D 0) (R 0) [50,65,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1308
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1309 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 328 17 172 236 172 428), lower := (rows 51 67 148 328 17 32 64 128 256), losses := [] }

theorem u1309 : Upper (D 0) (R 0) [50,65,144,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1309
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 67 148 328 20 169 233 169 425), lower := (rows 51 67 148 328 20 32 64 128 256), losses := [] }

theorem u1310 : Upper (D 0) (R 0) [50,65,144,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1310
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 67 148 328 24 165 229 165 421), lower := (rows 51 67 148 328 24 32 64 128 256), losses := [] }

theorem u1311 : Upper (D 0) (R 0) [50,65,144,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1311
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 328 48 173 205 141 397), lower := (rows 51 67 148 328 48 32 64 128 256), losses := [] }

theorem u1312 : Upper (D 0) (R 0) [50,65,144,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1312
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 45, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 148 328 144 45 109 173 301), lower := (rows 51 67 148 328 144 32 64 128 256), losses := [] }

theorem u1313 : Upper (D 0) (R 0) [50,65,144,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1313
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 108, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 148 392 17 108 108 236 364), lower := (rows 51 67 148 392 17 32 64 128 256), losses := [] }

theorem u1314 : Upper (D 0) (R 0) [50,65,144,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1314
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 51 67 148 392 20 105 105 233 361), lower := (rows 51 67 148 392 20 32 64 128 256), losses := [] }

theorem u1315 : Upper (D 0) (R 0) [50,65,144,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1315
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 51 67 148 392 24 101 101 229 357), lower := (rows 51 67 148 392 24 32 64 128 256), losses := [] }

theorem u1316 : Upper (D 0) (R 0) [50,65,144,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1316
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 148 392 48 109 77 205 333), lower := (rows 51 67 148 392 48 32 64 128 256), losses := [] }

theorem u1317 : Upper (D 0) (R 0) [50,65,144,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1317
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 148 392 80 45 109 173 301), lower := (rows 51 67 148 392 80 32 64 128 256), losses := [] }

theorem u1318 : Upper (D 0) (R 0) [50,65,144,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1318
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 268 17 184 248 184 440), lower := (rows 51 67 196 268 17 32 64 128 256), losses := [] }

theorem u1319 : Upper (D 0) (R 0) [50,65,192,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1319
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P00
