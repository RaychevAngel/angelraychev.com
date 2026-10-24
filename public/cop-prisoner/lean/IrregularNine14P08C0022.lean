import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0002

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 67 164 152 304 40 97 225 353), lower := (rows 7 67 164 152 304 40 64 128 256), losses := [] }

theorem u1320 : Upper (D 8) (R 8) [6,65,160,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1320 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1321 : Route 9 := (fun mask => (mask,id))

def c1321 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1321 : Upper (D 8) (R 8) [6,65,160,144,288,64] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144,288,64] 13 (by decide) (choices 1) [1,8,32] r1321 c1321
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u134
  · exact u135
  · exact u136

def b1322 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 152 336 33 104 168 296), lower := (rows 7 67 164 152 336 33 64 128 256), losses := [] }

theorem u1322 : Upper (D 8) (R 8) [6,65,160,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 164 152 336 40 97 161 289), lower := (rows 7 67 164 152 336 40 64 128 256), losses := [] }

theorem u1323 : Upper (D 8) (R 8) [6,65,160,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1323 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 200 280 33 112 176 304), lower := (rows 7 67 164 200 280 33 64 128 256), losses := [] }

theorem u1324 : Upper (D 8) (R 8) [6,65,160,192,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 164 200 280 48 97 161 289), lower := (rows 7 67 164 200 280 48 64 128 256), losses := [] }

theorem u1325 : Upper (D 8) (R 8) [6,65,160,192,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1325 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 200 304 33 120 184 312), lower := (rows 7 67 164 200 304 33 64 128 256), losses := [] }

theorem u1326 : Upper (D 8) (R 8) [6,65,160,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 67 164 200 304 40 113 177 305), lower := (rows 7 67 164 200 304 40 64 128 256), losses := [] }

theorem u1327 : Upper (D 8) (R 8) [6,65,160,192,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1327 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 67 164 200 304 48 105 169 297), lower := (rows 7 67 164 200 304 48 64 128 256), losses := [] }

theorem u1328 : Upper (D 8) (R 8) [6,65,160,192,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1328 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 56 208 33 224 160 416), lower := (rows 7 67 268 56 208 33 64 128 256), losses := [] }

theorem u1329 : Upper (D 8) (R 8) [6,65,264,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1329 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 268 56 208 160 97 161 289), lower := (rows 7 67 268 56 208 160 64 128 256), losses := [] }

theorem u1330 : Upper (D 8) (R 8) [6,65,264,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1330 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 152 112 33 224 160 416), lower := (rows 7 67 268 152 112 33 64 128 256), losses := [] }

theorem u1331 : Upper (D 8) (R 8) [6,65,264,144,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1331 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1332 : Route 9 := (fun mask => (mask,id))

def c1332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1332 : Upper (D 8) (R 8) [6,65,264,144,96,128] 13 := by
  apply FastRouting.sound _ _ [6,65,264,144,96,128] 13 (by decide) (choices 1) [1,32] r1332 c1332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u137
  · exact u138

def b1333 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 168 112 33 240 176 432), lower := (rows 7 67 268 168 112 33 64 128 256), losses := [] }

theorem u1333 : Upper (D 8) (R 8) [6,65,264,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1333 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 268 168 112 48 225 161 417), lower := (rows 7 67 268 168 112 48 64 128 256), losses := [] }

theorem u1334 : Upper (D 8) (R 8) [6,65,264,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1334 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 268 168 112 160 113 177 305), lower := (rows 7 67 268 168 112 160 64 128 256), losses := [] }

theorem u1335 : Upper (D 8) (R 8) [6,65,264,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 168 208 33 112 176 304), lower := (rows 7 67 268 168 208 33 64 128 256), losses := [] }

theorem u1336 : Upper (D 8) (R 8) [6,65,264,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1336 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 268 168 208 48 97 161 289), lower := (rows 7 67 268 168 208 48 64 128 256), losses := [] }

theorem u1337 : Upper (D 8) (R 8) [6,65,264,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1337 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 56 152 33 224 224 480), lower := (rows 7 67 292 56 152 33 64 128 256), losses := [] }

theorem u1338 : Upper (D 8) (R 8) [6,65,288,48,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1339 : Route 9 := (fun mask => (mask,id))

def c1339 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1339 : Upper (D 8) (R 8) [6,65,288,48,136,64] 13 := by
  apply FastRouting.sound _ _ [6,65,288,48,136,64] 13 (by decide) (choices 1) [1,32,128] r1339 c1339
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u139
  · exact u140
  · exact u141

def b1340 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 292 56 152 160 97 225 353), lower := (rows 7 67 292 56 152 160 64 128 256), losses := [] }

theorem u1340 : Upper (D 8) (R 8) [6,65,288,48,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1340 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 56 208 33 232 168 424), lower := (rows 7 67 292 56 208 33 64 128 256), losses := [] }

theorem u1341 : Upper (D 8) (R 8) [6,65,288,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1341 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 292 56 208 40 225 161 417), lower := (rows 7 67 292 56 208 40 64 128 256), losses := [] }

theorem u1342 : Upper (D 8) (R 8) [6,65,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1342 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 56 208 160 105 169 297), lower := (rows 7 67 292 56 208 160 64 128 256), losses := [] }

theorem u1343 : Upper (D 8) (R 8) [6,65,288,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1343 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 168, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 88 176 33 232 168 424), lower := (rows 7 67 292 88 176 33 64 128 256), losses := [] }

theorem u1344 : Upper (D 8) (R 8) [6,65,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1344 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 292 88 176 40 225 161 417), lower := (rows 7 67 292 88 176 40 64 128 256), losses := [] }

theorem u1345 : Upper (D 8) (R 8) [6,65,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1345 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 88 176 160 105 169 297), lower := (rows 7 67 292 88 176 160 64 128 256), losses := [] }

theorem u1346 : Upper (D 8) (R 8) [6,65,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 104 152 33 240 176 432), lower := (rows 7 67 292 104 152 33 64 128 256), losses := [] }

theorem u1347 : Upper (D 8) (R 8) [6,65,288,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 67 292 104 152 48 225 161 417), lower := (rows 7 67 292 104 152 48 64 128 256), losses := [] }

theorem u1348 : Upper (D 8) (R 8) [6,65,288,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1348 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1349 : Route 9 := (fun mask => (mask,id))

def c1349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1349 : Upper (D 8) (R 8) [6,65,288,96,136,128] 13 := by
  apply FastRouting.sound _ _ [6,65,288,96,136,128] 13 (by decide) (choices 1) [1,16,32] r1349 c1349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u142
  · exact u143
  · exact u144

def b1350 : PairBound 9 := { available := 152, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 104 176 33 216 152 408), lower := (rows 7 67 292 104 176 33 64 128 256), losses := [] }

theorem u1350 : Upper (D 8) (R 8) [6,65,288,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 67 292 104 176 40 209 145 401), lower := (rows 7 67 292 104 176 40 64 128 256), losses := [] }

theorem u1351 : Upper (D 8) (R 8) [6,65,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1351 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 67 292 104 176 48 201 137 393), lower := (rows 7 67 292 104 176 48 64 128 256), losses := [] }

theorem u1352 : Upper (D 8) (R 8) [6,65,288,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1352 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 104 176 160 89 153 281), lower := (rows 7 67 292 104 176 160 64 128 256), losses := [] }

theorem u1353 : Upper (D 8) (R 8) [6,65,288,96,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 168 208 33 120 184 312), lower := (rows 7 67 292 168 208 33 64 128 256), losses := [] }

theorem u1354 : Upper (D 8) (R 8) [6,65,288,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 67 292 168 208 40 113 177 305), lower := (rows 7 67 292 168 208 40 64 128 256), losses := [] }

theorem u1355 : Upper (D 8) (R 8) [6,65,288,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1355 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 67 292 168 208 48 105 169 297), lower := (rows 7 67 292 168 208 48 64 128 256), losses := [] }

theorem u1356 : Upper (D 8) (R 8) [6,65,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1356 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 56 208 33 104 168 296), lower := (rows 7 67 388 56 208 33 64 128 256), losses := [] }

theorem u1357 : Upper (D 8) (R 8) [6,65,384,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 388 56 208 40 97 161 289), lower := (rows 7 67 388 56 208 40 64 128 256), losses := [] }

theorem u1358 : Upper (D 8) (R 8) [6,65,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1358 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 88 176 33 104 168 296), lower := (rows 7 67 388 88 176 33 64 128 256), losses := [] }

theorem u1359 : Upper (D 8) (R 8) [6,65,384,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1359 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 388 88 176 40 97 161 289), lower := (rows 7 67 388 88 176 40 64 128 256), losses := [] }

theorem u1360 : Upper (D 8) (R 8) [6,65,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1360 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 104 152 33 112 176 304), lower := (rows 7 67 388 104 152 33 64 128 256), losses := [] }

theorem u1361 : Upper (D 8) (R 8) [6,65,384,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1361 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 67 388 104 152 48 97 161 289), lower := (rows 7 67 388 104 152 48 64 128 256), losses := [] }

theorem u1362 : Upper (D 8) (R 8) [6,65,384,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1362 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 388 104 176 33 120 184 312), lower := (rows 7 67 388 104 176 33 64 128 256), losses := [] }

theorem u1363 : Upper (D 8) (R 8) [6,65,384,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1363 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 67 388 104 176 40 113 177 305), lower := (rows 7 67 388 104 176 40 64 128 256), losses := [] }

theorem u1364 : Upper (D 8) (R 8) [6,65,384,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1364 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 67 388 104 176 48 105 169 297), lower := (rows 7 67 388 104 176 48 64 128 256), losses := [] }

theorem u1365 : Upper (D 8) (R 8) [6,65,384,96,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1365 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 148 41 304 33 224 224 480), lower := (rows 7 74 148 41 304 33 64 128 256), losses := [] }

theorem u1366 : Upper (D 8) (R 8) [6,72,144,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1366 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 7 74 148 41 304 96 225 161 417), lower := (rows 7 74 148 41 304 96 64 128 256), losses := [] }

theorem u1367 : Upper (D 8) (R 8) [6,72,144,33,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1367 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 7 74 148 41 304 160 97 225 353), lower := (rows 7 74 148 41 304 160 64 128 256), losses := [] }

theorem u1368 : Upper (D 8) (R 8) [6,72,144,33,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1368 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 25 304 33 224 224 480), lower := (rows 7 74 164 25 304 33 64 128 256), losses := [] }

theorem u1369 : Upper (D 8) (R 8) [6,72,160,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1369 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1370 : Route 9 := (fun mask => (mask,id))

def c1370 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1370 : Upper (D 8) (R 8) [6,72,160,17,288,64] 13 := by
  apply FastRouting.sound _ _ [6,72,160,17,288,64] 13 (by decide) (choices 1) [1,32,128] r1370 c1370
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u145
  · exact u146
  · exact u147

def b1371 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 25 304 160 97 225 353), lower := (rows 7 74 164 25 304 160 64 128 256), losses := [] }

theorem u1371 : Upper (D 8) (R 8) [6,72,160,17,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1371 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1372 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 112 33 464 400 400), lower := (rows 7 74 164 41 112 33 64 128 256), losses := [] }

theorem u1372 : Upper (D 8) (R 8) [6,72,160,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1372 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1373 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 7 74 164 41 112 48 449 385 385), lower := (rows 7 74 164 41 112 48 64 128 256), losses := [] }

theorem u1373 : Upper (D 8) (R 8) [6,72,160,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1373 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 347, targets := 128 }], pairs := [(0,7)], upper := (rows 7 74 164 41 112 160 337 401 273), lower := (rows 7 74 164 41 112 160 64 128 256), losses := [] }

theorem u1374 : Upper (D 8) (R 8) [6,72,160,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1374 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 74 164 41 112 288 209 145 401), lower := (rows 7 74 164 41 112 288 64 128 256), losses := [] }

theorem u1375 : Upper (D 8) (R 8) [6,72,160,33,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1375 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 208 33 368 432 304), lower := (rows 7 74 164 41 208 33 64 128 256), losses := [] }

theorem u1376 : Upper (D 8) (R 8) [6,72,160,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1376 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 7 74 164 41 208 48 353 417 289), lower := (rows 7 74 164 41 208 48 64 128 256), losses := [] }

theorem u1377 : Upper (D 8) (R 8) [6,72,160,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1377 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 74 164 41 208 288 113 177 305), lower := (rows 7 74 164 41 208 288 64 128 256), losses := [] }

theorem u1378 : Upper (D 8) (R 8) [6,72,160,33,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1378 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 466, targets := 1 }], pairs := [(1,0)], upper := (rows 7 74 164 41 304 33 208 208 464), lower := (rows 7 74 164 41 304 33 64 128 256), losses := [] }

theorem u1379 : Upper (D 8) (R 8) [6,72,160,33,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1379 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P08
