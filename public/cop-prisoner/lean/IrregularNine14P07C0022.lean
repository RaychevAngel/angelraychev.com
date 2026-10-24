import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 72, targets := 129 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(3,0),(3,7)], upper := (rows 7 35 196 104 280 48 66 129 385), lower := (rows 7 35 196 104 280 48 66 128 256), losses := [] }

theorem u1320 : Upper (D 7) (R 7) [6,33,192,96,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1320 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 104 280 48 192 131 259), lower := (rows 7 35 196 104 280 48 192 128 256), losses := [] }

theorem u1321 : Upper (D 7) (R 7) [6,33,192,96,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1321 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,0),(3,1),(3,7)], upper := (rows 7 35 196 104 400 48 65 138 266), lower := (rows 7 35 196 104 400 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 83 127 64 129 257), good := (rows 446 434 252 124 432 48 508 128 256) }] }

theorem u1322 : Upper (D 7) (R 7) [6,33,192,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1322 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 72, targets := 1 },{ cop := 1, region := 72, targets := 128 }], pairs := [(3,0),(3,1),(3,7)], upper := (rows 7 35 196 104 400 48 66 137 265), lower := (rows 7 35 196 104 400 48 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 76 19 115 64 129 257), good := (rows 445 433 236 104 432 48 120 128 256) }] }

theorem u1323 : Upper (D 7) (R 7) [6,33,192,96,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1323 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 104 400 48 72 131 259), lower := (rows 7 35 196 104 400 48 72 128 256), losses := [] }

theorem u1324 : Upper (D 7) (R 7) [6,33,192,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1324 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 26 208 96 72 160 416), lower := (rows 7 35 261 26 208 96 72 128 256), losses := [] }

theorem u1325 : Upper (D 7) (R 7) [6,33,257,18,192,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1325 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 35 261 26 208 96 96 136 392), lower := (rows 7 35 261 26 208 96 96 128 256), losses := [] }

theorem u1326 : Upper (D 7) (R 7) [6,33,257,18,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 261 26 208 96 192 168 296), lower := (rows 7 35 261 26 208 96 192 128 256), losses := [] }

theorem u1327 : Upper (D 7) (R 7) [6,33,257,18,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 1, region := 88, targets := 128 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 35 261 56 82 160 72 192 448), lower := (rows 7 35 261 56 82 160 72 128 256), losses := [] }

theorem u1328 : Upper (D 7) (R 7) [6,33,257,48,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1328 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 4, region := 168, targets := 2 }], pairs := [(3,0),(3,1),(4,0),(4,5)], upper := (rows 7 35 261 56 82 160 192 200 328), lower := (rows 7 35 261 56 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 18 0 232 136 264), good := (rows 23 83 261 472 82 192 192 192 256) }] }

theorem u1329 : Upper (D 7) (R 7) [6,33,257,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 112 160 72 144 400), lower := (rows 7 35 261 74 112 160 72 128 256), losses := [] }

theorem u1330 : Upper (D 7) (R 7) [6,33,257,66,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1330 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 112 160 80 136 392), lower := (rows 7 35 261 74 112 160 80 128 256), losses := [] }

theorem u1331 : Upper (D 7) (R 7) [6,33,257,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1331 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 24, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 261 74 112 160 192 152 280), lower := (rows 7 35 261 74 112 160 192 128 256), losses := [] }

theorem u1332 : Upper (D 7) (R 7) [6,33,257,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1332 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 152 96 80 160 416), lower := (rows 7 35 261 74 152 96 80 128 256), losses := [] }

theorem u1333 : Upper (D 7) (R 7) [6,33,257,66,136,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1333 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 405, targets := 96 }], pairs := [(0,5),(0,6),(2,5),(2,6)], upper := (rows 7 35 261 74 152 96 96 144 400), lower := (rows 7 35 261 74 152 96 96 128 256), losses := [] }

theorem u1334 : Upper (D 7) (R 7) [6,33,257,66,136,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1335 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(0,7),(3,0),(4,0),(4,1)], upper := (rows 7 35 261 74 152 96 192 176 304), lower := (rows 7 35 261 74 152 96 192 128 256), losses := [{ target := 7, region := (rows 17 18 20 8 16 104 64 0 272), good := (rows 7 35 261 106 319 96 96 0 256) }] }

theorem u1335 : Upper (D 7) (R 7) [6,33,257,66,136,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1336 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 248, targets := 1 },{ cop := 3, region := 176, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 35 261 74 152 160 80 224 352), lower := (rows 7 35 261 74 152 160 80 128 256), losses := [] }

theorem u1336 : Upper (D 7) (R 7) [6,33,257,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1336 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 261 74 152 160 96 208 336), lower := (rows 7 35 261 74 152 160 96 128 256), losses := [] }

theorem u1337 : Upper (D 7) (R 7) [6,33,257,66,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 176 96 72 144 400), lower := (rows 7 35 261 74 176 96 72 128 256), losses := [] }

theorem u1338 : Upper (D 7) (R 7) [6,33,257,66,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1338 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 389, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 261 74 176 96 80 136 392), lower := (rows 7 35 261 74 176 96 80 128 256), losses := [] }

theorem u1339 : Upper (D 7) (R 7) [6,33,257,66,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1339 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1340 : Route 9 := (fun mask => (mask,id))

def c1340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1340 : Upper (D 7) (R 7) [6,33,257,66,160,64,128] 13 := by
  apply FastRouting.sound _ _ [6,33,257,66,160,64,128] 13 (by decide) (choices 1) [8,16] r1340 c1340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u43
  · exact u44

def b1341 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 295, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 208 160 72 176 304), lower := (rows 7 35 261 74 208 160 72 128 256), losses := [] }

theorem u1341 : Upper (D 7) (R 7) [6,33,257,66,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1341 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 74 208 160 80 168 296), lower := (rows 7 35 261 74 208 160 80 128 256), losses := [] }

theorem u1342 : Upper (D 7) (R 7) [6,33,257,66,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1342 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 0, region := 248, targets := 1 }], pairs := [(0,5),(2,5),(3,0),(4,5)], upper := (rows 7 35 261 74 208 160 96 152 280), lower := (rows 7 35 261 74 208 160 96 128 256), losses := [] }

theorem u1343 : Upper (D 7) (R 7) [6,33,257,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1343 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 152, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 261 88 176 96 66 136 392), lower := (rows 7 35 261 88 176 96 66 128 256), losses := [] }

theorem u1344 : Upper (D 7) (R 7) [6,33,257,80,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1344 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 391, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 261 88 176 96 72 130 386), lower := (rows 7 35 261 88 176 96 72 128 256), losses := [] }

theorem u1345 : Upper (D 7) (R 7) [6,33,257,80,160,64,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1345 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 56, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 261 88 176 96 192 138 266), lower := (rows 7 35 261 88 176 96 192 128 256), losses := [] }

theorem u1346 : Upper (D 7) (R 7) [6,33,257,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1346 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 184, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 261 104 208 160 66 152 280), lower := (rows 7 35 261 104 208 160 66 128 256), losses := [] }

theorem u1347 : Upper (D 7) (R 7) [6,33,257,96,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1347 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 261 104 208 160 72 146 274), lower := (rows 7 35 261 104 208 160 72 128 256), losses := [] }

theorem u1348 : Upper (D 7) (R 7) [6,33,257,96,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1348 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 261 104 208 160 80 138 266), lower := (rows 7 35 261 104 208 160 80 128 256), losses := [] }

theorem u1349 : Upper (D 7) (R 7) [6,33,257,96,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1349 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 88, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(3,7)], upper := (rows 7 35 268 25 82 160 96 192 448), lower := (rows 7 35 268 25 82 160 96 128 256), losses := [] }

theorem u1350 : Upper (D 7) (R 7) [6,33,264,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1350 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(3,5),(4,0)], upper := (rows 7 35 268 25 82 160 192 224 352), lower := (rows 7 35 268 25 82 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 18 0 224 128 256), good := (rows 31 91 268 25 90 192 192 192 256) }] }

theorem u1351 : Upper (D 7) (R 7) [6,33,264,17,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1351 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 6, region := 176, targets := 3 }], pairs := [(3,7),(4,0),(4,1),(4,7)], upper := (rows 7 35 268 25 112 160 66 192 448), lower := (rows 7 35 268 25 112 160 66 128 256), losses := [] }

theorem u1352 : Upper (D 7) (R 7) [6,33,264,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1352 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 25 112 160 192 194 322), lower := (rows 7 35 268 25 112 160 192 128 256), losses := [] }

theorem u1353 : Upper (D 7) (R 7) [6,33,264,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1353 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 3, region := 484, targets := 3 }], pairs := [(2,0),(2,1),(3,7),(4,7)], upper := (rows 7 35 268 26 81 160 96 192 448), lower := (rows 7 35 268 26 81 160 96 128 256), losses := [] }

theorem u1354 : Upper (D 7) (R 7) [6,33,264,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1354 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 484, targets := 3 },{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(2,1),(3,5),(4,1)], upper := (rows 7 35 268 26 81 160 192 224 352), lower := (rows 7 35 268 26 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 2 4 11 18 0 224 128 256), good := (rows 31 91 268 26 89 192 192 192 256) }] }

theorem u1355 : Upper (D 7) (R 7) [6,33,264,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1355 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 56 81 160 66 192 448), lower := (rows 7 35 268 56 81 160 66 128 256), losses := [] }

theorem u1356 : Upper (D 7) (R 7) [6,33,264,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1356 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,0),(3,0),(3,1),(4,5)], upper := (rows 7 35 268 56 81 160 192 194 322), lower := (rows 7 35 268 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 243 243 131 259), good := (rows 486 482 268 124 508 224 224 224 256) },{ target := 1, region := (rows 1 0 4 26 18 224 224 128 256), good := (rows 29 121 268 120 121 224 224 224 256) }] }

theorem u1357 : Upper (D 7) (R 7) [6,33,264,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1357 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 268 56 82 160 65 192 448), lower := (rows 7 35 268 56 82 160 65 128 256), losses := [] }

theorem u1358 : Upper (D 7) (R 7) [6,33,264,48,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1358 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(2,1),(3,0),(4,0),(4,5)], upper := (rows 7 35 268 56 82 160 192 193 321), lower := (rows 7 35 268 56 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 224 224 128 256), good := (rows 30 122 268 120 122 224 224 224 256) },{ target := 1, region := (rows 1 0 20 24 16 243 243 131 259), good := (rows 485 481 268 124 508 224 224 224 256) }] }

theorem u1359 : Upper (D 7) (R 7) [6,33,264,48,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1359 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 35 268 73 82 160 80 160 416), lower := (rows 7 35 268 73 82 160 80 128 256), losses := [] }

theorem u1360 : Upper (D 7) (R 7) [6,33,264,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1360 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,5),(2,5),(3,5),(3,7)], upper := (rows 7 35 268 73 82 160 96 144 400), lower := (rows 7 35 268 73 82 160 96 128 256), losses := [] }

theorem u1361 : Upper (D 7) (R 7) [6,33,264,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 7 35 268 73 82 160 192 176 304), lower := (rows 7 35 268 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 255 255 155 283), good := (rows 502 498 492 508 498 224 224 224 256) },{ target := 1, region := (rows 1 0 20 10 16 240 240 144 272), good := (rows 13 105 268 105 508 224 224 224 256) }] }

theorem u1362 : Upper (D 7) (R 7) [6,33,264,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1363 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 268 73 112 160 66 144 400), lower := (rows 7 35 268 73 112 160 66 128 256), losses := [] }

theorem u1363 : Upper (D 7) (R 7) [6,33,264,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1363 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1364 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 73 112 160 80 130 386), lower := (rows 7 35 268 73 112 160 80 128 256), losses := [] }

theorem u1364 : Upper (D 7) (R 7) [6,33,264,65,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1364 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 73 112 160 192 146 274), lower := (rows 7 35 268 73 112 160 192 128 256), losses := [] }

theorem u1365 : Upper (D 7) (R 7) [6,33,264,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 420, targets := 3 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 268 73 146 160 80 224 352), lower := (rows 7 35 268 73 146 160 80 128 256), losses := [] }

theorem u1366 : Upper (D 7) (R 7) [6,33,264,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1366 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 240, targets := 1 },{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(2,0),(3,1),(3,7),(4,0)], upper := (rows 7 35 268 73 146 160 96 208 336), lower := (rows 7 35 268 73 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 191 255 155 283), good := (rows 502 498 492 508 498 224 96 224 256) }] }

theorem u1367 : Upper (D 7) (R 7) [6,33,264,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 268 73 208 48 66 160 416), lower := (rows 7 35 268 73 208 48 66 128 256), losses := [] }

theorem u1368 : Upper (D 7) (R 7) [6,33,264,65,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1368 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 130, camps := [{ cop := 7, region := 112, targets := 3 },{ cop := 1, region := 72, targets := 2 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 7 35 268 73 208 48 96 130 386), lower := (rows 7 35 268 73 208 48 96 128 256), losses := [] }

theorem u1369 : Upper (D 7) (R 7) [6,33,264,65,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1369 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 268 73 208 48 192 162 290), lower := (rows 7 35 268 73 208 48 192 128 256), losses := [] }

theorem u1370 : Upper (D 7) (R 7) [6,33,264,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1371 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 268 73 208 160 66 176 304), lower := (rows 7 35 268 73 208 160 66 128 256), losses := [] }

theorem u1371 : Upper (D 7) (R 7) [6,33,264,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1372 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 35 268 73 208 160 80 162 290), lower := (rows 7 35 268 73 208 160 80 128 256), losses := [] }

theorem u1372 : Upper (D 7) (R 7) [6,33,264,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1372 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1373 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 80, targets := 3 },{ cop := 1, region := 72, targets := 2 },{ cop := 1, region := 72, targets := 128 }], pairs := [(3,1),(3,7),(4,0),(4,1)], upper := (rows 7 35 268 73 208 160 96 146 274), lower := (rows 7 35 268 73 208 160 96 128 256), losses := [] }

theorem u1373 : Upper (D 7) (R 7) [6,33,264,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 35 268 74 81 160 80 160 416), lower := (rows 7 35 268 74 81 160 80 128 256), losses := [] }

theorem u1374 : Upper (D 7) (R 7) [6,33,264,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1374 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 405, targets := 32 },{ cop := 1, region := 72, targets := 128 }], pairs := [(0,5),(2,5),(3,7),(4,5)], upper := (rows 7 35 268 74 81 160 96 144 400), lower := (rows 7 35 268 74 81 160 96 128 256), losses := [] }

theorem u1375 : Upper (D 7) (R 7) [6,33,264,66,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 240, targets := 2 },{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6),(2,1),(3,0),(4,1)], upper := (rows 7 35 268 74 81 160 192 176 304), lower := (rows 7 35 268 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 240 240 144 272), good := (rows 14 106 268 106 496 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 19 255 255 155 283), good := (rows 501 497 492 508 497 224 224 224 256) }] }

theorem u1376 : Upper (D 7) (R 7) [6,33,264,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 35 268 74 112 160 65 144 400), lower := (rows 7 35 268 74 112 160 65 128 256), losses := [] }

theorem u1377 : Upper (D 7) (R 7) [6,33,264,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0)], upper := (rows 7 35 268 74 112 160 80 129 385), lower := (rows 7 35 268 74 112 160 80 128 256), losses := [] }

theorem u1378 : Upper (D 7) (R 7) [6,33,264,66,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1378 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 35 268 74 112 160 192 145 273), lower := (rows 7 35 268 74 112 160 192 128 256), losses := [] }

theorem u1379 : Upper (D 7) (R 7) [6,33,264,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P07
