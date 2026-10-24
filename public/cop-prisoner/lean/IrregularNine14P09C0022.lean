import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000
import IrregularNine14P09C0001

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1320 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 297, targets := 128 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(0,7),(3,7),(4,5),(4,6)], upper := (rows 35 70 28 104 145 288 192 385 257), lower := (rows 35 70 28 104 145 288 192 128 256), losses := [] }

theorem u1320 : Upper (D 9) (R 9) [34,68,24,96,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1320 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1321 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 70 28 104 145 288 320 129 385), lower := (rows 35 70 28 104 145 288 320 128 256), losses := [] }

theorem u1321 : Upper (D 9) (R 9) [34,68,24,96,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1321 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1322 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 28 104 400 160 65 385 257), lower := (rows 35 70 28 104 400 160 65 128 256), losses := [] }

theorem u1322 : Upper (D 9) (R 9) [34,68,24,96,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1322 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1323 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,0),(4,6)], upper := (rows 35 70 28 104 400 160 320 129 257), lower := (rows 35 70 28 104 400 160 320 128 256), losses := [] }

theorem u1323 : Upper (D 9) (R 9) [34,68,24,96,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1323 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1324 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 28 137 176 288 65 448 320), lower := (rows 35 70 28 137 176 288 65 128 256), losses := [] }

theorem u1324 : Upper (D 9) (R 9) [34,68,24,129,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1324 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1325 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(1,7),(3,5)], upper := (rows 35 70 28 137 176 288 320 193 321), lower := (rows 35 70 28 137 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 16 0 365 137 265), good := (rows 459 70 478 457 208 320 320 128 320) },{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 28 137 176 288 288 128 288) }] }

theorem u1325 : Upper (D 9) (R 9) [34,68,24,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1325 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1326 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(4,5)], upper := (rows 35 70 28 137 208 288 65 416 288), lower := (rows 35 70 28 137 208 288 65 128 256), losses := [] }

theorem u1326 : Upper (D 9) (R 9) [34,68,24,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1326 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1327 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 392, targets := 32 }], pairs := [(0,6),(0,7),(1,7),(3,5),(3,6)], upper := (rows 35 70 28 137 208 288 96 385 257), lower := (rows 35 70 28 137 208 288 96 128 256), losses := [] }

theorem u1327 : Upper (D 9) (R 9) [34,68,24,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1327 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1328 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 136, targets := 256 }], pairs := [(0,6),(0,7),(1,7),(3,6),(3,8)], upper := (rows 35 70 28 137 208 288 320 161 289), lower := (rows 35 70 28 137 208 288 320 128 256), losses := [] }

theorem u1328 : Upper (D 9) (R 9) [34,68,24,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1328 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1329 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5),(4,7)], upper := (rows 35 70 28 137 273 160 96 448 320), lower := (rows 35 70 28 137 273 160 96 128 256), losses := [{ target := 5, region := (rows 1 2 29 9 17 0 64 194 322), good := (rows 415 454 28 157 285 128 448 128 256) }] }

theorem u1329 : Upper (D 9) (R 9) [34,68,24,129,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1329 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1330 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 169, targets := 256 },{ cop := 0, region := 336, targets := 128 },{ cop := 2, region := 482, targets := 1 }], pairs := [(0,8),(1,0),(1,5),(3,8),(4,7)], upper := (rows 35 70 28 137 273 160 320 224 352), lower := (rows 35 70 28 137 273 160 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 336 128 256), good := (rows 3 70 94 137 337 128 320 128 320) }] }

theorem u1330 : Upper (D 9) (R 9) [34,68,24,129,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1330 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1331 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 136, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,6),(1,5),(3,6),(3,8),(4,0)], upper := (rows 35 70 28 137 336 288 65 160 416), lower := (rows 35 70 28 137 336 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 73 128 256), good := (rows 67 70 94 201 336 256 65 128 256) }] }

theorem u1331 : Upper (D 9) (R 9) [34,68,24,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1331 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1332 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 5, region := 80, targets := 129 },{ cop := 0, region := 136, targets := 32 }], pairs := [(0,6),(3,5),(3,6),(4,0),(4,7)], upper := (rows 35 70 28 137 336 288 96 129 385), lower := (rows 35 70 28 137 336 288 96 128 256), losses := [] }

theorem u1332 : Upper (D 9) (R 9) [34,68,24,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1332 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1333 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 1, region := 305, targets := 128 },{ cop := 0, region := 136, targets := 256 }], pairs := [(0,6),(0,7),(3,6),(3,8),(4,7)], upper := (rows 35 70 28 137 336 288 192 161 289), lower := (rows 35 70 28 137 336 288 192 128 256), losses := [] }

theorem u1333 : Upper (D 9) (R 9) [34,68,24,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1333 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1334 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 200, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,8),(4,0)], upper := (rows 35 70 28 137 400 288 65 224 352), lower := (rows 35 70 28 137 400 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 83 371 64 194 322), good := (rows 434 502 60 188 432 288 496 128 288) }] }

theorem u1334 : Upper (D 9) (R 9) [34,68,24,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1334 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1335 : Route 9 := (fun mask => (mask,id))

def c1335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1335 : Upper (D 9) (R 9) [34,68,24,129,384,256,32] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,384,256,32] 13 (by decide) (choices 1) [1,64] r1335 c1335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u54
  · exact u55

def b1336 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 136, targets := 256 }], pairs := [(0,6),(2,6),(3,6),(3,8),(4,5)], upper := (rows 35 70 28 168 336 288 65 129 385), lower := (rows 35 70 28 168 336 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 20 91 16 371 0 195 323), good := (rows 427 431 60 168 444 288 425 128 288) }] }

theorem u1336 : Upper (D 9) (R 9) [34,68,24,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1336 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1337 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 425, targets := 64 },{ cop := 1, region := 305, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(0,7),(3,6),(4,5),(4,7)], upper := (rows 35 70 28 168 336 288 192 129 257), lower := (rows 35 70 28 168 336 288 192 128 256), losses := [] }

theorem u1337 : Upper (D 9) (R 9) [34,68,24,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1337 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1338 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 44 137 208 288 65 400 272), lower := (rows 35 70 44 137 208 288 65 128 256), losses := [] }

theorem u1338 : Upper (D 9) (R 9) [34,68,40,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1338 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1339 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(0,6),(2,6),(3,6),(4,0)], upper := (rows 35 70 44 137 208 288 80 385 257), lower := (rows 35 70 44 137 208 288 80 128 256), losses := [] }

theorem u1339 : Upper (D 9) (R 9) [34,68,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1339 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1340 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(1,0),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 137 208 288 320 145 273), lower := (rows 35 70 44 137 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 352 352 128 256), good := (rows 98 102 110 136 240 352 352 128 352) },{ target := 5, region := (rows 1 6 4 9 29 0 365 137 265), good := (rows 475 86 478 473 208 320 320 128 320) },{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 44 137 176 288 288 128 288) }] }

theorem u1340 : Upper (D 9) (R 9) [34,68,40,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1340 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1341 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 200, targets := 256 }], pairs := [(2,0),(3,5),(3,8),(4,5)], upper := (rows 35 70 44 137 273 288 80 192 448), lower := (rows 35 70 44 137 273 288 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 371 80 210 338), good := (rows 418 486 44 172 496 288 496 128 288) }] }

theorem u1341 : Upper (D 9) (R 9) [34,68,40,129,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1341 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1342 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 305, targets := 128 },{ cop := 4, region := 200, targets := 256 }], pairs := [(0,7),(3,5),(3,8),(4,5),(4,7)], upper := (rows 35 70 44 137 273 288 192 208 336), lower := (rows 35 70 44 137 273 288 192 128 256), losses := [] }

theorem u1342 : Upper (D 9) (R 9) [34,68,40,129,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1342 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1343 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 44 137 336 288 65 144 400), lower := (rows 35 70 44 137 336 288 65 128 256), losses := [] }

theorem u1343 : Upper (D 9) (R 9) [34,68,40,129,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1343 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1344 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 },{ cop := 0, region := 136, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(3,6)], upper := (rows 35 70 44 137 336 288 80 129 385), lower := (rows 35 70 44 137 336 288 80 128 256), losses := [] }

theorem u1344 : Upper (D 9) (R 9) [34,68,40,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1344 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1345 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 305, targets := 128 }], pairs := [(0,7),(1,0),(3,5),(4,5),(4,7)], upper := (rows 35 70 44 137 336 288 192 145 273), lower := (rows 35 70 44 137 336 288 192 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 304 200 128 256), good := (rows 34 70 110 200 368 288 192 192 288) }] }

theorem u1345 : Upper (D 9) (R 9) [34,68,40,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1345 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1346 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 44 137 400 288 65 208 336), lower := (rows 35 70 44 137 400 288 65 128 256), losses := [] }

theorem u1346 : Upper (D 9) (R 9) [34,68,40,129,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1346 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1347 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7),(1,5),(3,5),(4,5)], upper := (rows 35 70 44 137 400 288 80 193 321), lower := (rows 35 70 44 137 400 288 80 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 29 0 95 137 265), good := (rows 475 86 478 473 464 256 80 128 256) }] }

theorem u1347 : Upper (D 9) (R 9) [34,68,40,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1347 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1348 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 44 200 145 288 65 400 272), lower := (rows 35 70 44 200 145 288 65 128 256), losses := [] }

theorem u1348 : Upper (D 9) (R 9) [34,68,40,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1348 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1349 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 35 70 44 200 145 288 80 385 257), lower := (rows 35 70 44 200 145 288 80 128 256), losses := [] }

theorem u1349 : Upper (D 9) (R 9) [34,68,40,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1349 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1350 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(3,5),(4,5),(4,6),(4,8)], upper := (rows 35 70 44 200 145 288 320 145 273), lower := (rows 35 70 44 200 145 288 320 128 256), losses := [] }

theorem u1350 : Upper (D 9) (R 9) [34,68,40,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1350 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1351 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 35 70 44 200 400 288 65 145 273), lower := (rows 35 70 44 200 400 288 65 128 256), losses := [] }

theorem u1351 : Upper (D 9) (R 9) [34,68,40,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1351 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1352 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 110, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 35 70 44 200 400 288 80 129 257), lower := (rows 35 70 44 200 400 288 80 128 256), losses := [] }

theorem u1352 : Upper (D 9) (R 9) [34,68,40,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1352 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1353 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 70 133 25 88 288 96 384 384), lower := (rows 35 70 133 25 88 288 96 128 256), losses := [] }

theorem u1353 : Upper (D 9) (R 9) [34,68,129,17,72,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1353 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1354 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 90, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 133 25 88 288 192 416 288), lower := (rows 35 70 133 25 88 288 192 128 256), losses := [] }

theorem u1354 : Upper (D 9) (R 9) [34,68,129,17,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1354 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1355 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 132, targets := 256 },{ cop := 2, region := 354, targets := 1 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(2,8),(4,0)], upper := (rows 35 70 133 25 88 288 320 160 416), lower := (rows 35 70 133 25 88 288 320 128 256), losses := [] }

theorem u1355 : Upper (D 9) (R 9) [34,68,129,17,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1355 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1356 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 }], pairs := [(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 70 133 25 112 288 72 384 384), lower := (rows 35 70 133 25 112 288 72 128 256), losses := [] }

theorem u1356 : Upper (D 9) (R 9) [34,68,129,17,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1356 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1357 : PairBound 9 := { available := 264, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 25 112 288 192 392 264), lower := (rows 35 70 133 25 112 288 192 128 256), losses := [] }

theorem u1357 : Upper (D 9) (R 9) [34,68,129,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1357 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1358 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 454, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 25 112 288 320 136 392), lower := (rows 35 70 133 25 112 288 320 128 256), losses := [] }

theorem u1358 : Upper (D 9) (R 9) [34,68,129,17,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1358 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1359 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 25 176 288 72 448 320), lower := (rows 35 70 133 25 176 288 72 128 256), losses := [] }

theorem u1359 : Upper (D 9) (R 9) [34,68,129,17,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1359 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1360 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 454, targets := 32 },{ cop := 3, region := 496, targets := 1 }], pairs := [(0,6),(0,7),(1,5),(2,5),(4,0)], upper := (rows 35 70 133 25 176 288 320 200 328), lower := (rows 35 70 133 25 176 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 352 0 128 256), good := (rows 35 39 133 25 176 288 288 128 288) },{ target := 7, region := (rows 3 2 4 8 16 360 360 0 264), good := (rows 99 103 5 377 112 352 352 0 352) }] }

theorem u1360 : Upper (D 9) (R 9) [34,68,129,17,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1360 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1361 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 90, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 70 133 25 208 288 72 416 288), lower := (rows 35 70 133 25 208 288 72 128 256), losses := [] }

theorem u1361 : Upper (D 9) (R 9) [34,68,129,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1361 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1362 : PairBound 9 := { available := 264, camps := [{ cop := 3, region := 496, targets := 1 },{ cop := 3, region := 388, targets := 32 },{ cop := 3, region := 388, targets := 64 }], pairs := [(1,0),(2,5),(2,6),(3,5),(4,0)], upper := (rows 35 70 133 25 208 288 96 392 264), lower := (rows 35 70 133 25 208 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 28 296 361 136 264), good := (rows 98 86 214 504 208 352 96 128 352) },{ target := 5, region := (rows 1 2 13 9 18 0 64 141 269), good := (rows 415 470 397 413 208 256 64 128 256) }] }

theorem u1362 : Upper (D 9) (R 9) [34,68,129,17,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1363 : Route 9 := (fun mask => (mask,id))

def c1363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1363 : Upper (D 9) (R 9) [34,68,129,17,192,256,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,192,256,256] 13 (by decide) (choices 1) [8,32] r1363 c1363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u56
  · exact u57

def b1364 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 388, targets := 96 },{ cop := 1, region := 400, targets := 33 }], pairs := [(2,5),(2,6),(4,0),(4,5)], upper := (rows 35 70 133 25 336 40 96 384 384), lower := (rows 35 70 133 25 336 40 96 128 256), losses := [] }

theorem u1364 : Upper (D 9) (R 9) [34,68,129,17,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1364 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1365 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(3,7),(4,7)], upper := (rows 35 70 133 25 336 40 192 416 288), lower := (rows 35 70 133 25 336 40 192 128 256), losses := [] }

theorem u1365 : Upper (D 9) (R 9) [34,68,129,17,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1365 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1366 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 25 336 40 320 160 416), lower := (rows 35 70 133 25 336 40 320 128 256), losses := [] }

theorem u1366 : Upper (D 9) (R 9) [34,68,129,17,320,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1366 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1367 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 132, targets := 256 },{ cop := 1, region := 432, targets := 1 }], pairs := [(0,6),(2,6),(2,8),(4,0)], upper := (rows 35 70 133 25 336 288 72 160 416), lower := (rows 35 70 133 25 336 288 72 128 256), losses := [] }

theorem u1367 : Upper (D 9) (R 9) [34,68,129,17,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1367 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1368 : PairBound 9 := { available := 136, camps := [{ cop := 5, region := 80, targets := 129 },{ cop := 3, region := 132, targets := 32 },{ cop := 3, region := 132, targets := 64 },{ cop := 3, region := 132, targets := 256 }], pairs := [(2,5),(2,6),(2,8),(4,0),(4,7)], upper := (rows 35 70 133 25 336 288 96 136 392), lower := (rows 35 70 133 25 336 288 96 128 256), losses := [] }

theorem u1368 : Upper (D 9) (R 9) [34,68,129,17,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1368 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1369 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 2, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7),(4,7)], upper := (rows 35 70 133 25 336 288 192 168 296), lower := (rows 35 70 133 25 336 288 192 128 256), losses := [] }

theorem u1369 : Upper (D 9) (R 9) [34,68,129,17,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1369 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1370 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 70 133 25 400 40 96 448 320), lower := (rows 35 70 133 25 400 40 96 128 256), losses := [] }

theorem u1370 : Upper (D 9) (R 9) [34,68,129,17,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1370 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1371 : Route 9 := (fun mask => (mask,id))

def c1371 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1371 : Upper (D 9) (R 9) [34,68,129,17,384,8,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384,8,256] 13 (by decide) (choices 1) [32,64] r1371 c1371
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u58
  · exact u59

def r1372 : Route 9 := (fun mask => (mask,id))

def c1372 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1372 : Upper (D 9) (R 9) [34,68,129,17,384,256,8] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384,256,8] 13 (by decide) (choices 1) [32,64] r1372 c1372
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u60
  · exact u61

def b1373 : PairBound 9 := { available := 72, camps := [{ cop := 3, region := 496, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,0),(4,5)], upper := (rows 35 70 133 25 400 288 96 200 328), lower := (rows 35 70 133 25 400 288 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 24 312 377 136 264), good := (rows 98 70 198 504 496 352 96 128 352) },{ target := 5, region := (rows 1 2 5 13 19 0 64 130 258), good := (rows 415 478 157 29 400 256 64 128 256) }] }

theorem u1373 : Upper (D 9) (R 9) [34,68,129,17,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1373 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1374 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 }], pairs := [(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 70 133 56 81 288 72 384 384), lower := (rows 35 70 133 56 81 288 72 128 256), losses := [] }

theorem u1374 : Upper (D 9) (R 9) [34,68,129,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1374 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1375 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 82, targets := 288 },{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(1,5),(1,8),(4,5),(4,8)], upper := (rows 35 70 133 56 81 288 192 392 264), lower := (rows 35 70 133 56 81 288 192 128 256), losses := [] }

theorem u1375 : Upper (D 9) (R 9) [34,68,129,48,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1375 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1376 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 64 },{ cop := 4, region := 424, targets := 1 }], pairs := [(0,6),(2,6),(3,0),(3,6),(4,5)], upper := (rows 35 70 133 56 81 288 320 136 392), lower := (rows 35 70 133 56 81 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 360 136 264), good := (rows 83 70 149 472 81 320 320 128 320) },{ target := 6, region := (rows 3 2 20 24 16 376 0 152 280), good := (rows 35 39 133 444 445 288 288 128 288) }] }

theorem u1376 : Upper (D 9) (R 9) [34,68,129,48,65,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1377 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 88, targets := 384 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,7),(3,8),(4,7),(4,8)], upper := (rows 35 70 133 56 88 288 65 384 384), lower := (rows 35 70 133 56 88 288 65 128 256), losses := [] }

theorem u1377 : Upper (D 9) (R 9) [34,68,129,48,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1377 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1378 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 454, targets := 32 }], pairs := [(0,7),(1,5),(2,5),(3,7),(4,7)], upper := (rows 35 70 133 56 88 288 192 385 257), lower := (rows 35 70 133 56 88 288 192 128 256), losses := [] }

theorem u1378 : Upper (D 9) (R 9) [34,68,129,48,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1378 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1379 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 133 56 88 288 320 129 385), lower := (rows 35 70 133 56 88 288 320 128 256), losses := [] }

theorem u1379 : Upper (D 9) (R 9) [34,68,129,48,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1379 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1379
end Delivery.IrregularNine14.P09
