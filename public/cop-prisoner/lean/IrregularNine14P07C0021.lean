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

def b1260 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 296 208 48 65 130 386), lower := (rows 7 35 76 296 208 48 65 128 256), losses := [] }

theorem u1260 : Upper (D 7) (R 7) [6,33,72,288,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1260 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1261 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 296 208 48 66 129 385), lower := (rows 7 35 76 296 208 48 66 128 256), losses := [] }

theorem u1261 : Upper (D 7) (R 7) [6,33,72,288,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1261 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1262 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 76 296 208 48 192 131 259), lower := (rows 7 35 76 296 208 48 192 128 256), losses := [] }

theorem u1262 : Upper (D 7) (R 7) [6,33,72,288,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1262 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1263 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 296 208 160 65 146 274), lower := (rows 7 35 76 296 208 160 65 128 256), losses := [] }

theorem u1263 : Upper (D 7) (R 7) [6,33,72,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1263 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1264 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 35 76 296 208 160 66 145 273), lower := (rows 7 35 76 296 208 160 66 128 256), losses := [] }

theorem u1264 : Upper (D 7) (R 7) [6,33,72,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1265 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 296 208 160 80 131 259), lower := (rows 7 35 76 296 208 160 80 128 256), losses := [] }

theorem u1265 : Upper (D 7) (R 7) [6,33,72,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1265 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1266 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 35 76 392 82 160 65 176 304), lower := (rows 7 35 76 392 82 160 65 128 256), losses := [] }

theorem u1266 : Upper (D 7) (R 7) [6,33,72,384,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1266 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1267 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 35 76 392 82 160 80 161 289), lower := (rows 7 35 76 392 82 160 80 128 256), losses := [] }

theorem u1267 : Upper (D 7) (R 7) [6,33,72,384,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1267 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1268 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(3,5)], upper := (rows 7 35 76 392 82 160 96 145 273), lower := (rows 7 35 76 392 82 160 96 128 256), losses := [] }

theorem u1268 : Upper (D 7) (R 7) [6,33,72,384,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1268 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1269 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 35 76 392 146 48 65 224 352), lower := (rows 7 35 76 392 146 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 77 17 115 64 196 324), good := (rows 446 58 492 392 178 48 508 128 256) }] }

theorem u1269 : Upper (D 7) (R 7) [6,33,72,384,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1269 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1270 : Route 9 := (fun mask => (mask,id))

def c1270 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1270 : Upper (D 7) (R 7) [6,33,72,384,130,16,32] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,130,16,32] 13 (by decide) (choices 1) [1,64] r1270 c1270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u38
  · exact u39

def b1271 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 392, targets := 65 }], pairs := [(2,0),(3,0),(3,6)], upper := (rows 7 35 76 392 208 48 65 162 290), lower := (rows 7 35 76 392 208 48 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 75 80 116 64 131 259), good := (rows 430 426 124 392 252 52 508 128 256) }] }

theorem u1271 : Upper (D 7) (R 7) [6,33,72,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1271 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1272 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 392, targets := 2 },{ cop := 1, region := 392, targets := 64 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 7 35 76 392 208 48 66 161 289), lower := (rows 7 35 76 392 208 48 66 128 256), losses := [{ target := 1, region := (rows 1 0 84 75 80 116 64 131 259), good := (rows 429 425 124 392 252 52 508 128 256) }] }

theorem u1272 : Upper (D 7) (R 7) [6,33,72,384,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1272 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1273 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 116, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 392 208 48 96 131 259), lower := (rows 7 35 76 392 208 48 96 128 256), losses := [] }

theorem u1273 : Upper (D 7) (R 7) [6,33,72,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1273 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1274 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 1, region := 80, targets := 1 }], pairs := [(3,7),(4,0),(4,7)], upper := (rows 7 35 196 25 112 288 66 136 392), lower := (rows 7 35 196 25 112 288 66 128 256), losses := [] }

theorem u1274 : Upper (D 7) (R 7) [6,33,192,17,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1274 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1275 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 88, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 25 112 288 72 130 386), lower := (rows 7 35 196 25 112 288 72 128 256), losses := [] }

theorem u1275 : Upper (D 7) (R 7) [6,33,192,17,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1275 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1276 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 25 112 288 192 138 266), lower := (rows 7 35 196 25 112 288 192 128 256), losses := [] }

theorem u1276 : Upper (D 7) (R 7) [6,33,192,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1276 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1277 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 88, targets := 128 },{ cop := 3, region := 197, targets := 32 }], pairs := [(0,5),(3,7),(4,7)], upper := (rows 7 35 196 26 112 288 65 136 392), lower := (rows 7 35 196 26 112 288 65 128 256), losses := [] }

theorem u1277 : Upper (D 7) (R 7) [6,33,192,18,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1277 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1278 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7)], upper := (rows 7 35 196 26 112 288 72 129 385), lower := (rows 7 35 196 26 112 288 72 128 256), losses := [] }

theorem u1278 : Upper (D 7) (R 7) [6,33,192,18,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1278 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1279 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 26 112 288 192 137 265), lower := (rows 7 35 196 26 112 288 192 128 256), losses := [] }

theorem u1279 : Upper (D 7) (R 7) [6,33,192,18,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1279 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1280 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 468, targets := 2 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 7 35 196 26 336 40 65 160 416), lower := (rows 7 35 196 26 336 40 65 128 256), losses := [{ target := 0, region := (rows 0 2 84 9 84 107 64 255 383), good := (rows 446 426 500 446 500 424 508 128 256) }] }

theorem u1280 : Upper (D 7) (R 7) [6,33,192,18,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1280 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1281 : Route 9 := (fun mask => (mask,id))

def c1281 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1281 : Upper (D 7) (R 7) [6,33,192,18,320,8,32] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,320,8,32] 13 (by decide) (choices 1) [1] r1281 c1281
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u40

def b1282 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 26 336 40 192 161 289), lower := (rows 7 35 196 26 336 40 192 128 256), losses := [] }

theorem u1282 : Upper (D 7) (R 7) [6,33,192,18,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1282 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1283 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 196 56 81 288 66 136 392), lower := (rows 7 35 196 56 81 288 66 128 256), losses := [] }

theorem u1283 : Upper (D 7) (R 7) [6,33,192,48,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1283 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1284 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 88, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 56 81 288 72 130 386), lower := (rows 7 35 196 56 81 288 72 128 256), losses := [] }

theorem u1284 : Upper (D 7) (R 7) [6,33,192,48,65,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1284 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1285 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 56 81 288 192 138 266), lower := (rows 7 35 196 56 81 288 192 128 256), losses := [] }

theorem u1285 : Upper (D 7) (R 7) [6,33,192,48,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1285 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1286 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 196 56 82 288 65 136 392), lower := (rows 7 35 196 56 82 288 65 128 256), losses := [] }

theorem u1286 : Upper (D 7) (R 7) [6,33,192,48,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1286 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1287 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 88, targets := 129 }], pairs := [(3,0),(3,7)], upper := (rows 7 35 196 56 82 288 72 129 385), lower := (rows 7 35 196 56 82 288 72 128 256), losses := [] }

theorem u1287 : Upper (D 7) (R 7) [6,33,192,48,66,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1287 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1288 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 56 82 288 192 137 265), lower := (rows 7 35 196 56 82 288 192 128 256), losses := [] }

theorem u1288 : Upper (D 7) (R 7) [6,33,192,48,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1288 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1289 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 196 73 146 288 72 176 304), lower := (rows 7 35 196 73 146 288 72 128 256), losses := [] }

theorem u1289 : Upper (D 7) (R 7) [6,33,192,65,130,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1289 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1290 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 73 146 288 80 168 296), lower := (rows 7 35 196 73 146 288 80 128 256), losses := [] }

theorem u1290 : Upper (D 7) (R 7) [6,33,192,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1290 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1291 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 7 35 196 73 146 288 96 152 280), lower := (rows 7 35 196 73 146 288 96 128 256), losses := [] }

theorem u1291 : Upper (D 7) (R 7) [6,33,192,65,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1291 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1292 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 73 152 288 66 176 304), lower := (rows 7 35 196 73 152 288 66 128 256), losses := [] }

theorem u1292 : Upper (D 7) (R 7) [6,33,192,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1292 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1293 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 73 152 288 80 162 290), lower := (rows 7 35 196 73 152 288 80 128 256), losses := [] }

theorem u1293 : Upper (D 7) (R 7) [6,33,192,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1293 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1294 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 1, region := 72, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 7 35 196 73 152 288 96 146 274), lower := (rows 7 35 196 73 152 288 96 128 256), losses := [] }

theorem u1294 : Upper (D 7) (R 7) [6,33,192,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1294 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1295 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 73 176 288 66 152 280), lower := (rows 7 35 196 73 176 288 66 128 256), losses := [] }

theorem u1295 : Upper (D 7) (R 7) [6,33,192,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1295 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1296 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 35 196 73 176 288 72 146 274), lower := (rows 7 35 196 73 176 288 72 128 256), losses := [] }

theorem u1296 : Upper (D 7) (R 7) [6,33,192,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1296 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1297 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 73 176 288 80 138 266), lower := (rows 7 35 196 73 176 288 80 128 256), losses := [] }

theorem u1297 : Upper (D 7) (R 7) [6,33,192,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1297 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1298 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 74 152 288 65 176 304), lower := (rows 7 35 196 74 152 288 65 128 256), losses := [] }

theorem u1298 : Upper (D 7) (R 7) [6,33,192,66,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1298 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1299 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 74 152 288 80 161 289), lower := (rows 7 35 196 74 152 288 80 128 256), losses := [] }

theorem u1299 : Upper (D 7) (R 7) [6,33,192,66,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1299 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1300 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 149, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 196 74 152 288 96 145 273), lower := (rows 7 35 196 74 152 288 96 128 256), losses := [] }

theorem u1300 : Upper (D 7) (R 7) [6,33,192,66,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1300 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1301 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 74 176 288 65 152 280), lower := (rows 7 35 196 74 176 288 65 128 256), losses := [] }

theorem u1301 : Upper (D 7) (R 7) [6,33,192,66,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1301 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1302 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 7 35 196 74 176 288 72 145 273), lower := (rows 7 35 196 74 176 288 72 128 256), losses := [] }

theorem u1302 : Upper (D 7) (R 7) [6,33,192,66,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1302 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1303 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 74 176 288 80 137 265), lower := (rows 7 35 196 74 176 288 80 128 256), losses := [] }

theorem u1303 : Upper (D 7) (R 7) [6,33,192,66,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1303 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1304 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 436, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 196 74 400 48 65 168 296), lower := (rows 7 35 196 74 400 48 65 128 256), losses := [] }

theorem u1304 : Upper (D 7) (R 7) [6,33,192,66,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1304 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1305 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 74 400 48 72 161 289), lower := (rows 7 35 196 74 400 48 72 128 256), losses := [] }

theorem u1305 : Upper (D 7) (R 7) [6,33,192,66,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1305 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1306 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 35 196 74 400 48 96 137 265), lower := (rows 7 35 196 74 400 48 96 128 256), losses := [] }

theorem u1306 : Upper (D 7) (R 7) [6,33,192,66,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1306 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1307 : PairBound 9 := { available := 10, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 176 288 65 138 266), lower := (rows 7 35 196 88 176 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 87 355 64 129 257), good := (rows 446 434 252 124 176 288 508 128 288) }] }

theorem u1307 : Upper (D 7) (R 7) [6,33,192,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1307 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1308 : Route 9 := (fun mask => (mask,id))

def c1308 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1308 : Upper (D 7) (R 7) [6,33,192,80,160,256,2] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160,256,2] 13 (by decide) (choices 1) [1,8] r1308 c1308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u41
  · exact u42

def b1309 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 76, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 88 176 288 72 131 259), lower := (rows 7 35 196 88 176 288 72 128 256), losses := [] }

theorem u1309 : Upper (D 7) (R 7) [6,33,192,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1309 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1310 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,0),(2,1)], upper := (rows 7 35 196 88 273 40 66 160 416), lower := (rows 7 35 196 88 273 40 66 128 256), losses := [] }

theorem u1310 : Upper (D 7) (R 7) [6,33,192,80,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1310 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1311 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0),(4,5),(4,6)], upper := (rows 7 35 196 88 273 40 96 130 386), lower := (rows 7 35 196 88 273 40 96 128 256), losses := [] }

theorem u1311 : Upper (D 7) (R 7) [6,33,192,80,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1311 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1312 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 88 273 40 192 162 290), lower := (rows 7 35 196 88 273 40 192 128 256), losses := [] }

theorem u1312 : Upper (D 7) (R 7) [6,33,192,80,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1312 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1313 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(2,0),(4,0),(4,6)], upper := (rows 7 35 196 88 400 40 65 162 290), lower := (rows 7 35 196 88 400 40 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 76 83 109 64 131 259), good := (rows 446 434 252 124 400 40 508 128 256) }] }

theorem u1313 : Upper (D 7) (R 7) [6,33,192,80,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1313 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1314 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 400, targets := 2 },{ cop := 1, region := 400, targets := 64 }], pairs := [(2,1),(4,1),(4,6)], upper := (rows 7 35 196 88 400 40 66 161 289), lower := (rows 7 35 196 88 400 40 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 76 83 109 64 131 259), good := (rows 445 433 252 124 400 40 508 128 256) }] }

theorem u1314 : Upper (D 7) (R 7) [6,33,192,80,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1314 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1315 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 196 88 400 40 96 131 259), lower := (rows 7 35 196 88 400 40 96 128 256), losses := [] }

theorem u1315 : Upper (D 7) (R 7) [6,33,192,80,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1315 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1316 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 132, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 196 104 274 48 65 136 392), lower := (rows 7 35 196 104 274 48 65 128 256), losses := [] }

theorem u1316 : Upper (D 7) (R 7) [6,33,192,96,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1317 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 196 104 274 48 72 129 385), lower := (rows 7 35 196 104 274 48 72 128 256), losses := [] }

theorem u1317 : Upper (D 7) (R 7) [6,33,192,96,258,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1317 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1318 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 104 274 48 192 137 265), lower := (rows 7 35 196 104 274 48 192 128 256), losses := [] }

theorem u1318 : Upper (D 7) (R 7) [6,33,192,96,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1318 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1319 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 1, region := 72, targets := 2 }], pairs := [(0,5),(2,5),(3,1)], upper := (rows 7 35 196 104 280 48 65 130 386), lower := (rows 7 35 196 104 280 48 65 128 256), losses := [] }

theorem u1319 : Upper (D 7) (R 7) [6,33,192,96,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1319 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1319
end Delivery.IrregularNine14.P07
