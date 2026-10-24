import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0001

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1200 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 100 265 208 48 225 161 417), lower := (rows 7 42 100 265 208 48 64 128 256), losses := [] }

theorem u1200 : Upper (D 8) (R 8) [6,40,96,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1200 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1201 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 265 208 160 113 177 305), lower := (rows 7 42 100 265 208 160 64 128 256), losses := [] }

theorem u1201 : Upper (D 8) (R 8) [6,40,96,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1202 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 280 145 33 224 224 480), lower := (rows 7 42 100 280 145 33 64 128 256), losses := [] }

theorem u1202 : Upper (D 8) (R 8) [6,40,96,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1203 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 280 145 96 225 161 417), lower := (rows 7 42 100 280 145 96 64 128 256), losses := [] }

theorem u1203 : Upper (D 8) (R 8) [6,40,96,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1203 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1204 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 280 145 160 97 225 353), lower := (rows 7 42 100 280 145 160 64 128 256), losses := [] }

theorem u1204 : Upper (D 8) (R 8) [6,40,96,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1205 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 42 100 280 176 33 193 193 449), lower := (rows 7 42 100 280 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 97 161 289), good := (rows 455 458 452 280 472 449 64 128 256) }] }

theorem u1205 : Upper (D 8) (R 8) [6,40,96,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1205 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1206 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 280 176 96 193 129 385), lower := (rows 7 42 100 280 176 96 64 128 256), losses := [] }

theorem u1206 : Upper (D 8) (R 8) [6,40,96,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1206 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1207 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 280 176 160 65 193 321), lower := (rows 7 42 100 280 176 160 64 128 256), losses := [] }

theorem u1207 : Upper (D 8) (R 8) [6,40,96,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1208 : Route 9 := (fun mask => (mask,id))

def c1208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1208 : Upper (D 8) (R 8) [6,40,96,272,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,192,1] 13 (by decide) (choices 1) [1,32,128] r1208 c1208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u90
  · exact u91
  · exact u92

def b1209 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 280 208 160 97 161 289), lower := (rows 7 42 100 280 208 160 64 128 256), losses := [] }

theorem u1209 : Upper (D 8) (R 8) [6,40,96,272,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1209 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1210 : Route 9 := (fun mask => (mask,id))

def c1210 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1210 : Upper (D 8) (R 8) [6,40,96,384,160,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,160,1] 13 (by decide) (choices 1) [1,16] r1210 c1210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u93
  · exact u94

def b1211 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 7 42 100 392 176 48 65 193 321), lower := (rows 7 42 100 392 176 48 64 128 256), losses := [] }

theorem u1211 : Upper (D 8) (R 8) [6,40,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1211 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1212 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 392 176 96 81 145 273), lower := (rows 7 42 100 392 176 96 64 128 256), losses := [] }

theorem u1212 : Upper (D 8) (R 8) [6,40,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1212 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1213 : Route 9 := (fun mask => (mask,id))

def c1213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1213 : Upper (D 8) (R 8) [6,40,96,384,192,1] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192,1] 13 (by decide) (choices 1) [1,16,32] r1213 c1213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u95
  · exact u96
  · exact u97

def b1214 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 42 100 392 208 48 97 161 289), lower := (rows 7 42 100 392 208 48 64 128 256), losses := [] }

theorem u1214 : Upper (D 8) (R 8) [6,40,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1214 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1215 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 196 25 304 33 224 224 480), lower := (rows 7 42 196 25 304 33 64 128 256), losses := [] }

theorem u1215 : Upper (D 8) (R 8) [6,40,192,17,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1216 : Route 9 := (fun mask => (mask,id))

def c1216 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1216 : Upper (D 8) (R 8) [6,40,192,17,288,64] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288,64] 13 (by decide) (choices 1) [1,32,128] r1216 c1216
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u98
  · exact u99
  · exact u100

def b1217 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 196 265 112 33 240 176 432), lower := (rows 7 42 196 265 112 33 64 128 256), losses := [] }

theorem u1217 : Upper (D 8) (R 8) [6,40,192,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1218 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 196 265 112 48 225 161 417), lower := (rows 7 42 196 265 112 48 64 128 256), losses := [] }

theorem u1218 : Upper (D 8) (R 8) [6,40,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1218 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1219 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 265 112 160 113 177 305), lower := (rows 7 42 196 265 112 160 64 128 256), losses := [] }

theorem u1219 : Upper (D 8) (R 8) [6,40,192,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1220 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 280 49 33 224 224 480), lower := (rows 7 42 196 280 49 33 64 128 256), losses := [] }

theorem u1220 : Upper (D 8) (R 8) [6,40,192,272,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1221 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 280 49 96 225 161 417), lower := (rows 7 42 196 280 49 96 64 128 256), losses := [] }

theorem u1221 : Upper (D 8) (R 8) [6,40,192,272,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1222 : PairBound 9 := { available := 161, camps := [], pairs := [(1,6)], upper := (rows 7 42 196 280 112 33 225 161 417), lower := (rows 7 42 196 280 112 33 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 33 0 161 289), good := (rows 423 426 132 282 442 417 0 128 256) }] }

theorem u1222 : Upper (D 8) (R 8) [6,40,192,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1223 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 280 112 160 97 161 289), lower := (rows 7 42 196 280 112 160 64 128 256), losses := [] }

theorem u1223 : Upper (D 8) (R 8) [6,40,192,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1224 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 88 176 33 224 224 480), lower := (rows 7 42 261 88 176 33 64 128 256), losses := [] }

theorem u1224 : Upper (D 8) (R 8) [6,40,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1225 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 176 96 225 161 417), lower := (rows 7 42 261 88 176 96 64 128 256), losses := [] }

theorem u1225 : Upper (D 8) (R 8) [6,40,257,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1226 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 88 176 160 97 225 353), lower := (rows 7 42 261 88 176 160 64 128 256), losses := [] }

theorem u1226 : Upper (D 8) (R 8) [6,40,257,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1227 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 200 112 33 240 176 432), lower := (rows 7 42 261 200 112 33 64 128 256), losses := [] }

theorem u1227 : Upper (D 8) (R 8) [6,40,257,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1228 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 261 200 112 48 225 161 417), lower := (rows 7 42 261 200 112 48 64 128 256), losses := [] }

theorem u1228 : Upper (D 8) (R 8) [6,40,257,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1228 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1229 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 261 200 112 160 113 177 305), lower := (rows 7 42 261 200 112 160 64 128 256), losses := [] }

theorem u1229 : Upper (D 8) (R 8) [6,40,257,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1229 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1230 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 276 73 176 33 224 224 480), lower := (rows 7 42 276 73 176 33 64 128 256), losses := [] }

theorem u1230 : Upper (D 8) (R 8) [6,40,272,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1231 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 276 73 176 96 225 161 417), lower := (rows 7 42 276 73 176 96 64 128 256), losses := [] }

theorem u1231 : Upper (D 8) (R 8) [6,40,272,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1232 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 276 73 176 160 97 225 353), lower := (rows 7 42 276 73 176 160 64 128 256), losses := [] }

theorem u1232 : Upper (D 8) (R 8) [6,40,272,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1233 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 276 200 49 33 224 224 480), lower := (rows 7 42 276 200 49 33 64 128 256), losses := [] }

theorem u1233 : Upper (D 8) (R 8) [6,40,272,192,33,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1234 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 276 200 49 96 225 161 417), lower := (rows 7 42 276 200 49 96 64 128 256), losses := [] }

theorem u1234 : Upper (D 8) (R 8) [6,40,272,192,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1235 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 7 42 276 200 112 33 225 161 417), lower := (rows 7 42 276 200 112 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 8 16 33 0 161 289), good := (rows 423 426 276 136 436 417 0 128 256) }] }

theorem u1235 : Upper (D 8) (R 8) [6,40,272,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1236 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 276 200 112 160 97 161 289), lower := (rows 7 42 276 200 112 160 64 128 256), losses := [] }

theorem u1236 : Upper (D 8) (R 8) [6,40,272,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1237 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 25 112 33 192 192 448), lower := (rows 7 42 292 25 112 33 64 128 256), losses := [] }

theorem u1237 : Upper (D 8) (R 8) [6,40,288,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1238 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 399, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 25 112 96 193 129 385), lower := (rows 7 42 292 25 112 96 64 128 256), losses := [] }

theorem u1238 : Upper (D 8) (R 8) [6,40,288,17,96,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1239 : Route 9 := (fun mask => (mask,id))

def c1239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1239 : Upper (D 8) (R 8) [6,40,288,17,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,96,128] 13 (by decide) (choices 1) [1,128] r1239 c1239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u101
  · exact u102

def b1240 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 25 208 33 224 224 480), lower := (rows 7 42 292 25 208 33 64 128 256), losses := [] }

theorem u1240 : Upper (D 8) (R 8) [6,40,288,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1241 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 25 208 96 225 161 417), lower := (rows 7 42 292 25 208 96 64 128 256), losses := [] }

theorem u1241 : Upper (D 8) (R 8) [6,40,288,17,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1242 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 73 112 33 208 144 400), lower := (rows 7 42 292 73 112 33 64 128 256), losses := [] }

theorem u1242 : Upper (D 8) (R 8) [6,40,288,65,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1242 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1243 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 292 73 112 48 193 129 385), lower := (rows 7 42 292 73 112 48 64 128 256), losses := [] }

theorem u1243 : Upper (D 8) (R 8) [6,40,288,65,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1243 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1244 : Route 9 := (fun mask => (mask,id))

def c1244 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1244 : Upper (D 8) (R 8) [6,40,288,65,96,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,96,128] 13 (by decide) (choices 1) [1,16,128] r1244 c1244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u103
  · exact u104
  · exact u105

def b1245 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 73 176 33 208 208 464), lower := (rows 7 42 292 73 176 33 64 128 256), losses := [] }

theorem u1245 : Upper (D 8) (R 8) [6,40,288,65,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1246 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 7 42 292 73 176 48 193 193 449), lower := (rows 7 42 292 73 176 48 64 128 256), losses := [] }

theorem u1246 : Upper (D 8) (R 8) [6,40,288,65,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1246 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1247 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 405, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 73 176 96 209 145 401), lower := (rows 7 42 292 73 176 96 64 128 256), losses := [] }

theorem u1247 : Upper (D 8) (R 8) [6,40,288,65,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1248 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 73 176 160 81 209 337), lower := (rows 7 42 292 73 176 160 64 128 256), losses := [] }

theorem u1248 : Upper (D 8) (R 8) [6,40,288,65,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1249 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 73 208 33 240 176 432), lower := (rows 7 42 292 73 208 33 64 128 256), losses := [] }

theorem u1249 : Upper (D 8) (R 8) [6,40,288,65,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1250 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 42 292 73 208 48 225 161 417), lower := (rows 7 42 292 73 208 48 64 128 256), losses := [] }

theorem u1250 : Upper (D 8) (R 8) [6,40,288,65,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1250 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1251 : Route 9 := (fun mask => (mask,id))

def c1251 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1251 : Upper (D 8) (R 8) [6,40,288,65,192,128] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,192,128] 13 (by decide) (choices 1) [1,16,32] r1251 c1251
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u106
  · exact u107
  · exact u108

def b1252 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 88 145 33 224 224 480), lower := (rows 7 42 292 88 145 33 64 128 256), losses := [] }

theorem u1252 : Upper (D 8) (R 8) [6,40,288,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1253 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 88 145 96 225 161 417), lower := (rows 7 42 292 88 145 96 64 128 256), losses := [] }

theorem u1253 : Upper (D 8) (R 8) [6,40,288,80,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1254 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 325, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 88 145 160 97 225 353), lower := (rows 7 42 292 88 145 160 64 128 256), losses := [] }

theorem u1254 : Upper (D 8) (R 8) [6,40,288,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1255 : PairBound 9 := { available := 193, camps := [], pairs := [(3,5)], upper := (rows 7 42 292 88 176 33 193 193 449), lower := (rows 7 42 292 88 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 97 161 289), good := (rows 455 458 452 88 472 449 64 128 256) }] }

theorem u1255 : Upper (D 8) (R 8) [6,40,288,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1256 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 88 176 96 193 129 385), lower := (rows 7 42 292 88 176 96 64 128 256), losses := [] }

theorem u1256 : Upper (D 8) (R 8) [6,40,288,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1257 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 292 88 176 160 65 193 321), lower := (rows 7 42 292 88 176 160 64 128 256), losses := [] }

theorem u1257 : Upper (D 8) (R 8) [6,40,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1258 : Route 9 := (fun mask => (mask,id))

def c1258 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1258 : Upper (D 8) (R 8) [6,40,288,192,96,1] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192,96,1] 13 (by decide) (choices 1) [1,16,128] r1258 c1258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u109
  · exact u110
  · exact u111

def b1259 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 42 292 200 112 48 193 129 385), lower := (rows 7 42 292 200 112 48 64 128 256), losses := [] }

theorem u1259 : Upper (D 8) (R 8) [6,40,288,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1259 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1259
end Delivery.IrregularNine14.P08
