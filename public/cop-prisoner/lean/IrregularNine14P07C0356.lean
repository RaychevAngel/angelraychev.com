import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0104

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r21360 : Route 9 := (fun mask => (mask,id))

def c21360 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21360 : Upper (D 7) (R 7) [34,260,66,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96,129,128] 13 (by decide) (choices 1) [1,8,16] r21360 c21360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6259
  · exact u6260
  · exact u6261

def b21361 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 104 152 33 209 145 401), lower := (rows 35 262 70 104 152 33 64 128 256), losses := [] }

theorem u21361 : Upper (D 7) (R 7) [34,260,66,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21361 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21362 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 262 70 104 152 48 193 129 385), lower := (rows 35 262 70 104 152 48 64 128 256), losses := [] }

theorem u21362 : Upper (D 7) (R 7) [34,260,66,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21362 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21363 : Route 9 := (fun mask => (mask,id))

def c21363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21363 : Upper (D 7) (R 7) [34,260,66,96,136,128] 13 := by
  apply FastRouting.sound _ _ [34,260,66,96,136,128] 13 (by decide) (choices 1) [1,16] r21363 c21363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6262
  · exact u6263

def b21364 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 137 176 33 88 216 344), lower := (rows 35 262 70 137 176 33 64 128 256), losses := [] }

theorem u21364 : Upper (D 7) (R 7) [34,260,66,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21365 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 70 137 176 40 81 209 337), lower := (rows 35 262 70 137 176 40 64 128 256), losses := [] }

theorem u21365 : Upper (D 7) (R 7) [34,260,66,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21365 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21366 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 70 137 176 48 73 201 329), lower := (rows 35 262 70 137 176 48 64 128 256), losses := [] }

theorem u21366 : Upper (D 7) (R 7) [34,260,66,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21366 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21367 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 2 },{ cop := 0, region := 152, targets := 64 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 262 70 137 176 96 89 153 281), lower := (rows 35 262 70 137 176 96 64 128 256), losses := [] }

theorem u21367 : Upper (D 7) (R 7) [34,260,66,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21368 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 137 208 33 120 184 312), lower := (rows 35 262 70 137 208 33 64 128 256), losses := [] }

theorem u21368 : Upper (D 7) (R 7) [34,260,66,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21368 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21369 : Route 9 := (fun mask => (mask,id))

def c21369 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21369 : Upper (D 7) (R 7) [34,260,66,129,192,8] 13 := by
  apply FastRouting.sound _ _ [34,260,66,129,192,8] 13 (by decide) (choices 1) [1,16,32] r21369 c21369
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6264
  · exact u6265
  · exact u6266

def b21370 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 262 70 137 208 48 105 169 297), lower := (rows 35 262 70 137 208 48 64 128 256), losses := [] }

theorem u21370 : Upper (D 7) (R 7) [34,260,66,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21370 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21371 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,1),(4,1)], upper := (rows 35 262 70 168 208 33 89 153 281), lower := (rows 35 262 70 168 208 33 64 128 256), losses := [] }

theorem u21371 : Upper (D 7) (R 7) [34,260,66,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21372 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 262 70 168 208 40 81 145 273), lower := (rows 35 262 70 168 208 40 64 128 256), losses := [] }

theorem u21372 : Upper (D 7) (R 7) [34,260,66,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21372 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21373 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 70 168 208 48 73 137 265), lower := (rows 35 262 70 168 208 48 64 128 256), losses := [] }

theorem u21373 : Upper (D 7) (R 7) [34,260,66,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21373 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21374 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 76 25 146 33 224 224 480), lower := (rows 35 262 76 25 146 33 64 128 256), losses := [] }

theorem u21374 : Upper (D 7) (R 7) [34,260,72,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21374 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21375 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 3, region := 228, targets := 2 }], pairs := [(0,7),(2,1),(3,6),(4,6)], upper := (rows 35 262 76 25 146 96 225 161 417), lower := (rows 35 262 76 25 146 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 24 16 100 64 0 256), good := (rows 35 295 108 25 27 96 96 0 256) }] }

theorem u21375 : Upper (D 7) (R 7) [34,260,72,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21376 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 3, region := 228, targets := 2 }], pairs := [(0,6),(1,7),(2,1),(3,6)], upper := (rows 35 262 76 25 146 160 97 225 353), lower := (rows 35 262 76 25 146 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 262 78 351 18 32 64 0 256) }] }

theorem u21376 : Upper (D 7) (R 7) [34,260,72,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21377 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 76 25 176 33 194 194 450), lower := (rows 35 262 76 25 176 33 64 128 256), losses := [] }

theorem u21377 : Upper (D 7) (R 7) [34,260,72,17,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21377 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21378 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 25 176 34 193 193 449), lower := (rows 35 262 76 25 176 34 64 128 256), losses := [] }

theorem u21378 : Upper (D 7) (R 7) [34,260,72,17,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21379 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,6),(4,6)], upper := (rows 35 262 76 25 176 96 195 131 387), lower := (rows 35 262 76 25 176 96 64 128 256), losses := [] }

theorem u21379 : Upper (D 7) (R 7) [34,260,72,17,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21380 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 76 25 176 160 67 195 323), lower := (rows 35 262 76 25 176 160 64 128 256), losses := [] }

theorem u21380 : Upper (D 7) (R 7) [34,260,72,17,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21381 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,0)], upper := (rows 35 262 76 25 208 33 226 162 418), lower := (rows 35 262 76 25 208 33 64 128 256), losses := [] }

theorem u21381 : Upper (D 7) (R 7) [34,260,72,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21382 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 25 208 34 225 161 417), lower := (rows 35 262 76 25 208 34 64 128 256), losses := [] }

theorem u21382 : Upper (D 7) (R 7) [34,260,72,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21383 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(1,7),(2,7)], upper := (rows 35 262 76 25 208 160 99 163 291), lower := (rows 35 262 76 25 208 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 32 65 0 257), good := (rows 355 262 78 351 80 32 64 0 256) }] }

theorem u21383 : Upper (D 7) (R 7) [34,260,72,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21384 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,1)], upper := (rows 35 262 76 26 112 33 193 129 385), lower := (rows 35 262 76 26 112 33 64 128 256), losses := [] }

theorem u21384 : Upper (D 7) (R 7) [34,260,72,18,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21385 : Route 9 := (fun mask => (mask,id))

def c21385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21385 : Upper (D 7) (R 7) [34,260,72,18,96,128] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,96,128] 13 (by decide) (choices 1) [1,128] r21385 c21385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6267
  · exact u6268

def b21386 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 262 76 26 145 33 224 224 480), lower := (rows 35 262 76 26 145 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 97 161 289), good := (rows 482 262 76 30 478 480 64 128 256) }] }

theorem u21386 : Upper (D 7) (R 7) [34,260,72,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21387 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(2,1),(3,6),(4,1),(4,6)], upper := (rows 35 262 76 26 145 96 225 161 417), lower := (rows 35 262 76 26 145 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 125 81 145 273), good := (rows 497 292 108 508 497 96 96 128 256) }] }

theorem u21387 : Upper (D 7) (R 7) [34,260,72,18,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21388 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(1,7),(2,1),(4,1)], upper := (rows 35 262 76 26 145 160 97 225 353), lower := (rows 35 262 76 26 145 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 17 185 81 145 273), good := (rows 497 260 108 508 497 160 64 160 256) },{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 262 13 59 177 160 0 160 256) },{ target := 7, region := (rows 1 18 20 24 16 32 65 0 257), good := (rows 355 262 76 30 351 32 64 0 256) }] }

theorem u21388 : Upper (D 7) (R 7) [34,260,72,18,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21389 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 262 76 26 176 33 193 193 449), lower := (rows 35 262 76 26 176 33 64 128 256), losses := [{ target := 5, region := (rows 1 18 20 24 16 0 97 161 289), good := (rows 451 262 76 30 478 449 64 128 256) }] }

theorem u21389 : Upper (D 7) (R 7) [34,260,72,18,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21389 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21390 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,7),(3,6),(4,1),(4,6)], upper := (rows 35 262 76 26 176 96 193 129 385), lower := (rows 35 262 76 26 176 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 108 27 48 96 96 0 256) }] }

theorem u21390 : Upper (D 7) (R 7) [34,260,72,18,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21391 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 262 76 26 176 160 65 193 321), lower := (rows 35 262 76 26 176 160 64 128 256), losses := [] }

theorem u21391 : Upper (D 7) (R 7) [34,260,72,18,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21392 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,1)], upper := (rows 35 262 76 26 208 33 225 161 417), lower := (rows 35 262 76 26 208 33 64 128 256), losses := [] }

theorem u21392 : Upper (D 7) (R 7) [34,260,72,18,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21392 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21393 : Route 9 := (fun mask => (mask,id))

def c21393 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21393 : Upper (D 7) (R 7) [34,260,72,18,192,128] 13 := by
  apply FastRouting.sound _ _ [34,260,72,18,192,128] 13 (by decide) (choices 1) [1,32] r21393 c21393
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6269
  · exact u6270

def b21394 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 76 56 145 33 194 194 450), lower := (rows 35 262 76 56 145 33 64 128 256), losses := [] }

theorem u21394 : Upper (D 7) (R 7) [34,260,72,48,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21394 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21395 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 56 145 34 193 193 449), lower := (rows 35 262 76 56 145 34 64 128 256), losses := [] }

theorem u21395 : Upper (D 7) (R 7) [34,260,72,48,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21395 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21396 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(3,6),(4,5),(4,6)], upper := (rows 35 262 76 56 145 96 195 131 387), lower := (rows 35 262 76 56 145 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 108 56 17 96 96 0 256) }] }

theorem u21396 : Upper (D 7) (R 7) [34,260,72,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21396 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21397 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 76 56 145 160 67 195 323), lower := (rows 35 262 76 56 145 160 64 128 256), losses := [] }

theorem u21397 : Upper (D 7) (R 7) [34,260,72,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21398 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 76 56 146 33 193 193 449), lower := (rows 35 262 76 56 146 33 64 128 256), losses := [] }

theorem u21398 : Upper (D 7) (R 7) [34,260,72,48,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21398 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21399 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(3,6),(4,5),(4,6)], upper := (rows 35 262 76 56 146 96 193 129 385), lower := (rows 35 262 76 56 146 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 108 56 19 96 96 0 256) }] }

theorem u21399 : Upper (D 7) (R 7) [34,260,72,48,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21399 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21400 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 35 262 76 56 146 160 65 193 321), lower := (rows 35 262 76 56 146 160 64 128 256), losses := [] }

theorem u21400 : Upper (D 7) (R 7) [34,260,72,48,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21400 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21401 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 208, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,6),(4,5)], upper := (rows 35 262 76 56 208 33 195 131 387), lower := (rows 35 262 76 56 208 33 64 128 256), losses := [] }

theorem u21401 : Upper (D 7) (R 7) [34,260,72,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21401 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21402 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 56 208 34 193 129 385), lower := (rows 35 262 76 56 208 34 64 128 256), losses := [] }

theorem u21402 : Upper (D 7) (R 7) [34,260,72,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21402 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21403 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 35 262 76 56 208 160 67 131 259), lower := (rows 35 262 76 56 208 160 64 128 256), losses := [] }

theorem u21403 : Upper (D 7) (R 7) [34,260,72,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21403 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21404 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 137 81 34 240 176 432), lower := (rows 35 262 76 137 81 34 64 128 256), losses := [] }

theorem u21404 : Upper (D 7) (R 7) [34,260,72,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21405 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(1,0),(2,0),(3,6)], upper := (rows 35 262 76 137 81 48 226 162 418), lower := (rows 35 262 76 137 81 48 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 48 65 129 257), good := (rows 482 262 78 462 496 48 64 128 256) }] }

theorem u21405 : Upper (D 7) (R 7) [34,260,72,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21405 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21406 : Route 9 := (fun mask => (mask,id))

def c21406 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21406 : Upper (D 7) (R 7) [34,260,72,129,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,65,128] 13 (by decide) (choices 1) [2,16,32] r21406 c21406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6271
  · exact u6272
  · exact u6273

def b21407 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,0)], upper := (rows 35 262 76 137 82 33 240 176 432), lower := (rows 35 262 76 137 82 33 64 128 256), losses := [] }

theorem u21407 : Upper (D 7) (R 7) [34,260,72,129,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21408 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 76 137 82 48 225 161 417), lower := (rows 35 262 76 137 82 48 64 128 256), losses := [] }

theorem u21408 : Upper (D 7) (R 7) [34,260,72,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21408 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21409 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 169, targets := 64 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(1,7),(3,6),(4,7)], upper := (rows 35 262 76 137 82 160 113 177 305), lower := (rows 35 262 76 137 82 160 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 29 32 65 0 257), good := (rows 371 278 94 351 82 32 64 0 256) }] }

theorem u21409 : Upper (D 7) (R 7) [34,260,72,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21409 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21410 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 262 76 137 112 33 210 146 402), lower := (rows 35 262 76 137 112 33 64 128 256), losses := [{ target := 0, region := (rows 0 14 12 8 49 32 73 137 265), good := (rows 498 262 462 478 112 496 64 128 256) }] }

theorem u21410 : Upper (D 7) (R 7) [34,260,72,129,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21411 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 137 112 34 209 145 401), lower := (rows 35 262 76 137 112 34 64 128 256), losses := [] }

theorem u21411 : Upper (D 7) (R 7) [34,260,72,129,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21412 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 76 137 112 48 195 131 387), lower := (rows 35 262 76 137 112 48 64 128 256), losses := [] }

theorem u21412 : Upper (D 7) (R 7) [34,260,72,129,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21412 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21413 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(1,7),(4,0),(4,1),(4,7)], upper := (rows 35 262 76 137 112 160 83 147 275), lower := (rows 35 262 76 137 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 278 124 168 112 160 64 160 256) },{ target := 1, region := (rows 1 0 4 8 20 168 64 128 256), good := (rows 33 276 124 169 112 160 64 160 256) },{ target := 7, region := (rows 1 14 12 8 17 32 73 0 265), good := (rows 371 262 334 351 112 32 64 0 256) }] }

theorem u21413 : Upper (D 7) (R 7) [34,260,72,129,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21413 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21414 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,0)], upper := (rows 35 262 76 137 146 33 112 240 368), lower := (rows 35 262 76 137 146 33 64 128 256), losses := [] }

theorem u21414 : Upper (D 7) (R 7) [34,260,72,129,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21415 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 76 137 146 48 97 225 353), lower := (rows 35 262 76 137 146 48 64 128 256), losses := [] }

theorem u21415 : Upper (D 7) (R 7) [34,260,72,129,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21415 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21416 : Route 9 := (fun mask => (mask,id))

def c21416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21416 : Upper (D 7) (R 7) [34,260,72,129,130,64] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,130,64] 13 (by decide) (choices 1) [1,16,32] r21416 c21416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6274
  · exact u6275
  · exact u6276

def b21417 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 3, region := 48, targets := 66 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 262 76 137 176 33 82 210 338), lower := (rows 35 262 76 137 176 33 64 128 256), losses := [] }

theorem u21417 : Upper (D 7) (R 7) [34,260,72,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21417 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21418 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 137 176 34 81 209 337), lower := (rows 35 262 76 137 176 34 64 128 256), losses := [] }

theorem u21418 : Upper (D 7) (R 7) [34,260,72,129,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21418 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21419 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 76 137 176 48 67 195 323), lower := (rows 35 262 76 137 176 48 64 128 256), losses := [] }

theorem u21419 : Upper (D 7) (R 7) [34,260,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21419 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21419
end Delivery.IrregularNine14.P07
