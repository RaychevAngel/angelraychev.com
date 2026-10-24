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

def r21420 : Route 9 := (fun mask => (mask,id))

def c21420 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21420 : Upper (D 7) (R 7) [34,260,72,129,160,64] 13 := by
  apply FastRouting.sound _ _ [34,260,72,129,160,64] 13 (by decide) (choices 1) [1,2,16] r21420 c21420
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6277
  · exact u6278
  · exact u6279

def b21421 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0)], upper := (rows 35 262 76 137 208 33 114 178 306), lower := (rows 35 262 76 137 208 33 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 57 32 65 129 257), good := (rows 498 262 94 478 208 496 64 128 256) }] }

theorem u21421 : Upper (D 7) (R 7) [34,260,72,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21421 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21422 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 137 208 34 113 177 305), lower := (rows 35 262 76 137 208 34 64 128 256), losses := [] }

theorem u21422 : Upper (D 7) (R 7) [34,260,72,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21422 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21423 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(1,7),(2,7),(3,6)], upper := (rows 35 262 76 137 208 48 99 163 291), lower := (rows 35 262 76 137 208 48 64 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 16 48 65 0 257), good := (rows 355 262 78 335 112 48 64 0 256) }] }

theorem u21423 : Upper (D 7) (R 7) [34,260,72,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21423 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21424 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 262 76 138 81 33 240 176 432), lower := (rows 35 262 76 138 81 33 64 128 256), losses := [{ target := 7, region := (rows 11 2 4 8 20 63 64 0 256), good := (rows 35 311 125 43 113 33 64 0 256) }] }

theorem u21424 : Upper (D 7) (R 7) [34,260,72,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21425 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 136, targets := 64 }], pairs := [(0,7),(3,6),(4,1)], upper := (rows 35 262 76 138 81 48 225 161 417), lower := (rows 35 262 76 138 81 48 64 128 256), losses := [{ target := 7, region := (rows 11 2 4 8 20 54 64 0 256), good := (rows 35 311 125 43 113 48 64 0 256) }] }

theorem u21425 : Upper (D 7) (R 7) [34,260,72,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21425 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21426 : Route 9 := (fun mask => (mask,id))

def c21426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21426 : Upper (D 7) (R 7) [34,260,72,130,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,65,128] 13 (by decide) (choices 1) [1,16,32] r21426 c21426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6280
  · exact u6281
  · exact u6282

def b21427 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(0,7),(4,1),(4,7)], upper := (rows 35 262 76 138 112 33 209 145 401), lower := (rows 35 262 76 138 112 33 64 128 256), losses := [{ target := 7, region := (rows 11 2 4 8 20 47 64 0 256), good := (rows 35 311 125 43 112 33 64 0 256) }] }

theorem u21427 : Upper (D 7) (R 7) [34,260,72,130,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21428 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 76 138 112 48 193 129 385), lower := (rows 35 262 76 138 112 48 64 128 256), losses := [] }

theorem u21428 : Upper (D 7) (R 7) [34,260,72,130,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21428 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21429 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1),(4,7)], upper := (rows 35 262 76 138 112 160 81 145 273), lower := (rows 35 262 76 138 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 278 124 170 112 160 64 160 256) }] }

theorem u21429 : Upper (D 7) (R 7) [34,260,72,130,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21429 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21430 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 262 76 138 145 33 112 240 368), lower := (rows 35 262 76 138 145 33 64 128 256), losses := [] }

theorem u21430 : Upper (D 7) (R 7) [34,260,72,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21430 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21431 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 49, targets := 64 },{ cop := 0, region := 208, targets := 2 }], pairs := [(0,6),(4,1),(4,6)], upper := (rows 35 262 76 138 145 48 97 225 353), lower := (rows 35 262 76 138 145 48 64 128 256), losses := [] }

theorem u21431 : Upper (D 7) (R 7) [34,260,72,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21431 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21432 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,7),(3,6),(4,1),(4,6)], upper := (rows 35 262 76 138 145 96 113 177 305), lower := (rows 35 262 76 138 145 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 116 80 0 272), good := (rows 35 295 108 11 369 96 96 0 256) }] }

theorem u21432 : Upper (D 7) (R 7) [34,260,72,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21432 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21433 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 2 },{ cop := 3, region := 49, targets := 64 }], pairs := [(0,6),(0,7),(4,1),(4,6)], upper := (rows 35 262 76 138 176 33 81 209 337), lower := (rows 35 262 76 138 176 33 64 128 256), losses := [] }

theorem u21433 : Upper (D 7) (R 7) [34,260,72,130,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21434 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 262 76 138 176 48 65 193 321), lower := (rows 35 262 76 138 176 48 64 128 256), losses := [] }

theorem u21434 : Upper (D 7) (R 7) [34,260,72,130,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21434 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21435 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 2 }], pairs := [(0,7),(3,6),(4,1),(4,6)], upper := (rows 35 262 76 138 176 96 81 145 273), lower := (rows 35 262 76 138 176 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 108 11 48 96 96 0 256) }] }

theorem u21435 : Upper (D 7) (R 7) [34,260,72,130,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21435 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21436 : Route 9 := (fun mask => (mask,id))

def c21436 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21436 : Upper (D 7) (R 7) [34,260,72,130,192,1] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,192,1] 13 (by decide) (choices 1) [1,16,32] r21436 c21436
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6283
  · exact u6284
  · exact u6285

def r21437 : Route 9 := (fun mask => (mask,id))

def c21437 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21437 : Upper (D 7) (R 7) [34,260,72,130,192,16] 13 := by
  apply FastRouting.sound _ _ [34,260,72,130,192,16] 13 (by decide) (choices 1) [1,32] r21437 c21437
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6286
  · exact u6287

def b21438 : PairBound 9 := { available := 162, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(1,6)], upper := (rows 35 262 76 152 81 33 226 162 418), lower := (rows 35 262 76 152 81 33 64 128 256), losses := [{ target := 0, region := (rows 0 18 20 24 16 32 65 129 257), good := (rows 482 262 76 158 478 480 64 128 256) }] }

theorem u21438 : Upper (D 7) (R 7) [34,260,72,144,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21439 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 152 81 34 225 161 417), lower := (rows 35 262 76 152 81 34 64 128 256), losses := [] }

theorem u21439 : Upper (D 7) (R 7) [34,260,72,144,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21440 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(3,6),(4,7)], upper := (rows 35 262 76 152 81 160 99 163 291), lower := (rows 35 262 76 152 81 160 64 128 256), losses := [{ target := 6, region := (rows 7 6 4 24 16 191 0 135 263), good := (rows 419 423 431 184 441 160 0 160 256) }] }

theorem u21440 : Upper (D 7) (R 7) [34,260,72,144,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21441 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 1, region := 33, targets := 128 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(0,7),(1,6),(3,6)], upper := (rows 35 262 76 152 82 33 225 161 417), lower := (rows 35 262 76 152 82 33 64 128 256), losses := [] }

theorem u21441 : Upper (D 7) (R 7) [34,260,72,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21441 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21442 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 80, targets := 128 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,7)], upper := (rows 35 262 76 152 82 160 97 161 289), lower := (rows 35 262 76 152 82 160 64 128 256), losses := [] }

theorem u21442 : Upper (D 7) (R 7) [34,260,72,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21442 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21443 : Route 9 := (fun mask => (mask,id))

def c21443 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21443 : Upper (D 7) (R 7) [34,260,72,144,96,1] 13 := by
  apply FastRouting.sound _ _ [34,260,72,144,96,1] 13 (by decide) (choices 1) [1,2,128] r21443 c21443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6288
  · exact u6289
  · exact u6290

def b21444 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 152 112 34 193 129 385), lower := (rows 35 262 76 152 112 34 64 128 256), losses := [] }

theorem u21444 : Upper (D 7) (R 7) [34,260,72,144,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21444 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21445 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 0, region := 80, targets := 128 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 35 262 76 152 112 160 67 131 259), lower := (rows 35 262 76 152 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 168 64 128 256), good := (rows 34 278 124 184 112 160 64 160 256) }] }

theorem u21445 : Upper (D 7) (R 7) [34,260,72,144,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21445 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21446 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(4,5)], upper := (rows 35 262 76 168 81 33 210 146 402), lower := (rows 35 262 76 168 81 33 64 128 256), losses := [{ target := 5, region := (rows 1 14 12 8 49 0 73 137 265), good := (rows 467 262 462 478 465 465 64 128 256) }] }

theorem u21446 : Upper (D 7) (R 7) [34,260,72,160,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21447 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 168 81 34 209 145 401), lower := (rows 35 262 76 168 81 34 64 128 256), losses := [] }

theorem u21447 : Upper (D 7) (R 7) [34,260,72,160,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21448 : Route 9 := (fun mask => (mask,id))

def c21448 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21448 : Upper (D 7) (R 7) [34,260,72,160,65,16] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,65,16] 13 (by decide) (choices 1) [1,2,128] r21448 c21448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6291
  · exact u6292
  · exact u6293

def b21449 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 262 76 168 81 160 83 147 275), lower := (rows 35 262 76 168 81 160 64 128 256), losses := [] }

theorem u21449 : Upper (D 7) (R 7) [34,260,72,160,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21450 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 169, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,5)], upper := (rows 35 262 76 168 82 33 209 145 401), lower := (rows 35 262 76 168 82 33 64 128 256), losses := [] }

theorem u21450 : Upper (D 7) (R 7) [34,260,72,160,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21451 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 262 76 168 82 48 193 129 385), lower := (rows 35 262 76 168 82 48 64 128 256), losses := [] }

theorem u21451 : Upper (D 7) (R 7) [34,260,72,160,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21451 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21452 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 35 262 76 168 82 160 81 145 273), lower := (rows 35 262 76 168 82 160 64 128 256), losses := [] }

theorem u21452 : Upper (D 7) (R 7) [34,260,72,160,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21453 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 4, region := 40, targets := 66 }], pairs := [(0,6),(0,7),(3,1),(3,6)], upper := (rows 35 262 76 168 145 33 82 210 338), lower := (rows 35 262 76 168 145 33 64 128 256), losses := [] }

theorem u21453 : Upper (D 7) (R 7) [34,260,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21454 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 168 145 34 81 209 337), lower := (rows 35 262 76 168 145 34 64 128 256), losses := [] }

theorem u21454 : Upper (D 7) (R 7) [34,260,72,160,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21455 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 76 168 145 48 67 195 323), lower := (rows 35 262 76 168 145 48 64 128 256), losses := [] }

theorem u21455 : Upper (D 7) (R 7) [34,260,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21455 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21456 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(3,6),(4,5),(4,6)], upper := (rows 35 262 76 168 145 96 83 147 275), lower := (rows 35 262 76 168 145 96 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 100 64 0 256), good := (rows 35 295 108 40 17 96 96 0 256) }] }

theorem u21456 : Upper (D 7) (R 7) [34,260,72,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21457 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 208, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(0,7),(3,6),(4,5)], upper := (rows 35 262 76 168 146 33 81 209 337), lower := (rows 35 262 76 168 146 33 64 128 256), losses := [] }

theorem u21457 : Upper (D 7) (R 7) [34,260,72,160,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21458 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 262 76 168 146 48 65 193 321), lower := (rows 35 262 76 168 146 48 64 128 256), losses := [] }

theorem u21458 : Upper (D 7) (R 7) [34,260,72,160,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21458 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21459 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 64 },{ cop := 0, region := 144, targets := 32 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(3,6),(4,5),(4,6)], upper := (rows 35 262 76 168 146 96 81 145 273), lower := (rows 35 262 76 168 146 96 64 128 256), losses := [] }

theorem u21459 : Upper (D 7) (R 7) [34,260,72,160,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21460 : Route 9 := (fun mask => (mask,id))

def c21460 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21460 : Upper (D 7) (R 7) [34,260,72,160,192,1] 13 := by
  apply FastRouting.sound _ _ [34,260,72,160,192,1] 13 (by decide) (choices 1) [1,2,16] r21460 c21460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6294
  · exact u6295
  · exact u6296

def b21461 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 262 76 168 208 34 81 145 273), lower := (rows 35 262 76 168 208 34 64 128 256), losses := [] }

theorem u21461 : Upper (D 7) (R 7) [34,260,72,160,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21461 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21462 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 44, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 262 76 168 208 48 67 131 259), lower := (rows 35 262 76 168 208 48 64 128 256), losses := [] }

theorem u21462 : Upper (D 7) (R 7) [34,260,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21462 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21463 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 35 262 100 25 146 33 200 200 456), lower := (rows 35 262 100 25 146 33 64 128 256), losses := [] }

theorem u21463 : Upper (D 7) (R 7) [34,260,96,17,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21464 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 41, targets := 192 }], pairs := [(0,6),(0,7),(3,6)], upper := (rows 35 262 100 25 146 40 193 193 449), lower := (rows 35 262 100 25 146 40 64 128 256), losses := [] }

theorem u21464 : Upper (D 7) (R 7) [34,260,96,17,130,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21464 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21465 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 35 262 100 25 146 96 201 137 393), lower := (rows 35 262 100 25 146 96 64 128 256), losses := [] }

theorem u21465 : Upper (D 7) (R 7) [34,260,96,17,130,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21465 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21466 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(3,5),(3,6),(4,5)], upper := (rows 35 262 100 25 146 160 73 201 329), lower := (rows 35 262 100 25 146 160 64 128 256), losses := [] }

theorem u21466 : Upper (D 7) (R 7) [34,260,96,17,130,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21467 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 454, targets := 1 },{ cop := 0, region := 216, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,5)], upper := (rows 35 262 100 25 152 33 194 194 450), lower := (rows 35 262 100 25 152 33 64 128 256), losses := [] }

theorem u21467 : Upper (D 7) (R 7) [34,260,96,17,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21467 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21468 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 25 152 34 193 193 449), lower := (rows 35 262 100 25 152 34 64 128 256), losses := [] }

theorem u21468 : Upper (D 7) (R 7) [34,260,96,17,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21468 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21469 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 35 262 100 25 152 96 195 131 387), lower := (rows 35 262 100 25 152 96 64 128 256), losses := [] }

theorem u21469 : Upper (D 7) (R 7) [34,260,96,17,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21470 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 216, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 35 262 100 25 152 160 67 195 323), lower := (rows 35 262 100 25 152 160 64 128 256), losses := [] }

theorem u21470 : Upper (D 7) (R 7) [34,260,96,17,136,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21470 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21471 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 25 208 33 202 138 394), lower := (rows 35 262 100 25 208 33 64 128 256), losses := [] }

theorem u21471 : Upper (D 7) (R 7) [34,260,96,17,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21471 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21472 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 220, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 262 100 25 208 34 201 137 393), lower := (rows 35 262 100 25 208 34 64 128 256), losses := [] }

theorem u21472 : Upper (D 7) (R 7) [34,260,96,17,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21472 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21473 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6),(3,5),(4,5)], upper := (rows 35 262 100 25 208 40 195 131 387), lower := (rows 35 262 100 25 208 40 64 128 256), losses := [] }

theorem u21473 : Upper (D 7) (R 7) [34,260,96,17,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21473 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21474 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 35 262 100 25 208 160 75 139 267), lower := (rows 35 262 100 25 208 160 64 128 256), losses := [] }

theorem u21474 : Upper (D 7) (R 7) [34,260,96,17,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21474 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21475 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 26 81 33 200 136 392), lower := (rows 35 262 100 26 81 33 64 128 256), losses := [] }

theorem u21475 : Upper (D 7) (R 7) [34,260,96,18,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21476 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 262 100 26 81 40 193 129 385), lower := (rows 35 262 100 26 81 40 64 128 256), losses := [] }

theorem u21476 : Upper (D 7) (R 7) [34,260,96,18,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21476 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r21477 : Route 9 := (fun mask => (mask,id))

def c21477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u21477 : Upper (D 7) (R 7) [34,260,96,18,65,128] 13 := by
  apply FastRouting.sound _ _ [34,260,96,18,65,128] 13 (by decide) (choices 1) [1,8,128] r21477 c21477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6297
  · exact u6298
  · exact u6299

def b21478 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 262 100 26 145 33 200 200 456), lower := (rows 35 262 100 26 145 33 64 128 256), losses := [] }

theorem u21478 : Upper (D 7) (R 7) [34,260,96,18,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21478 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21479 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 212, targets := 2 },{ cop := 0, region := 216, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 35 262 100 26 145 40 193 193 449), lower := (rows 35 262 100 26 145 40 64 128 256), losses := [] }

theorem u21479 : Upper (D 7) (R 7) [34,260,96,18,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21479 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u21479
end Delivery.IrregularNine14.P07
