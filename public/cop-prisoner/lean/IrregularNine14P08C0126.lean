import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0020
import IrregularNine14P08C0021

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7560 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 276 73 145 224 224 224 480), lower := (rows 7 42 276 73 145 32 64 128 256), losses := [] }

theorem u7560 : Upper (D 8) (R 8) [6,40,272,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7560 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7561 : Route 9 := (fun mask => (mask,id))

def c7561 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7561 : Upper (D 8) (R 8) [6,40,272,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,160] 13 (by decide) (choices 1) [1,64,128] r7561 c7561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1230
  · exact u1231
  · exact u1232

def b7562 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 276 73 208 161 225 161 417), lower := (rows 7 42 276 73 208 32 64 128 256), losses := [] }

theorem u7562 : Upper (D 8) (R 8) [6,40,272,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7563 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7563 : Upper (D 8) (R 8) [6,40,272,192,33] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,33] 13 (by decide) (choices 1) [1,64] r7563 c7563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1233
  · exact u1234

def b7564 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 42 276 200 81 161 225 161 417), lower := (rows 7 42 276 200 81 32 64 128 256), losses := [] }

theorem u7564 : Upper (D 8) (R 8) [6,40,272,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7565 : Route 9 := (fun mask => (mask,id))

def c7565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7565 : Upper (D 8) (R 8) [6,40,272,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,272,192,96] 13 (by decide) (choices 1) [1,128] r7565 c7565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1235
  · exact u1236

def b7566 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 276 200 208 33 97 161 289), lower := (rows 7 42 276 200 208 32 64 128 256), losses := [] }

theorem u7566 : Upper (D 8) (R 8) [6,40,272,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7566 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7567 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 25 49 224 192 192 448), lower := (rows 7 42 292 25 49 32 64 128 256), losses := [] }

theorem u7567 : Upper (D 8) (R 8) [6,40,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7568 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 292 25 81 224 224 224 480), lower := (rows 7 42 292 25 81 32 64 128 256), losses := [] }

theorem u7568 : Upper (D 8) (R 8) [6,40,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7569 : Route 9 := (fun mask => (mask,id))

def c7569 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7569 : Upper (D 8) (R 8) [6,40,288,17,96] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,96] 13 (by decide) (choices 1) [1,64,128] r7569 c7569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1237
  · exact u1238
  · exact u1239

def r7570 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7570 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7570 : Upper (D 8) (R 8) [6,40,288,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,17,192] 13 (by decide) (choices 1) [1,64] r7570 c7570
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1240
  · exact u1241

def b7571 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 73 49 240 208 208 464), lower := (rows 7 42 292 73 49 32 64 128 256), losses := [] }

theorem u7571 : Upper (D 8) (R 8) [6,40,288,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7572 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 292 73 81 176 240 176 432), lower := (rows 7 42 292 73 81 32 64 128 256), losses := [] }

theorem u7572 : Upper (D 8) (R 8) [6,40,288,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7572 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7573 : Route 9 := (fun mask => (mask,id))

def c7573 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7573 : Upper (D 8) (R 8) [6,40,288,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,96] 13 (by decide) (choices 1) [1,16,128] r7573 c7573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1242
  · exact u1243
  · exact u1244

def b7574 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 356, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 292 73 145 240 240 240 496), lower := (rows 7 42 292 73 145 32 64 128 256), losses := [] }

theorem u7574 : Upper (D 8) (R 8) [6,40,288,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7574 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7575 : Route 9 := (fun mask => (mask,id))

def c7575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7575 : Upper (D 8) (R 8) [6,40,288,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,160] 13 (by decide) (choices 1) [1,16,64,128] r7575 c7575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1245
  · exact u1246
  · exact u1247
  · exact u1248

def r7576 : Route 9 := (fun mask => (mask,id))

def c7576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7576 : Upper (D 8) (R 8) [6,40,288,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,288,65,192] 13 (by decide) (choices 1) [1,16,128] r7576 c7576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1249
  · exact u1250
  · exact u1251

def b7577 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 292 88 49 225 193 193 449), lower := (rows 7 42 292 88 49 32 64 128 256), losses := [] }

theorem u7577 : Upper (D 8) (R 8) [6,40,288,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7577 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7578 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 88 81 161 225 161 417), lower := (rows 7 42 292 88 81 32 64 128 256), losses := [] }

theorem u7578 : Upper (D 8) (R 8) [6,40,288,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7579 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 292 88 112 161 193 129 385), lower := (rows 7 42 292 88 112 32 64 128 256), losses := [] }

theorem u7579 : Upper (D 8) (R 8) [6,40,288,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7580 : Route 9 := (fun mask => (mask,id))

def c7580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7580 : Upper (D 8) (R 8) [6,40,288,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80,129] 13 (by decide) (choices 1) [1,64,128] r7580 c7580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1252
  · exact u1253
  · exact u1254

def r7581 : Route 9 := (fun mask => (mask,id))

def c7581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7581 : Upper (D 8) (R 8) [6,40,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,288,80,160] 13 (by decide) (choices 1) [1,64,128] r7581 c7581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1255
  · exact u1256
  · exact u1257

def b7582 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 292 88 208 161 225 161 417), lower := (rows 7 42 292 88 208 32 64 128 256), losses := [] }

theorem u7582 : Upper (D 8) (R 8) [6,40,288,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7582 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7583 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 292 200 49 241 209 209 465), lower := (rows 7 42 292 200 49 32 64 128 256), losses := [] }

theorem u7583 : Upper (D 8) (R 8) [6,40,288,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7584 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 42 292 200 81 177 241 177 433), lower := (rows 7 42 292 200 81 32 64 128 256), losses := [] }

theorem u7584 : Upper (D 8) (R 8) [6,40,288,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7585 : Route 9 := (fun mask => (mask,id))

def c7585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7585 : Upper (D 8) (R 8) [6,40,288,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,288,192,96] 13 (by decide) (choices 1) [1,16,128] r7585 c7585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1258
  · exact u1259
  · exact u1260

def b7586 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 292 200 208 49 113 177 305), lower := (rows 7 42 292 200 208 32 64 128 256), losses := [] }

theorem u7586 : Upper (D 8) (R 8) [6,40,288,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7587 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 25 49 224 224 224 480), lower := (rows 7 42 324 25 49 32 64 128 256), losses := [] }

theorem u7587 : Upper (D 8) (R 8) [6,40,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7588 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 25 81 160 224 160 416), lower := (rows 7 42 324 25 81 32 64 128 256), losses := [] }

theorem u7588 : Upper (D 8) (R 8) [6,40,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7588 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7589 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 25 112 161 225 161 417), lower := (rows 7 42 324 25 112 32 64 128 256), losses := [] }

theorem u7589 : Upper (D 8) (R 8) [6,40,320,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7589 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7590 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 324 25 145 224 224 224 480), lower := (rows 7 42 324 25 145 32 64 128 256), losses := [] }

theorem u7590 : Upper (D 8) (R 8) [6,40,320,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7591 : Route 9 := (fun mask => (mask,id))

def c7591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7591 : Upper (D 8) (R 8) [6,40,320,17,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,17,160] 13 (by decide) (choices 1) [1,64,128] r7591 c7591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1261
  · exact u1262
  · exact u1263

def b7592 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 25 208 161 225 161 417), lower := (rows 7 42 324 25 208 32 64 128 256), losses := [] }

theorem u7592 : Upper (D 8) (R 8) [6,40,320,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7592 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7593 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 324 137 49 240 240 240 496), lower := (rows 7 42 324 137 49 32 64 128 256), losses := [] }

theorem u7593 : Upper (D 8) (R 8) [6,40,320,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7593 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7594 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 137 81 176 240 176 432), lower := (rows 7 42 324 137 81 32 64 128 256), losses := [] }

theorem u7594 : Upper (D 8) (R 8) [6,40,320,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7594 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7595 : Route 9 := (fun mask => (mask,id))

def c7595 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7595 : Upper (D 8) (R 8) [6,40,320,129,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,96] 13 (by decide) (choices 1) [1,16,128] r7595 c7595
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1264
  · exact u1265
  · exact u1266

def b7596 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 324 137 145 112 112 240 368), lower := (rows 7 42 324 137 145 32 64 128 256), losses := [] }

theorem u7596 : Upper (D 8) (R 8) [6,40,320,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7596 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7597 : Route 9 := (fun mask => (mask,id))

def c7597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7597 : Upper (D 8) (R 8) [6,40,320,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160] 13 (by decide) (choices 1) [1,16,64] r7597 c7597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1267
  · exact u1268
  · exact u1269

def r7598 : Route 9 := (fun mask => (mask,id))

def c7598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7598 : Upper (D 8) (R 8) [6,40,320,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,192] 13 (by decide) (choices 1) [1,16] r7598 c7598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1270
  · exact u1271

def r7599 : Route 9 := (fun mask => (mask,id))

def c7599 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7599 : Upper (D 8) (R 8) [6,40,320,144,33] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,33] 13 (by decide) (choices 1) [1,64,128] r7599 c7599
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1272
  · exact u1273
  · exact u1274

def b7600 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 152 81 161 225 161 417), lower := (rows 7 42 324 152 81 32 64 128 256), losses := [] }

theorem u7600 : Upper (D 8) (R 8) [6,40,320,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7601 : Route 9 := (fun mask => (mask,id))

def c7601 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7601 : Upper (D 8) (R 8) [6,40,320,144,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,144,96] 13 (by decide) (choices 1) [1,128] r7601 c7601
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1275
  · exact u1276

def b7602 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 145 97 97 225 353), lower := (rows 7 42 324 152 145 32 64 128 256), losses := [] }

theorem u7602 : Upper (D 8) (R 8) [6,40,320,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7603 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 152 176 97 97 225 353), lower := (rows 7 42 324 152 176 32 64 128 256), losses := [] }

theorem u7603 : Upper (D 8) (R 8) [6,40,320,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7603 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7604 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 208 33 97 161 289), lower := (rows 7 42 324 152 208 32 64 128 256), losses := [] }

theorem u7604 : Upper (D 8) (R 8) [6,40,320,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7605 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 56 49 480 480 480 480), lower := (rows 7 67 140 56 49 32 64 128 256), losses := [] }

theorem u7605 : Upper (D 8) (R 8) [6,65,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7606 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 140 56 81 416 480 416 416), lower := (rows 7 67 140 56 81 32 64 128 256), losses := [] }

theorem u7606 : Upper (D 8) (R 8) [6,65,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7607 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 56 112 417 481 417 417), lower := (rows 7 67 140 56 112 32 64 128 256), losses := [] }

theorem u7607 : Upper (D 8) (R 8) [6,65,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7608 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 56 145 352 352 480 352), lower := (rows 7 67 140 56 145 32 64 128 256), losses := [] }

theorem u7608 : Upper (D 8) (R 8) [6,65,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7609 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 56 176 353 353 481 353), lower := (rows 7 67 140 56 176 32 64 128 256), losses := [] }

theorem u7609 : Upper (D 8) (R 8) [6,65,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7610 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 56 208 289 353 417 289), lower := (rows 7 67 140 56 208 32 64 128 256), losses := [] }

theorem u7610 : Upper (D 8) (R 8) [6,65,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7611 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 56 273 224 224 224 480), lower := (rows 7 67 140 56 273 32 64 128 256), losses := [] }

theorem u7611 : Upper (D 8) (R 8) [6,65,136,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7611 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7612 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 140 56 304 225 225 225 481), lower := (rows 7 67 140 56 304 32 64 128 256), losses := [] }

theorem u7612 : Upper (D 8) (R 8) [6,65,136,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7612 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7613 : Route 9 := (fun mask => (mask,id))

def c7613 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7613 : Upper (D 8) (R 8) [6,65,136,48,320] 13 := by
  apply FastRouting.sound _ _ [6,65,136,48,320] 13 (by decide) (choices 1) [1,128] r7613 c7613
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1277
  · exact u1278

def b7614 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 56 400 97 97 225 353), lower := (rows 7 67 140 56 400 32 64 128 256), losses := [] }

theorem u7614 : Upper (D 8) (R 8) [6,65,136,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7615 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 280 49 224 224 224 480), lower := (rows 7 67 140 280 49 32 64 128 256), losses := [] }

theorem u7615 : Upper (D 8) (R 8) [6,65,136,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7616 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 140 280 81 160 224 160 416), lower := (rows 7 67 140 280 81 32 64 128 256), losses := [] }

theorem u7616 : Upper (D 8) (R 8) [6,65,136,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7617 : Route 9 := (fun mask => (mask,id))

def c7617 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7617 : Upper (D 8) (R 8) [6,65,136,272,96] 13 := by
  apply FastRouting.sound _ _ [6,65,136,272,96] 13 (by decide) (choices 1) [1,128] r7617 c7617
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1279
  · exact u1280

def b7618 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 280 145 96 96 224 352), lower := (rows 7 67 140 280 145 32 64 128 256), losses := [] }

theorem u7618 : Upper (D 8) (R 8) [6,65,136,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7619 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 140 280 176 97 97 225 353), lower := (rows 7 67 140 280 176 32 64 128 256), losses := [] }

theorem u7619 : Upper (D 8) (R 8) [6,65,136,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7619
end Delivery.IrregularNine14.P08
