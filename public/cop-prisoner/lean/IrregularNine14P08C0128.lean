import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0021
import IrregularNine14P08C0022

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7680 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 164 152 280 97 97 225 353), lower := (rows 7 67 164 152 280 32 64 128 256), losses := [] }

theorem u7680 : Upper (D 8) (R 8) [6,65,160,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7681 : Route 9 := (fun mask => (mask,id))

def c7681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7681 : Upper (D 8) (R 8) [6,65,160,144,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144,288] 13 (by decide) (choices 1) [1,8,64] r7681 c7681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def r7682 : Route 9 := (fun mask => (mask,id))

def c7682 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7682 : Upper (D 8) (R 8) [6,65,160,144,320] 13 := by
  apply FastRouting.sound _ _ [6,65,160,144,320] 13 (by decide) (choices 1) [1,8] r7682 c7682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1322
  · exact u1323

def b7683 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 168 280 113 113 241 369), lower := (rows 7 67 164 168 280 32 64 128 256), losses := [] }

theorem u7683 : Upper (D 8) (R 8) [6,65,160,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7684 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 168 304 121 89 217 345), lower := (rows 7 67 164 168 304 32 64 128 256), losses := [] }

theorem u7684 : Upper (D 8) (R 8) [6,65,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7685 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 164 168 336 57 121 185 313), lower := (rows 7 67 164 168 336 32 64 128 256), losses := [] }

theorem u7685 : Upper (D 8) (R 8) [6,65,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7685 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7686 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 236, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 164 200 273 56 120 184 312), lower := (rows 7 67 164 200 273 32 64 128 256), losses := [] }

theorem u7686 : Upper (D 8) (R 8) [6,65,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7686 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7687 : Route 9 := (fun mask => (mask,id))

def c7687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7687 : Upper (D 8) (R 8) [6,65,160,192,264] 13 := by
  apply FastRouting.sound _ _ [6,65,160,192,264] 13 (by decide) (choices 1) [1,16] r7687 c7687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1324
  · exact u1325

def r7688 : Route 9 := (fun mask => (mask,id))

def c7688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7688 : Upper (D 8) (R 8) [6,65,160,192,288] 13 := by
  apply FastRouting.sound _ _ [6,65,160,192,288] 13 (by decide) (choices 1) [1,8,16] r7688 c7688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1326
  · exact u1327
  · exact u1328

def b7689 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 56 49 224 224 224 480), lower := (rows 7 67 268 56 49 32 64 128 256), losses := [] }

theorem u7689 : Upper (D 8) (R 8) [6,65,264,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7689 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7690 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 268 56 81 160 224 160 416), lower := (rows 7 67 268 56 81 32 64 128 256), losses := [] }

theorem u7690 : Upper (D 8) (R 8) [6,65,264,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7691 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 268 56 112 161 225 161 417), lower := (rows 7 67 268 56 112 32 64 128 256), losses := [] }

theorem u7691 : Upper (D 8) (R 8) [6,65,264,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7692 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 56 145 224 224 224 480), lower := (rows 7 67 268 56 145 32 64 128 256), losses := [] }

theorem u7692 : Upper (D 8) (R 8) [6,65,264,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7692 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7693 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 268 56 176 225 225 225 481), lower := (rows 7 67 268 56 176 32 64 128 256), losses := [] }

theorem u7693 : Upper (D 8) (R 8) [6,65,264,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7694 : Route 9 := (fun mask => (mask,id))

def c7694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7694 : Upper (D 8) (R 8) [6,65,264,48,192] 13 := by
  apply FastRouting.sound _ _ [6,65,264,48,192] 13 (by decide) (choices 1) [1,128] r7694 c7694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1329
  · exact u1330

def b7695 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 152 49 224 224 224 480), lower := (rows 7 67 268 152 49 32 64 128 256), losses := [] }

theorem u7695 : Upper (D 8) (R 8) [6,65,264,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7695 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7696 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 268 152 81 160 224 160 416), lower := (rows 7 67 268 152 81 32 64 128 256), losses := [] }

theorem u7696 : Upper (D 8) (R 8) [6,65,264,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7696 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7697 : Route 9 := (fun mask => (mask,id))

def c7697 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7697 : Upper (D 8) (R 8) [6,65,264,144,96] 13 := by
  apply FastRouting.sound _ _ [6,65,264,144,96] 13 (by decide) (choices 1) [1,128] r7697 c7697
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1331
  · exact u1332

def b7698 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 268 152 145 96 96 224 352), lower := (rows 7 67 268 152 145 32 64 128 256), losses := [] }

theorem u7698 : Upper (D 8) (R 8) [6,65,264,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7699 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 268 152 176 97 97 225 353), lower := (rows 7 67 268 152 176 32 64 128 256), losses := [] }

theorem u7699 : Upper (D 8) (R 8) [6,65,264,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7699 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7700 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 268 152 208 33 97 161 289), lower := (rows 7 67 268 152 208 32 64 128 256), losses := [] }

theorem u7700 : Upper (D 8) (R 8) [6,65,264,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7700 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7701 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 168 49 240 240 240 496), lower := (rows 7 67 268 168 49 32 64 128 256), losses := [] }

theorem u7701 : Upper (D 8) (R 8) [6,65,264,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7701 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7702 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 268 168 81 176 240 176 432), lower := (rows 7 67 268 168 81 32 64 128 256), losses := [] }

theorem u7702 : Upper (D 8) (R 8) [6,65,264,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7702 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7703 : Route 9 := (fun mask => (mask,id))

def c7703 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7703 : Upper (D 8) (R 8) [6,65,264,160,96] 13 := by
  apply FastRouting.sound _ _ [6,65,264,160,96] 13 (by decide) (choices 1) [1,16,128] r7703 c7703
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1333
  · exact u1334
  · exact u1335

def b7704 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 268 168 145 112 112 240 368), lower := (rows 7 67 268 168 145 32 64 128 256), losses := [] }

theorem u7704 : Upper (D 8) (R 8) [6,65,264,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7705 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 268 168 176 113 113 241 369), lower := (rows 7 67 268 168 176 32 64 128 256), losses := [] }

theorem u7705 : Upper (D 8) (R 8) [6,65,264,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7705 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7706 : Route 9 := (fun mask => (mask,id))

def c7706 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7706 : Upper (D 8) (R 8) [6,65,264,160,192] 13 := by
  apply FastRouting.sound _ _ [6,65,264,160,192] 13 (by decide) (choices 1) [1,16] r7706 c7706
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1336
  · exact u1337

def b7707 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 56 224 224 224 480), lower := (rows 7 67 292 25 56 32 64 128 256), losses := [] }

theorem u7707 : Upper (D 8) (R 8) [6,65,288,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7708 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 292 25 88 160 224 160 416), lower := (rows 7 67 292 25 88 32 64 128 256), losses := [] }

theorem u7708 : Upper (D 8) (R 8) [6,65,288,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7708 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7709 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 112 168 232 168 424), lower := (rows 7 67 292 25 112 32 64 128 256), losses := [] }

theorem u7709 : Upper (D 8) (R 8) [6,65,288,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7709 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7710 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 152 224 224 224 480), lower := (rows 7 67 292 25 152 32 64 128 256), losses := [] }

theorem u7710 : Upper (D 8) (R 8) [6,65,288,17,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7711 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 176 232 232 232 488), lower := (rows 7 67 292 25 176 32 64 128 256), losses := [] }

theorem u7711 : Upper (D 8) (R 8) [6,65,288,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7712 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 25 208 168 232 168 424), lower := (rows 7 67 292 25 208 32 64 128 256), losses := [] }

theorem u7712 : Upper (D 8) (R 8) [6,65,288,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7712 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7713 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 56 240 208 208 464), lower := (rows 7 67 292 41 56 32 64 128 256), losses := [] }

theorem u7713 : Upper (D 8) (R 8) [6,65,288,33,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7713 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7714 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 88 176 240 176 432), lower := (rows 7 67 292 41 88 32 64 128 256), losses := [] }

theorem u7714 : Upper (D 8) (R 8) [6,65,288,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7714 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7715 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 112 184 216 152 408), lower := (rows 7 67 292 41 112 32 64 128 256), losses := [] }

theorem u7715 : Upper (D 8) (R 8) [6,65,288,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7715 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7716 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 152 240 240 240 496), lower := (rows 7 67 292 41 152 32 64 128 256), losses := [] }

theorem u7716 : Upper (D 8) (R 8) [6,65,288,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7716 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7717 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 176 248 216 216 472), lower := (rows 7 67 292 41 176 32 64 128 256), losses := [] }

theorem u7717 : Upper (D 8) (R 8) [6,65,288,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7718 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 41 208 184 248 184 440), lower := (rows 7 67 292 41 208 32 64 128 256), losses := [] }

theorem u7718 : Upper (D 8) (R 8) [6,65,288,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7718 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7719 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 292 56 56 225 193 193 449), lower := (rows 7 67 292 56 56 32 64 128 256), losses := [] }

theorem u7719 : Upper (D 8) (R 8) [6,65,288,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7719 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7720 : PairBound 9 := { available := 168, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 67 292 56 81 168 232 168 424), lower := (rows 7 67 292 56 81 32 64 128 256), losses := [] }

theorem u7720 : Upper (D 8) (R 8) [6,65,288,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7721 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 292 56 88 161 225 161 417), lower := (rows 7 67 292 56 88 32 64 128 256), losses := [] }

theorem u7721 : Upper (D 8) (R 8) [6,65,288,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7722 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 292 56 112 169 201 137 393), lower := (rows 7 67 292 56 112 32 64 128 256), losses := [] }

theorem u7722 : Upper (D 8) (R 8) [6,65,288,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7722 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7723 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 56 145 232 232 232 488), lower := (rows 7 67 292 56 145 32 64 128 256), losses := [] }

theorem u7723 : Upper (D 8) (R 8) [6,65,288,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7724 : Route 9 := (fun mask => (mask,id))

def c7724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7724 : Upper (D 8) (R 8) [6,65,288,48,136] 13 := by
  apply FastRouting.sound _ _ [6,65,288,48,136] 13 (by decide) (choices 1) [1,64,128] r7724 c7724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340

def b7725 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 292 56 176 233 201 201 457), lower := (rows 7 67 292 56 176 32 64 128 256), losses := [] }

theorem u7725 : Upper (D 8) (R 8) [6,65,288,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7725 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7726 : Route 9 := (fun mask => (mask,id))

def c7726 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7726 : Upper (D 8) (R 8) [6,65,288,48,192] 13 := by
  apply FastRouting.sound _ _ [6,65,288,48,192] 13 (by decide) (choices 1) [1,8,128] r7726 c7726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1341
  · exact u1342
  · exact u1343

def b7727 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 292 73 152 176 240 176 432), lower := (rows 7 67 292 73 152 32 64 128 256), losses := [] }

theorem u7727 : Upper (D 8) (R 8) [6,65,288,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7728 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 67 292 73 176 184 248 184 440), lower := (rows 7 67 292 73 176 32 64 128 256), losses := [] }

theorem u7728 : Upper (D 8) (R 8) [6,65,288,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7728 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7729 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 88 145 168 232 168 424), lower := (rows 7 67 292 88 145 32 64 128 256), losses := [] }

theorem u7729 : Upper (D 8) (R 8) [6,65,288,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7730 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 7 67 292 88 152 161 225 161 417), lower := (rows 7 67 292 88 152 32 64 128 256), losses := [] }

theorem u7730 : Upper (D 8) (R 8) [6,65,288,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7731 : Route 9 := (fun mask => (mask,id))

def c7731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7731 : Upper (D 8) (R 8) [6,65,288,80,160] 13 := by
  apply FastRouting.sound _ _ [6,65,288,80,160] 13 (by decide) (choices 1) [1,8,128] r7731 c7731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1344
  · exact u1345
  · exact u1346

def b7732 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 364, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 104 145 184 248 184 440), lower := (rows 7 67 292 104 145 32 64 128 256), losses := [] }

theorem u7732 : Upper (D 8) (R 8) [6,65,288,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7733 : Route 9 := (fun mask => (mask,id))

def c7733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7733 : Upper (D 8) (R 8) [6,65,288,96,136] 13 := by
  apply FastRouting.sound _ _ [6,65,288,96,136] 13 (by decide) (choices 1) [1,16,128] r7733 c7733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1347
  · exact u1348
  · exact u1349

def r7734 : Route 9 := (fun mask => (mask,id))

def c7734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7734 : Upper (D 8) (R 8) [6,65,288,96,160] 13 := by
  apply FastRouting.sound _ _ [6,65,288,96,160] 13 (by decide) (choices 1) [1,8,16,128] r7734 c7734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1350
  · exact u1351
  · exact u1352
  · exact u1353

def b7735 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 137 152 112 112 240 368), lower := (rows 7 67 292 137 152 32 64 128 256), losses := [] }

theorem u7735 : Upper (D 8) (R 8) [6,65,288,129,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7736 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 137 176 120 120 248 376), lower := (rows 7 67 292 137 176 32 64 128 256), losses := [] }

theorem u7736 : Upper (D 8) (R 8) [6,65,288,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7737 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 292 137 208 56 120 184 312), lower := (rows 7 67 292 137 208 32 64 128 256), losses := [] }

theorem u7737 : Upper (D 8) (R 8) [6,65,288,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7737 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7738 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 67 292 152 152 97 97 225 353), lower := (rows 7 67 292 152 152 32 64 128 256), losses := [] }

theorem u7738 : Upper (D 8) (R 8) [6,65,288,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7739 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 67 292 152 176 105 105 233 361), lower := (rows 7 67 292 152 176 32 64 128 256), losses := [] }

theorem u7739 : Upper (D 8) (R 8) [6,65,288,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7739
end Delivery.IrregularNine14.P08
