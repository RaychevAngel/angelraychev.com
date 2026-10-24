import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0099

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b16500 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 259 67 28 137 148 96 96 224 352), lower := (rows 259 67 28 137 148 32 64 128 256), losses := [] }

theorem u16500 : Upper (D 8) (R 8) [258,65,24,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16501 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 28 137 176 100 100 228 356), lower := (rows 259 67 28 137 176 32 64 128 256), losses := [] }

theorem u16501 : Upper (D 8) (R 8) [258,65,24,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16501 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16502 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 28 137 208 36 100 164 292), lower := (rows 259 67 28 137 208 32 64 128 256), losses := [] }

theorem u16502 : Upper (D 8) (R 8) [258,65,24,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16502 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16503 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 140 176 97 97 225 353), lower := (rows 259 67 28 140 176 32 64 128 256), losses := [] }

theorem u16503 : Upper (D 8) (R 8) [258,65,24,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16503 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16504 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 140 208 33 97 161 289), lower := (rows 259 67 28 140 208 32 64 128 256), losses := [] }

theorem u16504 : Upper (D 8) (R 8) [258,65,24,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16505 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 28 168 176 101 101 229 357), lower := (rows 259 67 28 168 176 32 64 128 256), losses := [] }

theorem u16505 : Upper (D 8) (R 8) [258,65,24,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16506 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 28 168 208 37 101 165 293), lower := (rows 259 67 28 168 208 32 64 128 256), losses := [] }

theorem u16506 : Upper (D 8) (R 8) [258,65,24,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16507 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 88 176 240 176 432), lower := (rows 259 67 37 44 88 32 64 128 256), losses := [] }

theorem u16507 : Upper (D 8) (R 8) [258,65,33,36,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16508 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 112 184 216 152 408), lower := (rows 259 67 37 44 112 32 64 128 256), losses := [] }

theorem u16508 : Upper (D 8) (R 8) [258,65,33,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16509 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 152 240 240 240 496), lower := (rows 259 67 37 44 152 32 64 128 256), losses := [] }

theorem u16509 : Upper (D 8) (R 8) [258,65,33,36,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16510 : PairBound 9 := { available := 216, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 176 248 216 216 472), lower := (rows 259 67 37 44 176 32 64 128 256), losses := [] }

theorem u16510 : Upper (D 8) (R 8) [258,65,33,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16510 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16511 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 44 208 184 248 184 440), lower := (rows 259 67 37 44 208 32 64 128 256), losses := [] }

theorem u16511 : Upper (D 8) (R 8) [258,65,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16511 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16512 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 56 84 168 232 168 424), lower := (rows 259 67 37 56 84 32 64 128 256), losses := [] }

theorem u16512 : Upper (D 8) (R 8) [258,65,33,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16512 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16513 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 56 148 232 232 232 488), lower := (rows 259 67 37 56 148 32 64 128 256), losses := [] }

theorem u16513 : Upper (D 8) (R 8) [258,65,33,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16514 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 56 152 228 228 228 484), lower := (rows 259 67 37 56 152 32 64 128 256), losses := [] }

theorem u16514 : Upper (D 8) (R 8) [258,65,33,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16515 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 56 208 172 236 172 428), lower := (rows 259 67 37 56 208 32 64 128 256), losses := [] }

theorem u16515 : Upper (D 8) (R 8) [258,65,33,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16516 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 76 152 176 240 176 432), lower := (rows 259 67 37 76 152 32 64 128 256), losses := [] }

theorem u16516 : Upper (D 8) (R 8) [258,65,33,68,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16517 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 76 176 184 248 184 440), lower := (rows 259 67 37 76 176 32 64 128 256), losses := [] }

theorem u16517 : Upper (D 8) (R 8) [258,65,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16518 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 88 148 168 232 168 424), lower := (rows 259 67 37 88 148 32 64 128 256), losses := [] }

theorem u16518 : Upper (D 8) (R 8) [258,65,33,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16518 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16519 : PairBound 9 := { available := 172, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 88 176 172 236 172 428), lower := (rows 259 67 37 88 176 32 64 128 256), losses := [] }

theorem u16519 : Upper (D 8) (R 8) [258,65,33,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16519 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16520 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 104 148 184 248 184 440), lower := (rows 259 67 37 104 148 32 64 128 256), losses := [] }

theorem u16520 : Upper (D 8) (R 8) [258,65,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16521 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 104 152 180 244 180 436), lower := (rows 259 67 37 104 152 32 64 128 256), losses := [] }

theorem u16521 : Upper (D 8) (R 8) [258,65,33,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16522 : PairBound 9 := { available := 156, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 104 176 188 220 156 412), lower := (rows 259 67 37 104 176 32 64 128 256), losses := [] }

theorem u16522 : Upper (D 8) (R 8) [258,65,33,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16523 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 140 176 120 120 248 376), lower := (rows 259 67 37 140 176 32 64 128 256), losses := [] }

theorem u16523 : Upper (D 8) (R 8) [258,65,33,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16523 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16524 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 140 208 56 120 184 312), lower := (rows 259 67 37 140 208 32 64 128 256), losses := [] }

theorem u16524 : Upper (D 8) (R 8) [258,65,33,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16524 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16525 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 216, targets := 1 }], pairs := [(3,0)], upper := (rows 259 67 37 168 208 60 124 188 316), lower := (rows 259 67 37 168 208 32 64 128 256), losses := [] }

theorem u16525 : Upper (D 8) (R 8) [258,65,33,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16525 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16526 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 44 112 177 209 145 401), lower := (rows 259 67 44 44 112 32 64 128 256), losses := [] }

theorem u16526 : Upper (D 8) (R 8) [258,65,40,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16527 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 44 176 241 209 209 465), lower := (rows 259 67 44 44 176 32 64 128 256), losses := [] }

theorem u16527 : Upper (D 8) (R 8) [258,65,40,36,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16528 : PairBound 9 := { available := 177, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 44 208 177 241 177 433), lower := (rows 259 67 44 44 208 32 64 128 256), losses := [] }

theorem u16528 : Upper (D 8) (R 8) [258,65,40,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16529 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 84 161 225 161 417), lower := (rows 259 67 44 56 84 32 64 128 256), losses := [] }

theorem u16529 : Upper (D 8) (R 8) [258,65,40,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16530 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 112 165 197 133 389), lower := (rows 259 67 44 56 112 32 64 128 256), losses := [] }

theorem u16530 : Upper (D 8) (R 8) [258,65,40,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16530 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16531 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 148 225 225 225 481), lower := (rows 259 67 44 56 148 32 64 128 256), losses := [] }

theorem u16531 : Upper (D 8) (R 8) [258,65,40,48,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16531 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16532 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 176 229 197 197 453), lower := (rows 259 67 44 56 176 32 64 128 256), losses := [] }

theorem u16532 : Upper (D 8) (R 8) [258,65,40,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16533 : PairBound 9 := { available := 165, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 56 208 165 229 165 421), lower := (rows 259 67 44 56 208 32 64 128 256), losses := [] }

theorem u16533 : Upper (D 8) (R 8) [258,65,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16534 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 44 73 148 176 240 176 432), lower := (rows 259 67 44 73 148 32 64 128 256), losses := [] }

theorem u16534 : Upper (D 8) (R 8) [258,65,40,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16535 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 67 44 73 176 180 244 180 436), lower := (rows 259 67 44 73 176 32 64 128 256), losses := [] }

theorem u16535 : Upper (D 8) (R 8) [258,65,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16536 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 44 76 176 177 241 177 433), lower := (rows 259 67 44 76 176 32 64 128 256), losses := [] }

theorem u16536 : Upper (D 8) (R 8) [258,65,40,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16537 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 88 145 164 228 164 420), lower := (rows 259 67 44 88 145 32 64 128 256), losses := [] }

theorem u16537 : Upper (D 8) (R 8) [258,65,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16537 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16538 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 44 88 148 161 225 161 417), lower := (rows 259 67 44 88 148 32 64 128 256), losses := [] }

theorem u16538 : Upper (D 8) (R 8) [258,65,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16539 : Route 9 := (fun mask => (mask,id))

def c16539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16539 : Upper (D 8) (R 8) [258,65,40,80,160] 13 := by
  apply FastRouting.sound _ _ [258,65,40,80,160] 13 (by decide) (choices 1) [1,4,128] r16539 c16539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5974
  · exact u5975
  · exact u5976

def b16540 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 104 148 177 241 177 433), lower := (rows 259 67 44 104 148 32 64 128 256), losses := [] }

theorem u16540 : Upper (D 8) (R 8) [258,65,40,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16541 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 104 176 181 213 149 405), lower := (rows 259 67 44 104 176 32 64 128 256), losses := [] }

theorem u16541 : Upper (D 8) (R 8) [258,65,40,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16541 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16542 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 84 176 240 176 432), lower := (rows 259 67 44 137 84 32 64 128 256), losses := [] }

theorem u16542 : Upper (D 8) (R 8) [258,65,40,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16543 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 112 180 244 180 436), lower := (rows 259 67 44 137 112 32 64 128 256), losses := [] }

theorem u16543 : Upper (D 8) (R 8) [258,65,40,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16543 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16544 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 148 112 112 240 368), lower := (rows 259 67 44 137 148 32 64 128 256), losses := [] }

theorem u16544 : Upper (D 8) (R 8) [258,65,40,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16545 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 176 116 116 244 372), lower := (rows 259 67 44 137 176 32 64 128 256), losses := [] }

theorem u16545 : Upper (D 8) (R 8) [258,65,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16545 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16546 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 137 208 52 116 180 308), lower := (rows 259 67 44 137 208 32 64 128 256), losses := [] }

theorem u16546 : Upper (D 8) (R 8) [258,65,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16547 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 67 44 140 81 176 240 176 432), lower := (rows 259 67 44 140 81 32 64 128 256), losses := [] }

theorem u16547 : Upper (D 8) (R 8) [258,65,40,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16548 : Route 9 := (fun mask => (mask,id))

def c16548 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16548 : Upper (D 8) (R 8) [258,65,40,132,96] 13 := by
  apply FastRouting.sound _ _ [258,65,40,132,96] 13 (by decide) (choices 1) [1,16,128] r16548 c16548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5977
  · exact u5978
  · exact u5979

def b16549 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 140 145 112 112 240 368), lower := (rows 259 67 44 140 145 32 64 128 256), losses := [] }

theorem u16549 : Upper (D 8) (R 8) [258,65,40,132,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16550 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 140 176 113 113 241 369), lower := (rows 259 67 44 140 176 32 64 128 256), losses := [] }

theorem u16550 : Upper (D 8) (R 8) [258,65,40,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16551 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 140 208 49 113 177 305), lower := (rows 259 67 44 140 208 32 64 128 256), losses := [] }

theorem u16551 : Upper (D 8) (R 8) [258,65,40,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16551 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16552 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 67 44 152 81 164 228 164 420), lower := (rows 259 67 44 152 81 32 64 128 256), losses := [] }

theorem u16552 : Upper (D 8) (R 8) [258,65,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16553 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 259 67 44 152 84 161 225 161 417), lower := (rows 259 67 44 152 84 32 64 128 256), losses := [] }

theorem u16553 : Upper (D 8) (R 8) [258,65,40,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r16554 : Route 9 := (fun mask => (mask,id))

def c16554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u16554 : Upper (D 8) (R 8) [258,65,40,144,96] 13 := by
  apply FastRouting.sound _ _ [258,65,40,144,96] 13 (by decide) (choices 1) [1,4,128] r16554 c16554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5980
  · exact u5981
  · exact u5982

def b16555 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 152 145 100 100 228 356), lower := (rows 259 67 44 152 145 32 64 128 256), losses := [] }

theorem u16555 : Upper (D 8) (R 8) [258,65,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16555 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16556 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 152 148 97 97 225 353), lower := (rows 259 67 44 152 148 32 64 128 256), losses := [] }

theorem u16556 : Upper (D 8) (R 8) [258,65,40,144,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16557 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 152 176 101 101 229 357), lower := (rows 259 67 44 152 176 32 64 128 256), losses := [] }

theorem u16557 : Upper (D 8) (R 8) [258,65,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16558 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 67 44 152 208 37 101 165 293), lower := (rows 259 67 44 152 208 32 64 128 256), losses := [] }

theorem u16558 : Upper (D 8) (R 8) [258,65,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16559 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 67 44 168 84 177 241 177 433), lower := (rows 259 67 44 168 84 32 64 128 256), losses := [] }

theorem u16559 : Upper (D 8) (R 8) [258,65,40,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u16559
end Delivery.IrregularNine14.P08
