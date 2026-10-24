import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0069
import IrregularNine14P08C0070

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12780 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 88 400 169 233 169 425), lower := (rows 97 7 38 88 400 32 64 128 256), losses := [] }

theorem u12780 : Upper (D 8) (R 8) [96,5,34,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12780 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12781 : PairBound 9 := { available := 344, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 176 376 344 472 344), lower := (rows 97 7 38 137 176 32 64 128 256), losses := [] }

theorem u12781 : Upper (D 8) (R 8) [96,5,34,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12781 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12782 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 208 312 376 440 312), lower := (rows 97 7 38 137 208 32 64 128 256), losses := [] }

theorem u12782 : Upper (D 8) (R 8) [96,5,34,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12782 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12783 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 280 240 240 240 496), lower := (rows 97 7 38 137 280 32 64 128 256), losses := [] }

theorem u12783 : Upper (D 8) (R 8) [96,5,34,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12783 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12784 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 304 248 216 216 472), lower := (rows 97 7 38 137 304 32 64 128 256), losses := [] }

theorem u12784 : Upper (D 8) (R 8) [96,5,34,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12784 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12785 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 336 184 248 184 440), lower := (rows 97 7 38 137 336 32 64 128 256), losses := [] }

theorem u12785 : Upper (D 8) (R 8) [96,5,34,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12785 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12786 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 400 120 120 248 376), lower := (rows 97 7 38 137 400 32 64 128 256), losses := [] }

theorem u12786 : Upper (D 8) (R 8) [96,5,34,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12786 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12787 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 273 232 232 232 488), lower := (rows 97 7 38 152 273 32 64 128 256), losses := [] }

theorem u12787 : Upper (D 8) (R 8) [96,5,34,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12787 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12788 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 280 225 225 225 481), lower := (rows 97 7 38 152 280 32 64 128 256), losses := [] }

theorem u12788 : Upper (D 8) (R 8) [96,5,34,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12788 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12789 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 304 233 201 201 457), lower := (rows 97 7 38 152 304 32 64 128 256), losses := [] }

theorem u12789 : Upper (D 8) (R 8) [96,5,34,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12789 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12790 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 152 336 169 233 169 425), lower := (rows 97 7 38 152 336 32 64 128 256), losses := [] }

theorem u12790 : Upper (D 8) (R 8) [96,5,34,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12790 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12791 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 208 313 345 409 281), lower := (rows 97 7 38 168 208 32 64 128 256), losses := [] }

theorem u12791 : Upper (D 8) (R 8) [96,5,34,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12791 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12792 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 273 248 216 216 472), lower := (rows 97 7 38 168 273 32 64 128 256), losses := [] }

theorem u12792 : Upper (D 8) (R 8) [96,5,34,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12792 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12793 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 280 241 209 209 465), lower := (rows 97 7 38 168 280 32 64 128 256), losses := [] }

theorem u12793 : Upper (D 8) (R 8) [96,5,34,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12793 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12794 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 336 185 217 153 409), lower := (rows 97 7 38 168 336 32 64 128 256), losses := [] }

theorem u12794 : Upper (D 8) (R 8) [96,5,34,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12794 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12795 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 168 400 121 89 217 345), lower := (rows 97 7 38 168 400 32 64 128 256), losses := [] }

theorem u12795 : Upper (D 8) (R 8) [96,5,34,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12795 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12796 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 273 184 248 184 440), lower := (rows 97 7 38 200 273 32 64 128 256), losses := [] }

theorem u12796 : Upper (D 8) (R 8) [96,5,34,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12796 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12797 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 280 177 241 177 433), lower := (rows 97 7 38 200 280 32 64 128 256), losses := [] }

theorem u12797 : Upper (D 8) (R 8) [96,5,34,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12797 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12798 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 304 185 217 153 409), lower := (rows 97 7 38 200 304 32 64 128 256), losses := [] }

theorem u12798 : Upper (D 8) (R 8) [96,5,34,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12798 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12799 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 400 57 121 185 313), lower := (rows 97 7 38 200 400 32 64 128 256), losses := [] }

theorem u12799 : Upper (D 8) (R 8) [96,5,34,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12799 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12800 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 25 50 480 448 448 448), lower := (rows 97 7 44 25 50 32 64 128 256), losses := [] }

theorem u12800 : Upper (D 8) (R 8) [96,5,40,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12800 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12801 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 25 82 416 480 416 416), lower := (rows 97 7 44 25 82 32 64 128 256), losses := [] }

theorem u12801 : Upper (D 8) (R 8) [96,5,40,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12802 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 146 480 480 480 480), lower := (rows 97 7 44 25 146 32 64 128 256), losses := [] }

theorem u12802 : Upper (D 8) (R 8) [96,5,40,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12803 : PairBound 9 := { available := 450, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 176 482 450 450 450), lower := (rows 97 7 44 25 176 32 64 128 256), losses := [] }

theorem u12803 : Upper (D 8) (R 8) [96,5,40,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12803 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12804 : PairBound 9 := { available := 418, camps := [{ cop := 3, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 25 208 418 482 418 418), lower := (rows 97 7 44 25 208 32 64 128 256), losses := [] }

theorem u12804 : Upper (D 8) (R 8) [96,5,40,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12805 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 274 224 224 224 480), lower := (rows 97 7 44 25 274 32 64 128 256), losses := [] }

theorem u12805 : Upper (D 8) (R 8) [96,5,40,17,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12806 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 304 226 194 194 450), lower := (rows 97 7 44 25 304 32 64 128 256), losses := [] }

theorem u12806 : Upper (D 8) (R 8) [96,5,40,17,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12807 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 25 336 162 226 162 418), lower := (rows 97 7 44 25 336 32 64 128 256), losses := [] }

theorem u12807 : Upper (D 8) (R 8) [96,5,40,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12808 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 25 400 226 226 226 482), lower := (rows 97 7 44 25 400 32 64 128 256), losses := [] }

theorem u12808 : Upper (D 8) (R 8) [96,5,40,17,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12809 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 30, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 26 49 480 448 448 448), lower := (rows 97 7 44 26 49 32 64 128 256), losses := [] }

theorem u12809 : Upper (D 8) (R 8) [96,5,40,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12810 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 26 81 416 480 416 416), lower := (rows 97 7 44 26 81 32 64 128 256), losses := [] }

theorem u12810 : Upper (D 8) (R 8) [96,5,40,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12811 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 26 112 417 449 385 385), lower := (rows 97 7 44 26 112 32 64 128 256), losses := [] }

theorem u12811 : Upper (D 8) (R 8) [96,5,40,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12812 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 484, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 26 145 480 480 480 480), lower := (rows 97 7 44 26 145 32 64 128 256), losses := [] }

theorem u12812 : Upper (D 8) (R 8) [96,5,40,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12813 : Route 9 := (fun mask => (mask,id))

def c12813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u12813 : Upper (D 8) (R 8) [96,5,40,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,160] 13 (by decide) (choices 1) [1,64,128,256] r12813 c12813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4197
  · exact u4198
  · exact u4199
  · exact u4200

def b12814 : PairBound 9 := { available := 417, camps := [], pairs := [(2,6)], upper := (rows 97 7 44 26 208 417 481 417 417), lower := (rows 97 7 44 26 208 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 144 32 0 128 256) }] }

theorem u12814 : Upper (D 8) (R 8) [96,5,40,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12815 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 26 273 224 224 224 480), lower := (rows 97 7 44 26 273 32 64 128 256), losses := [] }

theorem u12815 : Upper (D 8) (R 8) [96,5,40,18,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12816 : Route 9 := (fun mask => (mask,id))

def c12816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12816 : Upper (D 8) (R 8) [96,5,40,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,288] 13 (by decide) (choices 1) [1,64,128] r12816 c12816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4201
  · exact u4202
  · exact u4203

def b12817 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 97 7 44 26 336 161 225 161 417), lower := (rows 97 7 44 26 336 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 44 446 272 32 0 128 256) }] }

theorem u12817 : Upper (D 8) (R 8) [96,5,40,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12818 : Route 9 := (fun mask => (mask,id))

def c12818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12818 : Upper (D 8) (R 8) [96,5,40,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,40,18,384] 13 (by decide) (choices 1) [1,64,128] r12818 c12818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4204
  · exact u4205
  · exact u4206

def b12819 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 41 82 432 464 400 400), lower := (rows 97 7 44 41 82 32 64 128 256), losses := [] }

theorem u12819 : Upper (D 8) (R 8) [96,5,40,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12820 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 146 496 464 464 464), lower := (rows 97 7 44 41 146 32 64 128 256), losses := [] }

theorem u12820 : Upper (D 8) (R 8) [96,5,40,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12820 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12821 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 208 434 466 402 402), lower := (rows 97 7 44 41 208 32 64 128 256), losses := [] }

theorem u12821 : Upper (D 8) (R 8) [96,5,40,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12822 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 274 240 208 208 464), lower := (rows 97 7 44 41 274 32 64 128 256), losses := [] }

theorem u12822 : Upper (D 8) (R 8) [96,5,40,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12823 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 336 178 210 146 402), lower := (rows 97 7 44 41 336 32 64 128 256), losses := [] }

theorem u12823 : Upper (D 8) (R 8) [96,5,40,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12824 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 41 400 242 210 210 466), lower := (rows 97 7 44 41 400 32 64 128 256), losses := [] }

theorem u12824 : Upper (D 8) (R 8) [96,5,40,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12824 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12825 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 145 496 464 464 464), lower := (rows 97 7 44 42 145 32 64 128 256), losses := [] }

theorem u12825 : Upper (D 8) (R 8) [96,5,40,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12826 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 208 433 465 401 401), lower := (rows 97 7 44 42 208 32 64 128 256), losses := [] }

theorem u12826 : Upper (D 8) (R 8) [96,5,40,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12827 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 273 240 208 208 464), lower := (rows 97 7 44 42 273 32 64 128 256), losses := [] }

theorem u12827 : Upper (D 8) (R 8) [96,5,40,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12828 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 336 177 209 145 401), lower := (rows 97 7 44 42 336 32 64 128 256), losses := [] }

theorem u12828 : Upper (D 8) (R 8) [96,5,40,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12829 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 42 400 241 209 209 465), lower := (rows 97 7 44 42 400 32 64 128 256), losses := [] }

theorem u12829 : Upper (D 8) (R 8) [96,5,40,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12830 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 56 82 417 449 385 385), lower := (rows 97 7 44 56 82 32 64 128 256), losses := [] }

theorem u12830 : Upper (D 8) (R 8) [96,5,40,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12831 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 145 482 450 450 450), lower := (rows 97 7 44 56 145 32 64 128 256), losses := [] }

theorem u12831 : Upper (D 8) (R 8) [96,5,40,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12832 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 146 481 449 449 449), lower := (rows 97 7 44 56 146 32 64 128 256), losses := [] }

theorem u12832 : Upper (D 8) (R 8) [96,5,40,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12833 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 208 419 451 387 387), lower := (rows 97 7 44 56 208 32 64 128 256), losses := [] }

theorem u12833 : Upper (D 8) (R 8) [96,5,40,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12833 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12834 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 273 226 194 194 450), lower := (rows 97 7 44 56 273 32 64 128 256), losses := [] }

theorem u12834 : Upper (D 8) (R 8) [96,5,40,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12835 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 274 225 193 193 449), lower := (rows 97 7 44 56 274 32 64 128 256), losses := [] }

theorem u12835 : Upper (D 8) (R 8) [96,5,40,48,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12836 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 336 163 195 131 387), lower := (rows 97 7 44 56 336 32 64 128 256), losses := [] }

theorem u12836 : Upper (D 8) (R 8) [96,5,40,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12836 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12837 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 56 400 227 195 195 451), lower := (rows 97 7 44 56 400 32 64 128 256), losses := [] }

theorem u12837 : Upper (D 8) (R 8) [96,5,40,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12838 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 50 432 464 400 400), lower := (rows 97 7 44 73 50 32 64 128 256), losses := [] }

theorem u12838 : Upper (D 8) (R 8) [96,5,40,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12838 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12839 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 146 432 496 432 432), lower := (rows 97 7 44 73 146 32 64 128 256), losses := [] }

theorem u12839 : Upper (D 8) (R 8) [96,5,40,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12839
end Delivery.IrregularNine14.P08
