import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0070

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12840 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 176 434 466 402 402), lower := (rows 97 7 44 73 176 32 64 128 256), losses := [] }

theorem u12840 : Upper (D 8) (R 8) [96,5,40,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12841 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 274 176 240 176 432), lower := (rows 97 7 44 73 274 32 64 128 256), losses := [] }

theorem u12841 : Upper (D 8) (R 8) [96,5,40,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12841 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12842 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 304 178 210 146 402), lower := (rows 97 7 44 73 304 32 64 128 256), losses := [] }

theorem u12842 : Upper (D 8) (R 8) [96,5,40,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12843 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 73 400 178 242 178 434), lower := (rows 97 7 44 73 400 32 64 128 256), losses := [] }

theorem u12843 : Upper (D 8) (R 8) [96,5,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12844 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 145 432 496 432 432), lower := (rows 97 7 44 74 145 32 64 128 256), losses := [] }

theorem u12844 : Upper (D 8) (R 8) [96,5,40,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12845 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 176 433 465 401 401), lower := (rows 97 7 44 74 176 32 64 128 256), losses := [] }

theorem u12845 : Upper (D 8) (R 8) [96,5,40,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12846 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 273 176 240 176 432), lower := (rows 97 7 44 74 273 32 64 128 256), losses := [] }

theorem u12846 : Upper (D 8) (R 8) [96,5,40,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12847 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 304 177 209 145 401), lower := (rows 97 7 44 74 304 32 64 128 256), losses := [] }

theorem u12847 : Upper (D 8) (R 8) [96,5,40,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12848 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 400 177 241 177 433), lower := (rows 97 7 44 74 400 32 64 128 256), losses := [] }

theorem u12848 : Upper (D 8) (R 8) [96,5,40,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12849 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 30, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 88 50 417 449 385 385), lower := (rows 97 7 44 88 50 32 64 128 256), losses := [] }

theorem u12849 : Upper (D 8) (R 8) [96,5,40,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12850 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 145 418 482 418 418), lower := (rows 97 7 44 88 145 32 64 128 256), losses := [] }

theorem u12850 : Upper (D 8) (R 8) [96,5,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12851 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 146 417 481 417 417), lower := (rows 97 7 44 88 146 32 64 128 256), losses := [] }

theorem u12851 : Upper (D 8) (R 8) [96,5,40,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12852 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 176 419 451 387 387), lower := (rows 97 7 44 88 176 32 64 128 256), losses := [] }

theorem u12852 : Upper (D 8) (R 8) [96,5,40,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12853 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 273 162 226 162 418), lower := (rows 97 7 44 88 273 32 64 128 256), losses := [] }

theorem u12853 : Upper (D 8) (R 8) [96,5,40,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12853 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12854 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 274 161 225 161 417), lower := (rows 97 7 44 88 274 32 64 128 256), losses := [] }

theorem u12854 : Upper (D 8) (R 8) [96,5,40,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12855 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 304 163 195 131 387), lower := (rows 97 7 44 88 304 32 64 128 256), losses := [] }

theorem u12855 : Upper (D 8) (R 8) [96,5,40,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12856 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 88 400 163 227 163 419), lower := (rows 97 7 44 88 400 32 64 128 256), losses := [] }

theorem u12856 : Upper (D 8) (R 8) [96,5,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12857 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 145 434 466 402 402), lower := (rows 97 7 44 104 145 32 64 128 256), losses := [] }

theorem u12857 : Upper (D 8) (R 8) [96,5,40,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12857 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12858 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 146 433 465 401 401), lower := (rows 97 7 44 104 146 32 64 128 256), losses := [] }

theorem u12858 : Upper (D 8) (R 8) [96,5,40,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12859 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 273 178 210 146 402), lower := (rows 97 7 44 104 273 32 64 128 256), losses := [] }

theorem u12859 : Upper (D 8) (R 8) [96,5,40,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12860 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 274 177 209 145 401), lower := (rows 97 7 44 104 274 32 64 128 256), losses := [] }

theorem u12860 : Upper (D 8) (R 8) [96,5,40,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12860 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12861 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 104 400 179 211 147 403), lower := (rows 97 7 44 104 400 32 64 128 256), losses := [] }

theorem u12861 : Upper (D 8) (R 8) [96,5,40,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12861 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12862 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 50 496 464 464 464), lower := (rows 97 7 44 137 50 32 64 128 256), losses := [] }

theorem u12862 : Upper (D 8) (R 8) [96,5,40,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12862 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12863 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 82 432 496 432 432), lower := (rows 97 7 44 137 82 32 64 128 256), losses := [] }

theorem u12863 : Upper (D 8) (R 8) [96,5,40,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12863 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12864 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 146 368 368 496 368), lower := (rows 97 7 44 137 146 32 64 128 256), losses := [] }

theorem u12864 : Upper (D 8) (R 8) [96,5,40,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12864 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12865 : PairBound 9 := { available := 338, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 176 370 338 466 338), lower := (rows 97 7 44 137 176 32 64 128 256), losses := [] }

theorem u12865 : Upper (D 8) (R 8) [96,5,40,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12865 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12866 : PairBound 9 := { available := 306, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 208 306 370 434 306), lower := (rows 97 7 44 137 208 32 64 128 256), losses := [] }

theorem u12866 : Upper (D 8) (R 8) [96,5,40,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12866 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12867 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 274 240 240 240 496), lower := (rows 97 7 44 137 274 32 64 128 256), losses := [] }

theorem u12867 : Upper (D 8) (R 8) [96,5,40,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12867 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12868 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 304 242 210 210 466), lower := (rows 97 7 44 137 304 32 64 128 256), losses := [] }

theorem u12868 : Upper (D 8) (R 8) [96,5,40,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12868 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12869 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 336 178 242 178 434), lower := (rows 97 7 44 137 336 32 64 128 256), losses := [] }

theorem u12869 : Upper (D 8) (R 8) [96,5,40,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12869 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12870 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 137 400 114 114 242 370), lower := (rows 97 7 44 137 400 32 64 128 256), losses := [] }

theorem u12870 : Upper (D 8) (R 8) [96,5,40,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12870 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12871 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 138 49 496 464 464 464), lower := (rows 97 7 44 138 49 32 64 128 256), losses := [] }

theorem u12871 : Upper (D 8) (R 8) [96,5,40,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12871 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12872 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 138 81 432 496 432 432), lower := (rows 97 7 44 138 81 32 64 128 256), losses := [] }

theorem u12872 : Upper (D 8) (R 8) [96,5,40,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12872 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12873 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 138 112 433 465 401 401), lower := (rows 97 7 44 138 112 32 64 128 256), losses := [] }

theorem u12873 : Upper (D 8) (R 8) [96,5,40,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12873 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12874 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 145 368 368 496 368), lower := (rows 97 7 44 138 145 32 64 128 256), losses := [] }

theorem u12874 : Upper (D 8) (R 8) [96,5,40,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12874 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12875 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 176 369 337 465 337), lower := (rows 97 7 44 138 176 32 64 128 256), losses := [] }

theorem u12875 : Upper (D 8) (R 8) [96,5,40,130,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12875 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12876 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 208 305 369 433 305), lower := (rows 97 7 44 138 208 32 64 128 256), losses := [] }

theorem u12876 : Upper (D 8) (R 8) [96,5,40,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12876 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12877 : Route 9 := (fun mask => (mask,id))

def c12877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12877 : Upper (D 8) (R 8) [96,5,40,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,257] 13 (by decide) (choices 1) [16,64,128] r12877 c12877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4207
  · exact u4208
  · exact u4209

def r12878 : Route 9 := (fun mask => (mask,id))

def c12878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12878 : Upper (D 8) (R 8) [96,5,40,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,288] 13 (by decide) (choices 1) [1,16,64,128] r12878 c12878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4210
  · exact u4211
  · exact u4212
  · exact u4213

def r12879 : Route 9 := (fun mask => (mask,id))

def c12879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12879 : Upper (D 8) (R 8) [96,5,40,130,320] 13 := by
  apply FastRouting.sound _ _ [96,5,40,130,320] 13 (by decide) (choices 1) [1,16,128] r12879 c12879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4214
  · exact u4215
  · exact u4216

def b12880 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 138 400 113 113 241 369), lower := (rows 97 7 44 138 400 32 64 128 256), losses := [] }

theorem u12880 : Upper (D 8) (R 8) [96,5,40,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12880 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12881 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 44 152 49 482 450 450 450), lower := (rows 97 7 44 152 49 32 64 128 256), losses := [] }

theorem u12881 : Upper (D 8) (R 8) [96,5,40,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12881 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12882 : PairBound 9 := { available := 449, camps := [], pairs := [(3,5)], upper := (rows 97 7 44 152 50 481 449 449 449), lower := (rows 97 7 44 152 50 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 24 16 0 67 131 259), good := (rows 449 455 12 152 474 0 64 128 256) }] }

theorem u12882 : Upper (D 8) (R 8) [96,5,40,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12882 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12883 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 44 152 81 418 482 418 418), lower := (rows 97 7 44 152 81 32 64 128 256), losses := [] }

theorem u12883 : Upper (D 8) (R 8) [96,5,40,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12883 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12884 : PairBound 9 := { available := 417, camps := [], pairs := [(2,6)], upper := (rows 97 7 44 152 82 417 481 417 417), lower := (rows 97 7 44 152 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 44 156 446 32 0 128 256) }] }

theorem u12884 : Upper (D 8) (R 8) [96,5,40,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12884 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12885 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 7 44 152 112 419 451 387 387), lower := (rows 97 7 44 152 112 32 64 128 256), losses := [] }

theorem u12885 : Upper (D 8) (R 8) [96,5,40,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12885 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12886 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 145 354 354 482 354), lower := (rows 97 7 44 152 145 32 64 128 256), losses := [] }

theorem u12886 : Upper (D 8) (R 8) [96,5,40,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12886 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12887 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 146 353 353 481 353), lower := (rows 97 7 44 152 146 32 64 128 256), losses := [] }

theorem u12887 : Upper (D 8) (R 8) [96,5,40,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12887 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12888 : PairBound 9 := { available := 323, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 152 176 355 323 451 323), lower := (rows 97 7 44 152 176 32 64 128 256), losses := [] }

theorem u12888 : Upper (D 8) (R 8) [96,5,40,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12888 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12889 : PairBound 9 := { available := 291, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 208 291 355 419 291), lower := (rows 97 7 44 152 208 32 64 128 256), losses := [] }

theorem u12889 : Upper (D 8) (R 8) [96,5,40,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12889 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12890 : Route 9 := (fun mask => (mask,id))

def c12890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12890 : Upper (D 8) (R 8) [96,5,40,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,257] 13 (by decide) (choices 1) [2,64,128] r12890 c12890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4217
  · exact u4218
  · exact u4219

def r12891 : Route 9 := (fun mask => (mask,id))

def c12891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12891 : Upper (D 8) (R 8) [96,5,40,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,258] 13 (by decide) (choices 1) [1,64,128] r12891 c12891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4220
  · exact u4221
  · exact u4222

def r12892 : Route 9 := (fun mask => (mask,id))

def c12892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12892 : Upper (D 8) (R 8) [96,5,40,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,288] 13 (by decide) (choices 1) [1,2,64,128] r12892 c12892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4223
  · exact u4224
  · exact u4225
  · exact u4226

def r12893 : Route 9 := (fun mask => (mask,id))

def c12893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12893 : Upper (D 8) (R 8) [96,5,40,144,320] 13 := by
  apply FastRouting.sound _ _ [96,5,40,144,320] 13 (by decide) (choices 1) [1,2,128] r12893 c12893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4227
  · exact u4228
  · exact u4229

def b12894 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 44 152 400 99 99 227 355), lower := (rows 97 7 44 152 400 32 64 128 256), losses := [] }

theorem u12894 : Upper (D 8) (R 8) [96,5,40,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12894 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12895 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 82 433 465 401 401), lower := (rows 97 7 44 168 82 32 64 128 256), losses := [] }

theorem u12895 : Upper (D 8) (R 8) [96,5,40,160,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12895 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12896 : PairBound 9 := { available := 338, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 145 370 338 466 338), lower := (rows 97 7 44 168 145 32 64 128 256), losses := [] }

theorem u12896 : Upper (D 8) (R 8) [96,5,40,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12896 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12897 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 146 369 337 465 337), lower := (rows 97 7 44 168 146 32 64 128 256), losses := [] }

theorem u12897 : Upper (D 8) (R 8) [96,5,40,160,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12897 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12898 : PairBound 9 := { available := 275, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 208 307 339 403 275), lower := (rows 97 7 44 168 208 32 64 128 256), losses := [] }

theorem u12898 : Upper (D 8) (R 8) [96,5,40,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12898 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12899 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 7 44 168 273 242 210 210 466), lower := (rows 97 7 44 168 273 32 64 128 256), losses := [] }

theorem u12899 : Upper (D 8) (R 8) [96,5,40,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12899 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12899
end Delivery.IrregularNine14.P08
