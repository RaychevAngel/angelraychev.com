import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0079

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14100 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 265 146 112 112 240 368), lower := (rows 97 14 133 265 146 32 64 128 256), losses := [] }

theorem u14100 : Upper (D 8) (R 8) [96,12,129,257,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14101 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 176 114 114 242 370), lower := (rows 97 14 133 265 176 32 64 128 256), losses := [] }

theorem u14101 : Upper (D 8) (R 8) [96,12,129,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14101 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14102 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 265 208 50 114 178 306), lower := (rows 97 14 133 265 208 32 64 128 256), losses := [] }

theorem u14102 : Upper (D 8) (R 8) [96,12,129,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14103 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 266 49 240 240 240 496), lower := (rows 97 14 133 266 49 32 64 128 256), losses := [] }

theorem u14103 : Upper (D 8) (R 8) [96,12,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14103 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14104 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 266 81 176 240 176 432), lower := (rows 97 14 133 266 81 32 64 128 256), losses := [] }

theorem u14104 : Upper (D 8) (R 8) [96,12,129,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14105 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 266 112 177 241 177 433), lower := (rows 97 14 133 266 112 32 64 128 256), losses := [] }

theorem u14105 : Upper (D 8) (R 8) [96,12,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14106 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 266 145 112 112 240 368), lower := (rows 97 14 133 266 145 32 64 128 256), losses := [] }

theorem u14106 : Upper (D 8) (R 8) [96,12,129,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14107 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 266 176 113 113 241 369), lower := (rows 97 14 133 266 176 32 64 128 256), losses := [] }

theorem u14107 : Upper (D 8) (R 8) [96,12,129,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14108 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 266 208 49 113 177 305), lower := (rows 97 14 133 266 208 32 64 128 256), losses := [] }

theorem u14108 : Upper (D 8) (R 8) [96,12,129,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14109 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 280 49 226 226 226 482), lower := (rows 97 14 133 280 49 32 64 128 256), losses := [] }

theorem u14109 : Upper (D 8) (R 8) [96,12,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14110 : Route 9 := (fun mask => (mask,id))

def c14110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u14110 : Upper (D 8) (R 8) [96,12,129,272,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,34] 13 (by decide) (choices 1) [1,64,128] r14110 c14110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4770
  · exact u4771
  · exact u4772

def b14111 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 280 81 162 226 162 418), lower := (rows 97 14 133 280 81 32 64 128 256), losses := [] }

theorem u14111 : Upper (D 8) (R 8) [96,12,129,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14111 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14112 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 133 280 82 161 225 161 417), lower := (rows 97 14 133 280 82 32 64 128 256), losses := [] }

theorem u14112 : Upper (D 8) (R 8) [96,12,129,272,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14113 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 280 112 163 227 163 419), lower := (rows 97 14 133 280 112 32 64 128 256), losses := [] }

theorem u14113 : Upper (D 8) (R 8) [96,12,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14114 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 280 145 98 98 226 354), lower := (rows 97 14 133 280 145 32 64 128 256), losses := [] }

theorem u14114 : Upper (D 8) (R 8) [96,12,129,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14115 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 146 97 97 225 353), lower := (rows 97 14 133 280 146 32 64 128 256), losses := [] }

theorem u14115 : Upper (D 8) (R 8) [96,12,129,272,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14116 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 176 99 99 227 355), lower := (rows 97 14 133 280 176 32 64 128 256), losses := [] }

theorem u14116 : Upper (D 8) (R 8) [96,12,129,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14116 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14117 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 280 208 35 99 163 291), lower := (rows 97 14 133 280 208 32 64 128 256), losses := [] }

theorem u14117 : Upper (D 8) (R 8) [96,12,129,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14118 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 296 49 242 210 210 466), lower := (rows 97 14 133 296 49 32 64 128 256), losses := [] }

theorem u14118 : Upper (D 8) (R 8) [96,12,129,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14119 : Route 9 := (fun mask => (mask,id))

def c14119 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u14119 : Upper (D 8) (R 8) [96,12,129,288,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,34] 13 (by decide) (choices 1) [1,16,64,128] r14119 c14119
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4773
  · exact u4774
  · exact u4775
  · exact u4776

def b14120 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 133 296 81 178 242 178 434), lower := (rows 97 14 133 296 81 32 64 128 256), losses := [] }

theorem u14120 : Upper (D 8) (R 8) [96,12,129,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14121 : Route 9 := (fun mask => (mask,id))

def c14121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14121 : Upper (D 8) (R 8) [96,12,129,288,66] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66] 13 (by decide) (choices 1) [1,16,128] r14121 c14121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4777
  · exact u4778
  · exact u4779

def b14122 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 133 296 112 179 211 147 403), lower := (rows 97 14 133 296 112 32 64 128 256), losses := [] }

theorem u14122 : Upper (D 8) (R 8) [96,12,129,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14123 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 296 145 114 114 242 370), lower := (rows 97 14 133 296 145 32 64 128 256), losses := [] }

theorem u14123 : Upper (D 8) (R 8) [96,12,129,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14124 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 146 113 113 241 369), lower := (rows 97 14 133 296 146 32 64 128 256), losses := [] }

theorem u14124 : Upper (D 8) (R 8) [96,12,129,288,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14125 : Route 9 := (fun mask => (mask,id))

def c14125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14125 : Upper (D 8) (R 8) [96,12,129,288,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,160] 13 (by decide) (choices 1) [1,2,16,64] r14125 c14125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4780
  · exact u4781
  · exact u4782
  · exact u4783

def r14126 : Route 9 := (fun mask => (mask,id))

def c14126 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14126 : Upper (D 8) (R 8) [96,12,129,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,192] 13 (by decide) (choices 1) [1,2,16] r14126 c14126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4784
  · exact u4785
  · exact u4786

def b14127 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 133 328 49 178 242 178 434), lower := (rows 97 14 133 328 49 32 64 128 256), losses := [] }

theorem u14127 : Upper (D 8) (R 8) [96,12,129,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14128 : Route 9 := (fun mask => (mask,id))

def c14128 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u14128 : Upper (D 8) (R 8) [96,12,129,320,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,320,34] 13 (by decide) (choices 1) [1,16,128] r14128 c14128
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4787
  · exact u4788
  · exact u4789

def b14129 : PairBound 9 := { available := 50, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 97 14 133 328 145 50 114 178 306), lower := (rows 97 14 133 328 145 32 64 128 256), losses := [] }

theorem u14129 : Upper (D 8) (R 8) [96,12,129,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14130 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 328 146 49 113 177 305), lower := (rows 97 14 133 328 146 32 64 128 256), losses := [] }

theorem u14130 : Upper (D 8) (R 8) [96,12,129,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r14131 : Route 9 := (fun mask => (mask,id))

def c14131 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14131 : Upper (D 8) (R 8) [96,12,129,320,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,320,160] 13 (by decide) (choices 1) [1,2,16] r14131 c14131
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4790
  · exact u4791
  · exact u4792

def b14132 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 392 50 113 113 241 369), lower := (rows 97 14 133 392 50 32 64 128 256), losses := [] }

theorem u14132 : Upper (D 8) (R 8) [96,12,129,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14133 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 392 82 49 113 177 305), lower := (rows 97 14 133 392 82 32 64 128 256), losses := [] }

theorem u14133 : Upper (D 8) (R 8) [96,12,129,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14134 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 273 97 97 225 353), lower := (rows 97 14 134 152 273 32 64 128 256), losses := [] }

theorem u14134 : Upper (D 8) (R 8) [96,12,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14135 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 304 97 97 225 353), lower := (rows 97 14 134 152 304 32 64 128 256), losses := [] }

theorem u14135 : Upper (D 8) (R 8) [96,12,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14136 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 152 336 33 97 161 289), lower := (rows 97 14 134 152 336 32 64 128 256), losses := [] }

theorem u14136 : Upper (D 8) (R 8) [96,12,130,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14137 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 273 113 113 241 369), lower := (rows 97 14 134 168 273 32 64 128 256), losses := [] }

theorem u14137 : Upper (D 8) (R 8) [96,12,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14138 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 304 113 81 209 337), lower := (rows 97 14 134 168 304 32 64 128 256), losses := [] }

theorem u14138 : Upper (D 8) (R 8) [96,12,130,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14139 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 168 336 49 113 177 305), lower := (rows 97 14 134 168 336 32 64 128 256), losses := [] }

theorem u14139 : Upper (D 8) (R 8) [96,12,130,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14140 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 200 273 49 113 177 305), lower := (rows 97 14 134 200 273 32 64 128 256), losses := [] }

theorem u14140 : Upper (D 8) (R 8) [96,12,130,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14141 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 134 200 304 49 113 177 305), lower := (rows 97 14 134 200 304 32 64 128 256), losses := [] }

theorem u14141 : Upper (D 8) (R 8) [96,12,130,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14142 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 134 265 49 240 240 240 496), lower := (rows 97 14 134 265 49 32 64 128 256), losses := [] }

theorem u14142 : Upper (D 8) (R 8) [96,12,130,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14143 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 134 265 81 176 240 176 432), lower := (rows 97 14 134 265 81 32 64 128 256), losses := [] }

theorem u14143 : Upper (D 8) (R 8) [96,12,130,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14144 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 134 265 112 177 241 177 433), lower := (rows 97 14 134 265 112 32 64 128 256), losses := [] }

theorem u14144 : Upper (D 8) (R 8) [96,12,130,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14145 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 265 145 112 112 240 368), lower := (rows 97 14 134 265 145 32 64 128 256), losses := [] }

theorem u14145 : Upper (D 8) (R 8) [96,12,130,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14146 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 265 176 113 113 241 369), lower := (rows 97 14 134 265 176 32 64 128 256), losses := [] }

theorem u14146 : Upper (D 8) (R 8) [96,12,130,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14147 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 265 208 49 113 177 305), lower := (rows 97 14 134 265 208 32 64 128 256), losses := [] }

theorem u14147 : Upper (D 8) (R 8) [96,12,130,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14148 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 134 280 49 225 225 225 481), lower := (rows 97 14 134 280 49 32 64 128 256), losses := [] }

theorem u14148 : Upper (D 8) (R 8) [96,12,130,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14149 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 134 280 81 161 225 161 417), lower := (rows 97 14 134 280 81 32 64 128 256), losses := [] }

theorem u14149 : Upper (D 8) (R 8) [96,12,130,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14150 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 134 280 112 161 225 161 417), lower := (rows 97 14 134 280 112 32 64 128 256), losses := [] }

theorem u14150 : Upper (D 8) (R 8) [96,12,130,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14151 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 280 145 97 97 225 353), lower := (rows 97 14 134 280 145 32 64 128 256), losses := [] }

theorem u14151 : Upper (D 8) (R 8) [96,12,130,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14152 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 280 176 97 97 225 353), lower := (rows 97 14 134 280 176 32 64 128 256), losses := [] }

theorem u14152 : Upper (D 8) (R 8) [96,12,130,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14153 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 280 208 33 97 161 289), lower := (rows 97 14 134 280 208 32 64 128 256), losses := [] }

theorem u14153 : Upper (D 8) (R 8) [96,12,130,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14154 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 134 296 49 241 209 209 465), lower := (rows 97 14 134 296 49 32 64 128 256), losses := [] }

theorem u14154 : Upper (D 8) (R 8) [96,12,130,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14155 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 134 296 81 177 241 177 433), lower := (rows 97 14 134 296 81 32 64 128 256), losses := [] }

theorem u14155 : Upper (D 8) (R 8) [96,12,130,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14156 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 134 296 112 177 209 145 401), lower := (rows 97 14 134 296 112 32 64 128 256), losses := [] }

theorem u14156 : Upper (D 8) (R 8) [96,12,130,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14157 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 296 145 113 113 241 369), lower := (rows 97 14 134 296 145 32 64 128 256), losses := [] }

theorem u14157 : Upper (D 8) (R 8) [96,12,130,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14158 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 296 176 113 81 209 337), lower := (rows 97 14 134 296 176 32 64 128 256), losses := [] }

theorem u14158 : Upper (D 8) (R 8) [96,12,130,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14159 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 134 296 208 49 113 177 305), lower := (rows 97 14 134 296 208 32 64 128 256), losses := [] }

theorem u14159 : Upper (D 8) (R 8) [96,12,130,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u14159
end Delivery.IrregularNine14.P08
