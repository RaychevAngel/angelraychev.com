import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0065

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b12120 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 88 145 41 105 169 297), lower := (rows 67 262 164 88 145 32 64 128 256), losses := [] }

theorem u12120 : Upper (D 8) (R 8) [66,260,160,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12121 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 422, targets := 64 }], pairs := [(1,6)], upper := (rows 67 262 164 88 152 33 97 161 289), lower := (rows 67 262 164 88 152 32 64 128 256), losses := [] }

theorem u12121 : Upper (D 8) (R 8) [66,260,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12122 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 164 88 176 41 105 169 297), lower := (rows 67 262 164 88 176 32 64 128 256), losses := [] }

theorem u12122 : Upper (D 8) (R 8) [66,260,160,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12123 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7)], upper := (rows 67 262 164 104 145 57 121 185 313), lower := (rows 67 262 164 104 145 32 64 128 256), losses := [] }

theorem u12123 : Upper (D 8) (R 8) [66,260,160,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12124 : Route 9 := (fun mask => (mask,id))

def c12124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u12124 : Upper (D 8) (R 8) [66,260,160,96,136] 13 := by
  apply FastRouting.sound _ _ [66,260,160,96,136] 13 (by decide) (choices 1) [1,16] r12124 c12124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3907
  · exact u3908

def b12125 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 67 262 164 104 176 57 89 153 281), lower := (rows 67 262 164 104 176 32 64 128 256), losses := [] }

theorem u12125 : Upper (D 8) (R 8) [66,260,160,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12126 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 13 112 176 240 176 432), lower := (rows 67 290 13 13 112 32 64 128 256), losses := [] }

theorem u12126 : Upper (D 8) (R 8) [66,288,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12127 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 13 176 240 240 240 496), lower := (rows 67 290 13 13 176 32 64 128 256), losses := [] }

theorem u12127 : Upper (D 8) (R 8) [66,288,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12128 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 13 208 176 240 176 432), lower := (rows 67 290 13 13 208 32 64 128 256), losses := [] }

theorem u12128 : Upper (D 8) (R 8) [66,288,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12129 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 25 52 224 224 224 480), lower := (rows 67 290 13 25 52 32 64 128 256), losses := [] }

theorem u12129 : Upper (D 8) (R 8) [66,288,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12130 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 25 84 160 224 160 416), lower := (rows 67 290 13 25 84 32 64 128 256), losses := [] }

theorem u12130 : Upper (D 8) (R 8) [66,288,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12131 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 25 112 164 228 164 420), lower := (rows 67 290 13 25 112 32 64 128 256), losses := [] }

theorem u12131 : Upper (D 8) (R 8) [66,288,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12132 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 25 148 224 224 224 480), lower := (rows 67 290 13 25 148 32 64 128 256), losses := [] }

theorem u12132 : Upper (D 8) (R 8) [66,288,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12133 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 25 176 228 228 228 484), lower := (rows 67 290 13 25 176 32 64 128 256), losses := [] }

theorem u12133 : Upper (D 8) (R 8) [66,288,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12134 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 25 208 164 228 164 420), lower := (rows 67 290 13 25 208 32 64 128 256), losses := [] }

theorem u12134 : Upper (D 8) (R 8) [66,288,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12135 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 28 49 224 224 224 480), lower := (rows 67 290 13 28 49 32 64 128 256), losses := [] }

theorem u12135 : Upper (D 8) (R 8) [66,288,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12136 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 28, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 28 81 160 224 160 416), lower := (rows 67 290 13 28 81 32 64 128 256), losses := [] }

theorem u12136 : Upper (D 8) (R 8) [66,288,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12137 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 28 112 161 225 161 417), lower := (rows 67 290 13 28 112 32 64 128 256), losses := [] }

theorem u12137 : Upper (D 8) (R 8) [66,288,9,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12138 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 28 145 224 224 224 480), lower := (rows 67 290 13 28 145 32 64 128 256), losses := [] }

theorem u12138 : Upper (D 8) (R 8) [66,288,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12139 : Route 9 := (fun mask => (mask,id))

def c12139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12139 : Upper (D 8) (R 8) [66,288,9,20,160] 13 := by
  apply FastRouting.sound _ _ [66,288,9,20,160] 13 (by decide) (choices 1) [1,64,128] r12139 c12139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3909
  · exact u3910
  · exact u3911

def b12140 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 28 208 161 225 161 417), lower := (rows 67 290 13 28 208 32 64 128 256), losses := [] }

theorem u12140 : Upper (D 8) (R 8) [66,288,9,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12141 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 41 52 240 208 208 464), lower := (rows 67 290 13 41 52 32 64 128 256), losses := [] }

theorem u12141 : Upper (D 8) (R 8) [66,288,9,33,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12142 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 41 84 176 240 176 432), lower := (rows 67 290 13 41 84 32 64 128 256), losses := [] }

theorem u12142 : Upper (D 8) (R 8) [66,288,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12143 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 41 112 180 212 148 404), lower := (rows 67 290 13 41 112 32 64 128 256), losses := [] }

theorem u12143 : Upper (D 8) (R 8) [66,288,9,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12144 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 41 148 240 240 240 496), lower := (rows 67 290 13 41 148 32 64 128 256), losses := [] }

theorem u12144 : Upper (D 8) (R 8) [66,288,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12145 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 41 176 244 212 212 468), lower := (rows 67 290 13 41 176 32 64 128 256), losses := [] }

theorem u12145 : Upper (D 8) (R 8) [66,288,9,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12146 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 41 208 180 244 180 436), lower := (rows 67 290 13 41 208 32 64 128 256), losses := [] }

theorem u12146 : Upper (D 8) (R 8) [66,288,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12147 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 44 49 240 208 208 464), lower := (rows 67 290 13 44 49 32 64 128 256), losses := [] }

theorem u12147 : Upper (D 8) (R 8) [66,288,9,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12148 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 44 81 176 240 176 432), lower := (rows 67 290 13 44 81 32 64 128 256), losses := [] }

theorem u12148 : Upper (D 8) (R 8) [66,288,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12149 : Route 9 := (fun mask => (mask,id))

def c12149 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12149 : Upper (D 8) (R 8) [66,288,9,36,96] 13 := by
  apply FastRouting.sound _ _ [66,288,9,36,96] 13 (by decide) (choices 1) [1,16,128] r12149 c12149
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3912
  · exact u3913
  · exact u3914

def b12150 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 44 145 240 240 240 496), lower := (rows 67 290 13 44 145 32 64 128 256), losses := [] }

theorem u12150 : Upper (D 8) (R 8) [66,288,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12151 : Route 9 := (fun mask => (mask,id))

def c12151 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u12151 : Upper (D 8) (R 8) [66,288,9,36,160] 13 := by
  apply FastRouting.sound _ _ [66,288,9,36,160] 13 (by decide) (choices 1) [1,16,64,128] r12151 c12151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3915
  · exact u3916
  · exact u3917
  · exact u3918

def r12152 : Route 9 := (fun mask => (mask,id))

def c12152 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u12152 : Upper (D 8) (R 8) [66,288,9,36,192] 13 := by
  apply FastRouting.sound _ _ [66,288,9,36,192] 13 (by decide) (choices 1) [1,16,128] r12152 c12152
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3919
  · exact u3920
  · exact u3921

def b12153 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 290 13 56 49 228 196 196 452), lower := (rows 67 290 13 56 49 32 64 128 256), losses := [] }

theorem u12153 : Upper (D 8) (R 8) [66,288,9,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12154 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 13 56 52 225 193 193 449), lower := (rows 67 290 13 56 52 32 64 128 256), losses := [] }

theorem u12154 : Upper (D 8) (R 8) [66,288,9,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12155 : PairBound 9 := { available := 164, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 56 81 164 228 164 420), lower := (rows 67 290 13 56 81 32 64 128 256), losses := [] }

theorem u12155 : Upper (D 8) (R 8) [66,288,9,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12156 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 56 84 161 225 161 417), lower := (rows 67 290 13 56 84 32 64 128 256), losses := [] }

theorem u12156 : Upper (D 8) (R 8) [66,288,9,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12157 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 13 56 112 165 197 133 389), lower := (rows 67 290 13 56 112 32 64 128 256), losses := [] }

theorem u12157 : Upper (D 8) (R 8) [66,288,9,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12158 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0)], upper := (rows 67 290 13 56 145 228 228 228 484), lower := (rows 67 290 13 56 145 32 64 128 256), losses := [] }

theorem u12158 : Upper (D 8) (R 8) [66,288,9,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r12159 : Route 9 := (fun mask => (mask,id))

def c12159 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u12159 : Upper (D 8) (R 8) [66,288,9,48,132] 13 := by
  apply FastRouting.sound _ _ [66,288,9,48,132] 13 (by decide) (choices 1) [1,64,128] r12159 c12159
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3922
  · exact u3923
  · exact u3924

def b12160 : PairBound 9 := { available := 197, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 67 290 13 56 176 229 197 197 453), lower := (rows 67 290 13 56 176 32 64 128 256), losses := [] }

theorem u12160 : Upper (D 8) (R 8) [66,288,9,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12161 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 56 208 165 229 165 421), lower := (rows 67 290 13 56 208 32 64 128 256), losses := [] }

theorem u12161 : Upper (D 8) (R 8) [66,288,9,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12162 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 73 52 176 240 176 432), lower := (rows 67 290 13 73 52 32 64 128 256), losses := [] }

theorem u12162 : Upper (D 8) (R 8) [66,288,9,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12163 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 73 148 176 240 176 432), lower := (rows 67 290 13 73 148 32 64 128 256), losses := [] }

theorem u12163 : Upper (D 8) (R 8) [66,288,9,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12164 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 73 176 180 244 180 436), lower := (rows 67 290 13 73 176 32 64 128 256), losses := [] }

theorem u12164 : Upper (D 8) (R 8) [66,288,9,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12165 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 76 49 176 240 176 432), lower := (rows 67 290 13 76 49 32 64 128 256), losses := [] }

theorem u12165 : Upper (D 8) (R 8) [66,288,9,68,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12166 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 76 145 176 240 176 432), lower := (rows 67 290 13 76 145 32 64 128 256), losses := [] }

theorem u12166 : Upper (D 8) (R 8) [66,288,9,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12167 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 76 176 177 241 177 433), lower := (rows 67 290 13 76 176 32 64 128 256), losses := [] }

theorem u12167 : Upper (D 8) (R 8) [66,288,9,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12168 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 88 49 164 228 164 420), lower := (rows 67 290 13 88 49 32 64 128 256), losses := [] }

theorem u12168 : Upper (D 8) (R 8) [66,288,9,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12169 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 88 52 161 225 161 417), lower := (rows 67 290 13 88 52 32 64 128 256), losses := [] }

theorem u12169 : Upper (D 8) (R 8) [66,288,9,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12170 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 88 145 164 228 164 420), lower := (rows 67 290 13 88 145 32 64 128 256), losses := [] }

theorem u12170 : Upper (D 8) (R 8) [66,288,9,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12171 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 88 148 161 225 161 417), lower := (rows 67 290 13 88 148 32 64 128 256), losses := [] }

theorem u12171 : Upper (D 8) (R 8) [66,288,9,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12172 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 88 176 165 229 165 421), lower := (rows 67 290 13 88 176 32 64 128 256), losses := [] }

theorem u12172 : Upper (D 8) (R 8) [66,288,9,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12173 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 104 49 180 212 148 404), lower := (rows 67 290 13 104 49 32 64 128 256), losses := [] }

theorem u12173 : Upper (D 8) (R 8) [66,288,9,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12174 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 104 52 177 209 145 401), lower := (rows 67 290 13 104 52 32 64 128 256), losses := [] }

theorem u12174 : Upper (D 8) (R 8) [66,288,9,96,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12175 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 104 145 180 244 180 436), lower := (rows 67 290 13 104 145 32 64 128 256), losses := [] }

theorem u12175 : Upper (D 8) (R 8) [66,288,9,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12176 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 104 148 177 241 177 433), lower := (rows 67 290 13 104 148 32 64 128 256), losses := [] }

theorem u12176 : Upper (D 8) (R 8) [66,288,9,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12177 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 67 290 13 104 176 181 213 149 405), lower := (rows 67 290 13 104 176 32 64 128 256), losses := [] }

theorem u12177 : Upper (D 8) (R 8) [66,288,9,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12178 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 52 240 240 240 496), lower := (rows 67 290 13 137 52 32 64 128 256), losses := [] }

theorem u12178 : Upper (D 8) (R 8) [66,288,9,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12179 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 67 290 13 137 84 176 240 176 432), lower := (rows 67 290 13 137 84 32 64 128 256), losses := [] }

theorem u12179 : Upper (D 8) (R 8) [66,288,9,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u12179
end Delivery.IrregularNine14.P08
