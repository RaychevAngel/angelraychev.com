import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0111

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b18120 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 166, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 134 88 152 33 97 161 289), lower := (rows 321 7 134 88 152 32 64 128 256), losses := [] }

theorem u18120 : Upper (D 8) (R 8) [320,5,130,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18121 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 88 176 41 105 169 297), lower := (rows 321 7 134 88 176 32 64 128 256), losses := [] }

theorem u18121 : Upper (D 8) (R 8) [320,5,130,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18122 : PairBound 9 := { available := 56, camps := [{ cop := 4, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 134 104 145 56 120 184 312), lower := (rows 321 7 134 104 145 32 64 128 256), losses := [] }

theorem u18122 : Upper (D 8) (R 8) [320,5,130,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18122 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18123 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 104 152 49 113 177 305), lower := (rows 321 7 134 104 152 32 64 128 256), losses := [] }

theorem u18123 : Upper (D 8) (R 8) [320,5,130,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18124 : PairBound 9 := { available := 57, camps := [{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 134 104 176 57 121 185 313), lower := (rows 321 7 134 104 176 32 64 128 256), losses := [] }

theorem u18124 : Upper (D 8) (R 8) [320,5,130,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18125 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 25 176 98 98 226 354), lower := (rows 321 7 140 25 176 32 64 128 256), losses := [] }

theorem u18125 : Upper (D 8) (R 8) [320,5,136,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18126 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 25 208 34 98 162 290), lower := (rows 321 7 140 25 208 32 64 128 256), losses := [] }

theorem u18126 : Upper (D 8) (R 8) [320,5,136,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18127 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 140 26 49 224 224 224 480), lower := (rows 321 7 140 26 49 32 64 128 256), losses := [] }

theorem u18127 : Upper (D 8) (R 8) [320,5,136,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18128 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 26 81 160 224 160 416), lower := (rows 321 7 140 26 81 32 64 128 256), losses := [] }

theorem u18128 : Upper (D 8) (R 8) [320,5,136,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18129 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 321 7 140 26 112 161 225 161 417), lower := (rows 321 7 140 26 112 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 35 0 131 259), good := (rows 417 423 140 446 48 32 0 128 256) }] }

theorem u18129 : Upper (D 8) (R 8) [320,5,136,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18129 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18130 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 140 26 145 96 96 224 352), lower := (rows 321 7 140 26 145 32 64 128 256), losses := [] }

theorem u18130 : Upper (D 8) (R 8) [320,5,136,18,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18131 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 26 176 97 97 225 353), lower := (rows 321 7 140 26 176 32 64 128 256), losses := [] }

theorem u18131 : Upper (D 8) (R 8) [320,5,136,18,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18132 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 26 208 33 97 161 289), lower := (rows 321 7 140 26 208 32 64 128 256), losses := [] }

theorem u18132 : Upper (D 8) (R 8) [320,5,136,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18133 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 50 240 240 240 496), lower := (rows 321 7 140 41 50 32 64 128 256), losses := [] }

theorem u18133 : Upper (D 8) (R 8) [320,5,136,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18133 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18134 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 82 176 240 176 432), lower := (rows 321 7 140 41 82 32 64 128 256), losses := [] }

theorem u18134 : Upper (D 8) (R 8) [320,5,136,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18135 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 112 178 242 178 434), lower := (rows 321 7 140 41 112 32 64 128 256), losses := [] }

theorem u18135 : Upper (D 8) (R 8) [320,5,136,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18136 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 41 146 112 112 240 368), lower := (rows 321 7 140 41 146 32 64 128 256), losses := [] }

theorem u18136 : Upper (D 8) (R 8) [320,5,136,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18136 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18137 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 176 114 114 242 370), lower := (rows 321 7 140 41 176 32 64 128 256), losses := [] }

theorem u18137 : Upper (D 8) (R 8) [320,5,136,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18138 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 321 7 140 41 208 50 114 178 306), lower := (rows 321 7 140 41 208 32 64 128 256), losses := [] }

theorem u18138 : Upper (D 8) (R 8) [320,5,136,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18139 : Route 9 := (fun mask => (mask,id))

def c18139 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u18139 : Upper (D 8) (R 8) [320,5,136,34,33] 13 := by
  apply FastRouting.sound _ _ [320,5,136,34,33] 13 (by decide) (choices 1) [16,64,128] r18139 c18139
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6665
  · exact u6666
  · exact u6667

def b18140 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 42 81 176 240 176 432), lower := (rows 321 7 140 42 81 32 64 128 256), losses := [] }

theorem u18140 : Upper (D 8) (R 8) [320,5,136,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r18141 : Route 9 := (fun mask => (mask,id))

def c18141 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u18141 : Upper (D 8) (R 8) [320,5,136,34,96] 13 := by
  apply FastRouting.sound _ _ [320,5,136,34,96] 13 (by decide) (choices 1) [1,16,128] r18141 c18141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6668
  · exact u6669
  · exact u6670

def b18142 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 42 145 112 112 240 368), lower := (rows 321 7 140 42 145 32 64 128 256), losses := [] }

theorem u18142 : Upper (D 8) (R 8) [320,5,136,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18143 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 321, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 42 176 113 113 241 369), lower := (rows 321 7 140 42 176 32 64 128 256), losses := [] }

theorem u18143 : Upper (D 8) (R 8) [320,5,136,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18144 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 42 208 49 113 177 305), lower := (rows 321 7 140 42 208 32 64 128 256), losses := [] }

theorem u18144 : Upper (D 8) (R 8) [320,5,136,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18145 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 140 56 49 226 226 226 482), lower := (rows 321 7 140 56 49 32 64 128 256), losses := [] }

theorem u18145 : Upper (D 8) (R 8) [320,5,136,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18146 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 140 56 50 225 225 225 481), lower := (rows 321 7 140 56 50 32 64 128 256), losses := [] }

theorem u18146 : Upper (D 8) (R 8) [320,5,136,48,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18147 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 174, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 56 81 162 226 162 418), lower := (rows 321 7 140 56 81 32 64 128 256), losses := [] }

theorem u18147 : Upper (D 8) (R 8) [320,5,136,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18148 : PairBound 9 := { available := 161, camps := [], pairs := [(2,6)], upper := (rows 321 7 140 56 82 161 225 161 417), lower := (rows 321 7 140 56 82 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 20 24 16 35 0 131 259), good := (rows 417 423 140 60 446 32 0 128 256) }] }

theorem u18148 : Upper (D 8) (R 8) [320,5,136,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18149 : PairBound 9 := { available := 163, camps := [{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 321 7 140 56 112 163 227 163 419), lower := (rows 321 7 140 56 112 32 64 128 256), losses := [] }

theorem u18149 : Upper (D 8) (R 8) [320,5,136,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18150 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 56 145 98 98 226 354), lower := (rows 321 7 140 56 145 32 64 128 256), losses := [] }

theorem u18150 : Upper (D 8) (R 8) [320,5,136,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18151 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 56 146 97 97 225 353), lower := (rows 321 7 140 56 146 32 64 128 256), losses := [] }

theorem u18151 : Upper (D 8) (R 8) [320,5,136,48,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18152 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 321 7 140 56 176 99 99 227 355), lower := (rows 321 7 140 56 176 32 64 128 256), losses := [] }

theorem u18152 : Upper (D 8) (R 8) [320,5,136,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18153 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 56 208 35 99 163 291), lower := (rows 321 7 140 56 208 32 64 128 256), losses := [] }

theorem u18153 : Upper (D 8) (R 8) [320,5,136,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18154 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 73 50 176 240 176 432), lower := (rows 321 7 140 73 50 32 64 128 256), losses := [] }

theorem u18154 : Upper (D 8) (R 8) [320,5,136,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18155 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 182, targets := 64 }], pairs := [(1,6)], upper := (rows 321 7 140 73 176 50 114 178 306), lower := (rows 321 7 140 73 176 32 64 128 256), losses := [] }

theorem u18155 : Upper (D 8) (R 8) [320,5,136,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18156 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 74 49 176 240 176 432), lower := (rows 321 7 140 74 49 32 64 128 256), losses := [] }

theorem u18156 : Upper (D 8) (R 8) [320,5,136,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18157 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 74 145 48 112 176 304), lower := (rows 321 7 140 74 145 32 64 128 256), losses := [] }

theorem u18157 : Upper (D 8) (R 8) [320,5,136,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18158 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 74 176 49 113 177 305), lower := (rows 321 7 140 74 176 32 64 128 256), losses := [] }

theorem u18158 : Upper (D 8) (R 8) [320,5,136,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18158 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18159 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 88 49 162 226 162 418), lower := (rows 321 7 140 88 49 32 64 128 256), losses := [] }

theorem u18159 : Upper (D 8) (R 8) [320,5,136,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18159 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18160 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 88 50 161 225 161 417), lower := (rows 321 7 140 88 50 32 64 128 256), losses := [] }

theorem u18160 : Upper (D 8) (R 8) [320,5,136,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18161 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 88 145 34 98 162 290), lower := (rows 321 7 140 88 145 32 64 128 256), losses := [] }

theorem u18161 : Upper (D 8) (R 8) [320,5,136,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18162 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 88 146 33 97 161 289), lower := (rows 321 7 140 88 146 32 64 128 256), losses := [] }

theorem u18162 : Upper (D 8) (R 8) [320,5,136,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18162 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18163 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 88 176 35 99 163 291), lower := (rows 321 7 140 88 176 32 64 128 256), losses := [] }

theorem u18163 : Upper (D 8) (R 8) [320,5,136,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18163 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18164 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 104 49 178 242 178 434), lower := (rows 321 7 140 104 49 32 64 128 256), losses := [] }

theorem u18164 : Upper (D 8) (R 8) [320,5,136,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18165 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 104 50 177 241 177 433), lower := (rows 321 7 140 104 50 32 64 128 256), losses := [] }

theorem u18165 : Upper (D 8) (R 8) [320,5,136,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18166 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 104 145 50 114 178 306), lower := (rows 321 7 140 104 145 32 64 128 256), losses := [] }

theorem u18166 : Upper (D 8) (R 8) [320,5,136,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18166 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18167 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 104 146 49 113 177 305), lower := (rows 321 7 140 104 146 32 64 128 256), losses := [] }

theorem u18167 : Upper (D 8) (R 8) [320,5,136,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18168 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 321 7 140 104 176 51 115 179 307), lower := (rows 321 7 140 104 176 32 64 128 256), losses := [] }

theorem u18168 : Upper (D 8) (R 8) [320,5,136,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18169 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 140 137 50 112 112 240 368), lower := (rows 321 7 140 137 50 32 64 128 256), losses := [] }

theorem u18169 : Upper (D 8) (R 8) [320,5,136,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18170 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 140 137 82 48 112 176 304), lower := (rows 321 7 140 137 82 32 64 128 256), losses := [] }

theorem u18170 : Upper (D 8) (R 8) [320,5,136,129,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18170 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18171 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 321 7 140 137 112 50 114 178 306), lower := (rows 321 7 140 137 112 32 64 128 256), losses := [] }

theorem u18171 : Upper (D 8) (R 8) [320,5,136,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18171 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18172 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 138 49 112 112 240 368), lower := (rows 321 7 140 138 49 32 64 128 256), losses := [] }

theorem u18172 : Upper (D 8) (R 8) [320,5,136,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18172 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18173 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 138 112 49 113 177 305), lower := (rows 321 7 140 138 112 32 64 128 256), losses := [] }

theorem u18173 : Upper (D 8) (R 8) [320,5,136,130,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18173 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18174 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 152 49 98 98 226 354), lower := (rows 321 7 140 152 49 32 64 128 256), losses := [] }

theorem u18174 : Upper (D 8) (R 8) [320,5,136,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18174 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18175 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 152 50 97 97 225 353), lower := (rows 321 7 140 152 50 32 64 128 256), losses := [] }

theorem u18175 : Upper (D 8) (R 8) [320,5,136,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18175 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18176 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 152 82 33 97 161 289), lower := (rows 321 7 140 152 82 32 64 128 256), losses := [] }

theorem u18176 : Upper (D 8) (R 8) [320,5,136,144,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18176 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18177 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 152 112 35 99 163 291), lower := (rows 321 7 140 152 112 32 64 128 256), losses := [] }

theorem u18177 : Upper (D 8) (R 8) [320,5,136,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18177 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18178 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 168 49 114 114 242 370), lower := (rows 321 7 140 168 49 32 64 128 256), losses := [] }

theorem u18178 : Upper (D 8) (R 8) [320,5,136,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18178 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18179 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 321 7 140 168 50 113 113 241 369), lower := (rows 321 7 140 168 50 32 64 128 256), losses := [] }

theorem u18179 : Upper (D 8) (R 8) [320,5,136,160,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u18179
end Delivery.IrregularNine14.P08
