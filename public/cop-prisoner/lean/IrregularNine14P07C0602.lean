import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0359

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b36120 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 88 145 172 236 172 428), lower := (rows 35 322 7 88 145 32 64 128 256), losses := [] }

theorem u36120 : Upper (D 7) (R 7) [34,320,3,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36120 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36121 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 88 148 169 233 169 425), lower := (rows 35 322 7 88 148 32 64 128 256), losses := [] }

theorem u36121 : Upper (D 7) (R 7) [34,320,3,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36121 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36122 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 4, targets := 160 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,5),(2,6),(2,7)], upper := (rows 35 322 7 88 152 165 229 165 421), lower := (rows 35 322 7 88 152 32 64 128 256), losses := [] }

theorem u36122 : Upper (D 7) (R 7) [34,320,3,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36122 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36123 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 88 176 173 205 141 397), lower := (rows 35 322 7 88 176 32 64 128 256), losses := [] }

theorem u36123 : Upper (D 7) (R 7) [34,320,3,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36124 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 104 145 188 220 156 412), lower := (rows 35 322 7 104 145 32 64 128 256), losses := [] }

theorem u36124 : Upper (D 7) (R 7) [34,320,3,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36124 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36125 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 104 148 185 217 153 409), lower := (rows 35 322 7 104 148 32 64 128 256), losses := [] }

theorem u36125 : Upper (D 7) (R 7) [34,320,3,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36126 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 104 152 181 213 149 405), lower := (rows 35 322 7 104 152 32 64 128 256), losses := [] }

theorem u36126 : Upper (D 7) (R 7) [34,320,3,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36127 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 137 148 120 120 248 376), lower := (rows 35 322 7 137 148 32 64 128 256), losses := [] }

theorem u36127 : Upper (D 7) (R 7) [34,320,3,129,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36128 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 137 176 124 92 220 348), lower := (rows 35 322 7 137 176 32 64 128 256), losses := [] }

theorem u36128 : Upper (D 7) (R 7) [34,320,3,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36128 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36129 : PairBound 9 := { available := 60, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 137 208 60 124 188 316), lower := (rows 35 322 7 137 208 32 64 128 256), losses := [] }

theorem u36129 : Upper (D 7) (R 7) [34,320,3,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36130 : PairBound 9 := { available := 89, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 140 176 121 89 217 345), lower := (rows 35 322 7 140 176 32 64 128 256), losses := [] }

theorem u36130 : Upper (D 7) (R 7) [34,320,3,132,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36130 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36131 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 140 208 57 121 185 313), lower := (rows 35 322 7 140 208 32 64 128 256), losses := [] }

theorem u36131 : Upper (D 7) (R 7) [34,320,3,132,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36131 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36132 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 4, targets := 224 },{ cop := 2, region := 248, targets := 2 }], pairs := [(2,5),(2,6),(2,7),(3,1)], upper := (rows 35 322 7 168 208 61 93 157 285), lower := (rows 35 322 7 168 208 32 64 128 256), losses := [] }

theorem u36132 : Upper (D 7) (R 7) [34,320,3,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36132 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36133 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 13 112 178 210 146 402), lower := (rows 35 322 13 13 112 32 64 128 256), losses := [] }

theorem u36133 : Upper (D 7) (R 7) [34,320,9,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36134 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 13 146 240 240 240 496), lower := (rows 35 322 13 13 146 32 64 128 256), losses := [] }

theorem u36134 : Upper (D 7) (R 7) [34,320,9,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36135 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 13 176 242 210 210 466), lower := (rows 35 322 13 13 176 32 64 128 256), losses := [] }

theorem u36135 : Upper (D 7) (R 7) [34,320,9,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36135 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36136 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 13 208 178 242 178 434), lower := (rows 35 322 13 13 208 32 64 128 256), losses := [] }

theorem u36136 : Upper (D 7) (R 7) [34,320,9,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36136 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36137 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 81 176 240 176 432), lower := (rows 35 322 13 14 81 32 64 128 256), losses := [] }

theorem u36137 : Upper (D 7) (R 7) [34,320,9,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36138 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 112 177 209 145 401), lower := (rows 35 322 13 14 112 32 64 128 256), losses := [] }

theorem u36138 : Upper (D 7) (R 7) [34,320,9,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36138 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36139 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 145 240 240 240 496), lower := (rows 35 322 13 14 145 32 64 128 256), losses := [] }

theorem u36139 : Upper (D 7) (R 7) [34,320,9,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36139 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36140 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 176 241 209 209 465), lower := (rows 35 322 13 14 176 32 64 128 256), losses := [] }

theorem u36140 : Upper (D 7) (R 7) [34,320,9,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36140 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36141 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 12, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 14 208 177 241 177 433), lower := (rows 35 322 13 14 208 32 64 128 256), losses := [] }

theorem u36141 : Upper (D 7) (R 7) [34,320,9,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36141 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36142 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 28, targets := 224 }], pairs := [(2,5),(2,6),(2,7),(3,5)], upper := (rows 35 322 13 25 22 224 224 224 480), lower := (rows 35 322 13 25 22 32 64 128 256), losses := [] }

theorem u36142 : Upper (D 7) (R 7) [34,320,9,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36142 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36143 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 25 52 226 194 194 450), lower := (rows 35 322 13 25 52 32 64 128 256), losses := [] }

theorem u36143 : Upper (D 7) (R 7) [34,320,9,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36143 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36144 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 25 84 162 226 162 418), lower := (rows 35 322 13 25 84 32 64 128 256), losses := [] }

theorem u36144 : Upper (D 7) (R 7) [34,320,9,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36144 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36145 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 35 322 13 25 112 166 198 134 390), lower := (rows 35 322 13 25 112 32 64 128 256), losses := [] }

theorem u36145 : Upper (D 7) (R 7) [34,320,9,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36145 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36146 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 224 },{ cop := 2, region := 482, targets := 1 }], pairs := [(1,0),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 25 146 228 228 228 484), lower := (rows 35 322 13 25 146 32 64 128 256), losses := [] }

theorem u36146 : Upper (D 7) (R 7) [34,320,9,17,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36146 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36147 : PairBound 9 := { available := 226, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 25 148 226 226 226 482), lower := (rows 35 322 13 25 148 32 64 128 256), losses := [] }

theorem u36147 : Upper (D 7) (R 7) [34,320,9,17,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36147 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36148 : PairBound 9 := { available := 198, camps := [{ cop := 3, region := 4, targets := 194 },{ cop := 2, region := 450, targets := 1 }], pairs := [(1,0),(2,1),(2,6),(2,7)], upper := (rows 35 322 13 25 176 230 198 198 454), lower := (rows 35 322 13 25 176 32 64 128 256), losses := [] }

theorem u36148 : Upper (D 7) (R 7) [34,320,9,17,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36148 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36149 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 4, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 25 208 166 230 166 422), lower := (rows 35 322 13 25 208 32 64 128 256), losses := [] }

theorem u36149 : Upper (D 7) (R 7) [34,320,9,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36149 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36150 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 26 49 228 196 196 452), lower := (rows 35 322 13 26 49 32 64 128 256), losses := [] }

theorem u36150 : Upper (D 7) (R 7) [34,320,9,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36150 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36151 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 26 52 225 193 193 449), lower := (rows 35 322 13 26 52 32 64 128 256), losses := [] }

theorem u36151 : Upper (D 7) (R 7) [34,320,9,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36151 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36152 : PairBound 9 := { available := 164, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 240, targets := 2 }], pairs := [(0,6),(1,0),(2,6),(4,1)], upper := (rows 35 322 13 26 81 164 228 164 420), lower := (rows 35 322 13 26 81 32 64 128 256), losses := [] }

theorem u36152 : Upper (D 7) (R 7) [34,320,9,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36152 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36153 : Route 9 := (fun mask => (mask,id))

def c36153 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36153 : Upper (D 7) (R 7) [34,320,9,18,68] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,68] 13 (by decide) (choices 1) [1,128] r36153 c36153
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u21563
  · exact u21564

def b36154 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 2, region := 240, targets := 2 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,1)], upper := (rows 35 322 13 26 112 165 197 133 389), lower := (rows 35 322 13 26 112 32 64 128 256), losses := [] }

theorem u36154 : Upper (D 7) (R 7) [34,320,9,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36154 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36155 : Route 9 := (fun mask => (mask,id))

def c36155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36155 : Upper (D 7) (R 7) [34,320,9,18,129] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,129] 13 (by decide) (choices 1) [4,64,128] r36155 c36155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21565
  · exact u21566
  · exact u21567

def r36156 : Route 9 := (fun mask => (mask,id))

def c36156 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36156 : Upper (D 7) (R 7) [34,320,9,18,132] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,132] 13 (by decide) (choices 1) [1,64,128] r36156 c36156
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21568
  · exact u21569
  · exact u21570

def r36157 : Route 9 := (fun mask => (mask,id))

def c36157 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36157 : Upper (D 7) (R 7) [34,320,9,18,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,160] 13 (by decide) (choices 1) [1,4,64,128] r36157 c36157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21571
  · exact u21572
  · exact u21573
  · exact u21574

def r36158 : Route 9 := (fun mask => (mask,id))

def c36158 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36158 : Upper (D 7) (R 7) [34,320,9,18,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,18,192] 13 (by decide) (choices 1) [1,4,128] r36158 c36158
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21575
  · exact u21576
  · exact u21577

def b36159 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 28, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 28 49 226 194 194 450), lower := (rows 35 322 13 28 49 32 64 128 256), losses := [] }

theorem u36159 : Upper (D 7) (R 7) [34,320,9,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36159 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36160 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 28, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 28 50 225 193 193 449), lower := (rows 35 322 13 28 50 32 64 128 256), losses := [] }

theorem u36160 : Upper (D 7) (R 7) [34,320,9,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36161 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 28 81 162 226 162 418), lower := (rows 35 322 13 28 81 32 64 128 256), losses := [] }

theorem u36161 : Upper (D 7) (R 7) [34,320,9,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36162 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 322 13 28 82 161 225 161 417), lower := (rows 35 322 13 28 82 32 64 128 256), losses := [] }

theorem u36162 : Upper (D 7) (R 7) [34,320,9,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36163 : Route 9 := (fun mask => (mask,id))

def c36163 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36163 : Upper (D 7) (R 7) [34,320,9,20,96] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,96] 13 (by decide) (choices 1) [1,2,128] r36163 c36163
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21578
  · exact u21579
  · exact u21580

def b36164 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 12, targets := 226 }], pairs := [(2,1),(2,5),(2,6),(2,7)], upper := (rows 35 322 13 28 145 226 226 226 482), lower := (rows 35 322 13 28 145 32 64 128 256), losses := [] }

theorem u36164 : Upper (D 7) (R 7) [34,320,9,20,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r36165 : Route 9 := (fun mask => (mask,id))

def c36165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36165 : Upper (D 7) (R 7) [34,320,9,20,130] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,130] 13 (by decide) (choices 1) [1,64,128] r36165 c36165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21581
  · exact u21582
  · exact u21583

def r36166 : Route 9 := (fun mask => (mask,id))

def c36166 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u36166 : Upper (D 7) (R 7) [34,320,9,20,160] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,160] 13 (by decide) (choices 1) [1,2,64,128] r36166 c36166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u21584
  · exact u21585
  · exact u21586
  · exact u21587

def r36167 : Route 9 := (fun mask => (mask,id))

def c36167 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u36167 : Upper (D 7) (R 7) [34,320,9,20,192] 13 := by
  apply FastRouting.sound _ _ [34,320,9,20,192] 13 (by decide) (choices 1) [1,2,128] r36167 c36167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u21588
  · exact u21589
  · exact u21590

def b36168 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 41 22 240 208 208 464), lower := (rows 35 322 13 41 22 32 64 128 256), losses := [] }

theorem u36168 : Upper (D 7) (R 7) [34,320,9,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36168 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36169 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 41 84 178 210 146 402), lower := (rows 35 322 13 41 84 32 64 128 256), losses := [] }

theorem u36169 : Upper (D 7) (R 7) [34,320,9,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36170 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 41 146 244 212 212 468), lower := (rows 35 322 13 41 146 32 64 128 256), losses := [] }

theorem u36170 : Upper (D 7) (R 7) [34,320,9,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36171 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 41 148 242 210 210 466), lower := (rows 35 322 13 41 148 32 64 128 256), losses := [] }

theorem u36171 : Upper (D 7) (R 7) [34,320,9,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36172 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 41 208 182 214 150 406), lower := (rows 35 322 13 41 208 32 64 128 256), losses := [] }

theorem u36172 : Upper (D 7) (R 7) [34,320,9,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36173 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 42 81 180 212 148 404), lower := (rows 35 322 13 42 81 32 64 128 256), losses := [] }

theorem u36173 : Upper (D 7) (R 7) [34,320,9,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36174 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 42 84 177 209 145 401), lower := (rows 35 322 13 42 84 32 64 128 256), losses := [] }

theorem u36174 : Upper (D 7) (R 7) [34,320,9,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36175 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 42 145 244 212 212 468), lower := (rows 35 322 13 42 145 32 64 128 256), losses := [] }

theorem u36175 : Upper (D 7) (R 7) [34,320,9,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36175 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36176 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 42 148 241 209 209 465), lower := (rows 35 322 13 42 148 32 64 128 256), losses := [] }

theorem u36176 : Upper (D 7) (R 7) [34,320,9,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36177 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 12, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7)], upper := (rows 35 322 13 42 208 181 213 149 405), lower := (rows 35 322 13 42 208 32 64 128 256), losses := [] }

theorem u36177 : Upper (D 7) (R 7) [34,320,9,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36178 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 44 81 178 210 146 402), lower := (rows 35 322 13 44 81 32 64 128 256), losses := [] }

theorem u36178 : Upper (D 7) (R 7) [34,320,9,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36178 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36179 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 12, targets := 194 }], pairs := [(2,1),(2,6),(2,7),(3,1)], upper := (rows 35 322 13 44 145 242 210 210 466), lower := (rows 35 322 13 44 145 32 64 128 256), losses := [] }

theorem u36179 : Upper (D 7) (R 7) [34,320,9,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36179 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u36179
end Delivery.IrregularNine14.P07
