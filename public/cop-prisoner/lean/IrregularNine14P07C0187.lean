import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0014

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b11220 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 262 164 88 145 34 72 131 259), lower := (rows 97 262 164 88 145 34 72 128 256), losses := [] }

theorem u11220 : Upper (D 7) (R 7) [96,260,160,80,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11220 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11221 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 414, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(4,0)], upper := (rows 97 262 164 88 146 33 65 138 266), lower := (rows 97 262 164 88 146 33 65 128 256), losses := [] }

theorem u11221 : Upper (D 7) (R 7) [96,260,160,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11222 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 165, targets := 2 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,1),(2,1),(3,0),(3,5)], upper := (rows 97 262 164 88 146 33 66 137 265), lower := (rows 97 262 164 88 146 33 66 128 256), losses := [] }

theorem u11222 : Upper (D 7) (R 7) [96,260,160,80,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11222 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11223 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 262 164 88 146 33 72 131 259), lower := (rows 97 262 164 88 146 33 72 128 256), losses := [] }

theorem u11223 : Upper (D 7) (R 7) [96,260,160,80,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11223 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11224 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 290 7 25 146 36 72 192 448), lower := (rows 97 290 7 25 146 36 72 128 256), losses := [] }

theorem u11224 : Upper (D 7) (R 7) [96,288,3,17,130,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11224 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11225 : Route 9 := (fun mask => (mask,id))

def c11225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11225 : Upper (D 7) (R 7) [96,288,3,17,130,4,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,17,130,4,128] 13 (by decide) (choices 1) [8,64] r11225 c11225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u847
  · exact u848

def b11226 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 290 7 25 146 160 68 200 328), lower := (rows 97 290 7 25 146 160 68 128 256), losses := [] }

theorem u11226 : Upper (D 7) (R 7) [96,288,3,17,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11226 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11227 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 25 146 160 72 196 324), lower := (rows 97 290 7 25 146 160 72 128 256), losses := [] }

theorem u11227 : Upper (D 7) (R 7) [96,288,3,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11227 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11228 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 25 148 160 66 200 328), lower := (rows 97 290 7 25 148 160 66 128 256), losses := [] }

theorem u11228 : Upper (D 7) (R 7) [96,288,3,17,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11229 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 25 148 160 72 194 322), lower := (rows 97 290 7 25 148 160 72 128 256), losses := [] }

theorem u11229 : Upper (D 7) (R 7) [96,288,3,17,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11229 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11230 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 7 26 84 160 65 136 392), lower := (rows 97 290 7 26 84 160 65 128 256), losses := [] }

theorem u11230 : Upper (D 7) (R 7) [96,288,3,18,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11231 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 26 84 160 72 129 385), lower := (rows 97 290 7 26 84 160 72 128 256), losses := [] }

theorem u11231 : Upper (D 7) (R 7) [96,288,3,18,68,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11231 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11232 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 7 26 84 160 192 137 265), lower := (rows 97 290 7 26 84 160 192 128 256), losses := [] }

theorem u11232 : Upper (D 7) (R 7) [96,288,3,18,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11233 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 144, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 97 290 7 26 145 36 72 192 448), lower := (rows 97 290 7 26 145 36 72 128 256), losses := [] }

theorem u11233 : Upper (D 7) (R 7) [96,288,3,18,129,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11233 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r11234 : Route 9 := (fun mask => (mask,id))

def c11234 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u11234 : Upper (D 7) (R 7) [96,288,3,18,129,4,128] 13 := by
  apply FastRouting.sound _ _ [96,288,3,18,129,4,128] 13 (by decide) (choices 1) [8,64] r11234 c11234
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u849
  · exact u850

def b11235 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 290 7 26 145 160 68 200 328), lower := (rows 97 290 7 26 145 160 68 128 256), losses := [] }

theorem u11235 : Upper (D 7) (R 7) [96,288,3,18,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11235 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11236 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 26 145 160 72 196 324), lower := (rows 97 290 7 26 145 160 72 128 256), losses := [] }

theorem u11236 : Upper (D 7) (R 7) [96,288,3,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11236 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11237 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 26 148 160 65 200 328), lower := (rows 97 290 7 26 148 160 65 128 256), losses := [] }

theorem u11237 : Upper (D 7) (R 7) [96,288,3,18,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11237 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11238 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 26 148 160 72 193 321), lower := (rows 97 290 7 26 148 160 72 128 256), losses := [] }

theorem u11238 : Upper (D 7) (R 7) [96,288,3,18,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11238 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11239 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 290 7 26 208 36 65 136 392), lower := (rows 97 290 7 26 208 36 65 128 256), losses := [] }

theorem u11239 : Upper (D 7) (R 7) [96,288,3,18,192,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11239 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11240 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 144, targets := 34 }], pairs := [(4,1),(4,5)], upper := (rows 97 290 7 26 208 36 72 129 385), lower := (rows 97 290 7 26 208 36 72 128 256), losses := [] }

theorem u11240 : Upper (D 7) (R 7) [96,288,3,18,192,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11240 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11241 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 7 26 208 36 192 137 265), lower := (rows 97 290 7 26 208 36 192 128 256), losses := [] }

theorem u11241 : Upper (D 7) (R 7) [96,288,3,18,192,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11241 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11242 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 26 208 160 65 140 268), lower := (rows 97 290 7 26 208 160 65 128 256), losses := [] }

theorem u11242 : Upper (D 7) (R 7) [96,288,3,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11243 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5)], upper := (rows 97 290 7 26 208 160 68 137 265), lower := (rows 97 290 7 26 208 160 68 128 256), losses := [] }

theorem u11243 : Upper (D 7) (R 7) [96,288,3,18,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11243 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11244 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 262, targets := 64 },{ cop := 0, region := 262, targets := 128 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 97 290 7 26 208 160 72 133 261), lower := (rows 97 290 7 26 208 160 72 128 256), losses := [] }

theorem u11244 : Upper (D 7) (R 7) [96,288,3,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11244 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11245 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 7 28 82 160 65 136 392), lower := (rows 97 290 7 28 82 160 65 128 256), losses := [] }

theorem u11245 : Upper (D 7) (R 7) [96,288,3,20,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11246 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 28 82 160 72 129 385), lower := (rows 97 290 7 28 82 160 72 128 256), losses := [] }

theorem u11246 : Upper (D 7) (R 7) [96,288,3,20,66,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11246 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11247 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 286, targets := 128 }], pairs := [(1,7),(2,7),(3,7),(4,7)], upper := (rows 97 290 7 28 82 160 192 137 265), lower := (rows 97 290 7 28 82 160 192 128 256), losses := [] }

theorem u11247 : Upper (D 7) (R 7) [96,288,3,20,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11248 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 28 145 160 66 200 328), lower := (rows 97 290 7 28 145 160 66 128 256), losses := [] }

theorem u11248 : Upper (D 7) (R 7) [96,288,3,20,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11249 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 28 145 160 72 194 322), lower := (rows 97 290 7 28 145 160 72 128 256), losses := [] }

theorem u11249 : Upper (D 7) (R 7) [96,288,3,20,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11249 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11250 : PairBound 9 := { available := 72, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 28 146 160 65 200 328), lower := (rows 97 290 7 28 146 160 65 128 256), losses := [] }

theorem u11250 : Upper (D 7) (R 7) [96,288,3,20,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11251 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 262, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(1,7),(2,7),(3,5)], upper := (rows 97 290 7 28 146 160 72 193 321), lower := (rows 97 290 7 28 146 160 72 128 256), losses := [] }

theorem u11251 : Upper (D 7) (R 7) [96,288,3,20,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11251 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11252 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 28 208 160 65 138 266), lower := (rows 97 290 7 28 208 160 65 128 256), losses := [] }

theorem u11252 : Upper (D 7) (R 7) [96,288,3,20,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11253 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 28 208 160 66 137 265), lower := (rows 97 290 7 28 208 160 66 128 256), losses := [] }

theorem u11253 : Upper (D 7) (R 7) [96,288,3,20,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11254 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 262, targets := 64 },{ cop := 0, region := 258, targets := 128 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 97 290 7 28 208 160 72 131 259), lower := (rows 97 290 7 28 208 160 72 128 256), losses := [] }

theorem u11254 : Upper (D 7) (R 7) [96,288,3,20,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11254 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11255 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 74 145 160 68 152 280), lower := (rows 97 290 7 74 145 160 68 128 256), losses := [] }

theorem u11255 : Upper (D 7) (R 7) [96,288,3,66,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11255 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11256 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 74 145 160 72 148 276), lower := (rows 97 290 7 74 145 160 72 128 256), losses := [] }

theorem u11256 : Upper (D 7) (R 7) [96,288,3,66,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11256 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11257 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 74 145 160 80 140 268), lower := (rows 97 290 7 74 145 160 80 128 256), losses := [] }

theorem u11257 : Upper (D 7) (R 7) [96,288,3,66,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11257 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11258 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 74 148 48 65 136 392), lower := (rows 97 290 7 74 148 48 65 128 256), losses := [] }

theorem u11258 : Upper (D 7) (R 7) [96,288,3,66,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11258 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11259 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 290 7 74 148 48 72 129 385), lower := (rows 97 290 7 74 148 48 72 128 256), losses := [] }

theorem u11259 : Upper (D 7) (R 7) [96,288,3,66,132,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11259 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11260 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 74 148 48 192 137 265), lower := (rows 97 290 7 74 148 48 192 128 256), losses := [] }

theorem u11260 : Upper (D 7) (R 7) [96,288,3,66,132,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11260 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11261 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 97 290 7 74 148 160 65 152 280), lower := (rows 97 290 7 74 148 160 65 128 256), losses := [] }

theorem u11261 : Upper (D 7) (R 7) [96,288,3,66,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11261 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11262 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 74 148 160 72 145 273), lower := (rows 97 290 7 74 148 160 72 128 256), losses := [] }

theorem u11262 : Upper (D 7) (R 7) [96,288,3,66,132,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11262 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11263 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 74 148 160 80 137 265), lower := (rows 97 290 7 74 148 160 80 128 256), losses := [] }

theorem u11263 : Upper (D 7) (R 7) [96,288,3,66,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11263 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11264 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 97 290 7 74 152 160 65 148 276), lower := (rows 97 290 7 74 152 160 65 128 256), losses := [] }

theorem u11264 : Upper (D 7) (R 7) [96,288,3,66,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11264 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11265 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 290 7 74 152 160 68 145 273), lower := (rows 97 290 7 74 152 160 68 128 256), losses := [] }

theorem u11265 : Upper (D 7) (R 7) [96,288,3,66,136,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11265 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11266 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 74 152 160 80 133 261), lower := (rows 97 290 7 74 152 160 80 128 256), losses := [] }

theorem u11266 : Upper (D 7) (R 7) [96,288,3,66,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11266 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11267 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 97 290 7 76 145 160 66 152 280), lower := (rows 97 290 7 76 145 160 66 128 256), losses := [] }

theorem u11267 : Upper (D 7) (R 7) [96,288,3,68,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11267 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11268 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 76 145 160 72 146 274), lower := (rows 97 290 7 76 145 160 72 128 256), losses := [] }

theorem u11268 : Upper (D 7) (R 7) [96,288,3,68,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11268 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11269 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 76 145 160 80 138 266), lower := (rows 97 290 7 76 145 160 80 128 256), losses := [] }

theorem u11269 : Upper (D 7) (R 7) [96,288,3,68,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11269 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11270 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 290 7 76 146 160 65 152 280), lower := (rows 97 290 7 76 146 160 65 128 256), losses := [] }

theorem u11270 : Upper (D 7) (R 7) [96,288,3,68,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11270 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11271 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 290 7 76 146 160 72 145 273), lower := (rows 97 290 7 76 146 160 72 128 256), losses := [] }

theorem u11271 : Upper (D 7) (R 7) [96,288,3,68,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11271 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11272 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 76 146 160 80 137 265), lower := (rows 97 290 7 76 146 160 80 128 256), losses := [] }

theorem u11272 : Upper (D 7) (R 7) [96,288,3,68,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11272 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11273 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 97 290 7 76 152 160 65 146 274), lower := (rows 97 290 7 76 152 160 65 128 256), losses := [] }

theorem u11273 : Upper (D 7) (R 7) [96,288,3,68,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11273 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11274 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 },{ cop := 2, region := 72, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(3,7)], upper := (rows 97 290 7 76 152 160 66 145 273), lower := (rows 97 290 7 76 152 160 66 128 256), losses := [] }

theorem u11274 : Upper (D 7) (R 7) [96,288,3,68,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11274 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11275 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7),(2,7),(3,7)], upper := (rows 97 290 7 76 152 160 80 131 259), lower := (rows 97 290 7 76 152 160 80 128 256), losses := [] }

theorem u11275 : Upper (D 7) (R 7) [96,288,3,68,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11275 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11276 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 152, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 290 7 88 145 36 66 136 392), lower := (rows 97 290 7 88 145 36 66 128 256), losses := [] }

theorem u11276 : Upper (D 7) (R 7) [96,288,3,80,129,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11276 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11277 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 97 290 7 88 145 36 72 130 386), lower := (rows 97 290 7 88 145 36 72 128 256), losses := [] }

theorem u11277 : Upper (D 7) (R 7) [96,288,3,80,129,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11277 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11278 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 97 290 7 88 145 36 192 138 266), lower := (rows 97 290 7 88 145 36 192 128 256), losses := [] }

theorem u11278 : Upper (D 7) (R 7) [96,288,3,80,129,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11278 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11279 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 216, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 97 290 7 88 145 160 66 140 268), lower := (rows 97 290 7 88 145 160 66 128 256), losses := [] }

theorem u11279 : Upper (D 7) (R 7) [96,288,3,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11279 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u11279
end Delivery.IrregularNine14.P07
