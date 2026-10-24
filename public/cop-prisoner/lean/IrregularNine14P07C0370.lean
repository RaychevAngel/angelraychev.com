import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0111
import IrregularNine14P07C0112

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22200 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 88 400 34 195 131 387), lower := (rows 37 42 69 88 400 34 64 128 256), losses := [] }

theorem u22200 : Upper (D 7) (R 7) [36,40,65,80,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22201 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,1),(0,7),(1,0),(2,7)], upper := (rows 37 42 69 88 400 160 67 131 259), lower := (rows 37 42 69 88 400 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 36 42 68 122 432 160 64 160 256) },{ target := 1, region := (rows 11 0 12 8 16 176 64 128 256), good := (rows 37 45 69 125 432 160 64 160 256) }] }

theorem u22201 : Upper (D 7) (R 7) [36,40,65,80,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22202 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 137 82 34 464 400 400), lower := (rows 37 42 69 137 82 34 64 128 256), losses := [] }

theorem u22202 : Upper (D 7) (R 7) [36,40,65,129,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22202 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22203 : PairBound 9 := { available := 386, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 137 82 48 450 386 386), lower := (rows 37 42 69 137 82 48 64 128 256), losses := [] }

theorem u22203 : Upper (D 7) (R 7) [36,40,65,129,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22203 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22204 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 137 82 160 338 402 274), lower := (rows 37 42 69 137 82 160 64 128 256), losses := [] }

theorem u22204 : Upper (D 7) (R 7) [36,40,65,129,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22205 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 42 69 137 82 288 210 146 402), lower := (rows 37 42 69 137 82 288 64 128 256), losses := [] }

theorem u22205 : Upper (D 7) (R 7) [36,40,65,129,66,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22205 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22206 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 137 208 34 338 402 274), lower := (rows 37 42 69 137 208 34 64 128 256), losses := [] }

theorem u22206 : Upper (D 7) (R 7) [36,40,65,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22207 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 45, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 42 69 137 208 48 322 386 258), lower := (rows 37 42 69 137 208 48 64 128 256), losses := [] }

theorem u22207 : Upper (D 7) (R 7) [36,40,65,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22207 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22208 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 208, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 42 69 137 208 288 82 146 274), lower := (rows 37 42 69 137 208 288 64 128 256), losses := [] }

theorem u22208 : Upper (D 7) (R 7) [36,40,65,129,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22208 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22209 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 137 274 34 208 208 464), lower := (rows 37 42 69 137 274 34 64 128 256), losses := [] }

theorem u22209 : Upper (D 7) (R 7) [36,40,65,129,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22210 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 1, region := 464, targets := 32 }], pairs := [(1,0),(4,0),(4,5)], upper := (rows 37 42 69 137 274 48 194 194 450), lower := (rows 37 42 69 137 274 48 64 128 256), losses := [] }

theorem u22210 : Upper (D 7) (R 7) [36,40,65,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22210 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22211 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 137 274 96 210 146 402), lower := (rows 37 42 69 137 274 96 64 128 256), losses := [] }

theorem u22211 : Upper (D 7) (R 7) [36,40,65,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22212 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 137 274 160 82 210 338), lower := (rows 37 42 69 137 274 160 64 128 256), losses := [] }

theorem u22212 : Upper (D 7) (R 7) [36,40,65,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22213 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 137 336 34 210 146 402), lower := (rows 37 42 69 137 336 34 64 128 256), losses := [] }

theorem u22213 : Upper (D 7) (R 7) [36,40,65,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22214 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 137 336 48 194 130 386), lower := (rows 37 42 69 137 336 48 64 128 256), losses := [] }

theorem u22214 : Upper (D 7) (R 7) [36,40,65,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22214 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22215 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 137 336 160 82 146 274), lower := (rows 37 42 69 137 336 160 64 128 256), losses := [] }

theorem u22215 : Upper (D 7) (R 7) [36,40,65,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22216 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 34, targets := 192 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 37 42 69 137 400 34 82 210 338), lower := (rows 37 42 69 137 400 34 64 128 256), losses := [] }

theorem u22216 : Upper (D 7) (R 7) [36,40,65,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22217 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 42 69 137 400 48 66 194 322), lower := (rows 37 42 69 137 400 48 64 128 256), losses := [] }

theorem u22217 : Upper (D 7) (R 7) [36,40,65,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22217 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22218 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 137 400 96 82 146 274), lower := (rows 37 42 69 137 400 96 64 128 256), losses := [] }

theorem u22218 : Upper (D 7) (R 7) [36,40,65,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22219 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 138 82 33 464 400 400), lower := (rows 37 42 69 138 82 33 64 128 256), losses := [] }

theorem u22219 : Upper (D 7) (R 7) [36,40,65,130,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22220 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 37 42 69 138 82 48 449 385 385), lower := (rows 37 42 69 138 82 48 64 128 256), losses := [] }

theorem u22220 : Upper (D 7) (R 7) [36,40,65,130,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22220 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22221 : PairBound 9 := { available := 273, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 138 82 160 337 401 273), lower := (rows 37 42 69 138 82 160 64 128 256), losses := [] }

theorem u22221 : Upper (D 7) (R 7) [36,40,65,130,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22221 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22222 : Route 9 := (fun mask => (mask,id))

def c22222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22222 : Upper (D 7) (R 7) [36,40,65,130,66,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,66,256] 13 (by decide) (choices 1) [1,16,128] r22222 c22222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6707
  · exact u6708
  · exact u6709

def b22223 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 138 208 33 338 402 274), lower := (rows 37 42 69 138 208 33 64 128 256), losses := [] }

theorem u22223 : Upper (D 7) (R 7) [36,40,65,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22223 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22224 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 42, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 37 42 69 138 208 48 323 387 259), lower := (rows 37 42 69 138 208 48 64 128 256), losses := [] }

theorem u22224 : Upper (D 7) (R 7) [36,40,65,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22224 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22225 : Route 9 := (fun mask => (mask,id))

def c22225 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22225 : Upper (D 7) (R 7) [36,40,65,130,192,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,130,192,256] 13 (by decide) (choices 1) [1,2,16] r22225 c22225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6710
  · exact u6711
  · exact u6712

def b22226 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 42 69 138 273 34 208 208 464), lower := (rows 37 42 69 138 273 34 64 128 256), losses := [] }

theorem u22226 : Upper (D 7) (R 7) [36,40,65,130,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22227 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 42 69 138 273 48 194 194 450), lower := (rows 37 42 69 138 273 48 64 128 256), losses := [] }

theorem u22227 : Upper (D 7) (R 7) [36,40,65,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22227 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22228 : PairBound 9 := { available := 146, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 138 273 96 210 146 402), lower := (rows 37 42 69 138 273 96 64 128 256), losses := [] }

theorem u22228 : Upper (D 7) (R 7) [36,40,65,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22229 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 138 273 160 82 210 338), lower := (rows 37 42 69 138 273 160 64 128 256), losses := [] }

theorem u22229 : Upper (D 7) (R 7) [36,40,65,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22230 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 138 336 33 210 146 402), lower := (rows 37 42 69 138 336 33 64 128 256), losses := [] }

theorem u22230 : Upper (D 7) (R 7) [36,40,65,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22231 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 37 42 69 138 336 34 209 145 401), lower := (rows 37 42 69 138 336 34 64 128 256), losses := [] }

theorem u22231 : Upper (D 7) (R 7) [36,40,65,130,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22232 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 37, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 42 69 138 336 48 195 131 387), lower := (rows 37 42 69 138 336 48 64 128 256), losses := [] }

theorem u22232 : Upper (D 7) (R 7) [36,40,65,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22232 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22233 : PairBound 9 := { available := 19, camps := [{ cop := 5, region := 10, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 37 42 69 138 336 160 83 147 275), lower := (rows 37 42 69 138 336 160 64 128 256), losses := [] }

theorem u22233 : Upper (D 7) (R 7) [36,40,65,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22234 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 152 82 33 450 386 386), lower := (rows 37 42 69 152 82 33 64 128 256), losses := [] }

theorem u22234 : Upper (D 7) (R 7) [36,40,65,144,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22234 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22235 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 452, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 69 152 82 34 449 385 385), lower := (rows 37 42 69 152 82 34 64 128 256), losses := [] }

theorem u22235 : Upper (D 7) (R 7) [36,40,65,144,66,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22235 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22236 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 152 82 160 323 387 259), lower := (rows 37 42 69 152 82 160 64 128 256), losses := [] }

theorem u22236 : Upper (D 7) (R 7) [36,40,65,144,66,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22236 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22237 : Route 9 := (fun mask => (mask,id))

def c22237 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22237 : Upper (D 7) (R 7) [36,40,65,144,66,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,66,256] 13 (by decide) (choices 1) [1,2,128] r22237 c22237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6713
  · exact u6714
  · exact u6715

def b22238 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 37 42 69 152 273 34 194 194 450), lower := (rows 37 42 69 152 273 34 64 128 256), losses := [] }

theorem u22238 : Upper (D 7) (R 7) [36,40,65,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22239 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 152 273 96 194 130 386), lower := (rows 37 42 69 152 273 96 64 128 256), losses := [] }

theorem u22239 : Upper (D 7) (R 7) [36,40,65,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22240 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 4, region := 234, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 152 273 160 66 194 322), lower := (rows 37 42 69 152 273 160 64 128 256), losses := [] }

theorem u22240 : Upper (D 7) (R 7) [36,40,65,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22241 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 152 274 33 194 194 450), lower := (rows 37 42 69 152 274 33 64 128 256), losses := [] }

theorem u22241 : Upper (D 7) (R 7) [36,40,65,144,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22242 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 34, targets := 193 },{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 37 42 69 152 274 34 193 193 449), lower := (rows 37 42 69 152 274 34 64 128 256), losses := [] }

theorem u22242 : Upper (D 7) (R 7) [36,40,65,144,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22243 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 5, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 42 69 152 274 96 195 131 387), lower := (rows 37 42 69 152 274 96 64 128 256), losses := [] }

theorem u22243 : Upper (D 7) (R 7) [36,40,65,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22244 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 152 274 160 67 195 323), lower := (rows 37 42 69 152 274 160 64 128 256), losses := [] }

theorem u22244 : Upper (D 7) (R 7) [36,40,65,144,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22245 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 152 336 33 194 130 386), lower := (rows 37 42 69 152 336 33 64 128 256), losses := [] }

theorem u22245 : Upper (D 7) (R 7) [36,40,65,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22246 : Route 9 := (fun mask => (mask,id))

def c22246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u22246 : Upper (D 7) (R 7) [36,40,65,144,320,2] 13 := by
  apply FastRouting.sound _ _ [36,40,65,144,320,2] 13 (by decide) (choices 1) [1,2,128] r22246 c22246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6716
  · exact u6717
  · exact u6718

def b22247 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 152 336 160 67 131 259), lower := (rows 37 42 69 152 336 160 64 128 256), losses := [] }

theorem u22247 : Upper (D 7) (R 7) [36,40,65,144,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22248 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 200 145 34 338 402 274), lower := (rows 37 42 69 200 145 34 64 128 256), losses := [] }

theorem u22248 : Upper (D 7) (R 7) [36,40,65,192,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22249 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 53, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 42 69 200 145 48 322 386 258), lower := (rows 37 42 69 200 145 48 64 128 256), losses := [] }

theorem u22249 : Upper (D 7) (R 7) [36,40,65,192,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22249 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22250 : Route 9 := (fun mask => (mask,id))

def c22250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22250 : Upper (D 7) (R 7) [36,40,65,192,129,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,129,256] 13 (by decide) (choices 1) [2,16] r22250 c22250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6719
  · exact u6720

def b22251 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 200 146 33 338 402 274), lower := (rows 37 42 69 200 146 33 64 128 256), losses := [] }

theorem u22251 : Upper (D 7) (R 7) [36,40,65,192,130,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22252 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 37 42 69 200 146 34 337 401 273), lower := (rows 37 42 69 200 146 34 64 128 256), losses := [] }

theorem u22252 : Upper (D 7) (R 7) [36,40,65,192,130,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22253 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 50, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 37 42 69 200 146 48 323 387 259), lower := (rows 37 42 69 200 146 48 64 128 256), losses := [] }

theorem u22253 : Upper (D 7) (R 7) [36,40,65,192,130,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22253 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r22254 : Route 9 := (fun mask => (mask,id))

def c22254 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u22254 : Upper (D 7) (R 7) [36,40,65,192,130,256] 13 := by
  apply FastRouting.sound _ _ [36,40,65,192,130,256] 13 (by decide) (choices 1) [1,2,16] r22254 c22254
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6721
  · exact u6722
  · exact u6723

def b22255 : PairBound 9 := { available := 146, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 200 273 34 210 146 402), lower := (rows 37 42 69 200 273 34 64 128 256), losses := [] }

theorem u22255 : Upper (D 7) (R 7) [36,40,65,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22256 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 202, targets := 1 },{ cop := 1, region := 200, targets := 32 }], pairs := [(1,0),(3,0),(3,5)], upper := (rows 37 42 69 200 273 48 194 130 386), lower := (rows 37 42 69 200 273 48 64 128 256), losses := [] }

theorem u22256 : Upper (D 7) (R 7) [36,40,65,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22256 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22257 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 341, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 42 69 200 273 160 82 146 274), lower := (rows 37 42 69 200 273 160 64 128 256), losses := [] }

theorem u22257 : Upper (D 7) (R 7) [36,40,65,192,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22258 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 37 42 69 200 274 33 210 146 402), lower := (rows 37 42 69 200 274 33 64 128 256), losses := [] }

theorem u22258 : Upper (D 7) (R 7) [36,40,65,192,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22259 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 39, targets := 128 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 42 69 200 274 34 209 145 401), lower := (rows 37 42 69 200 274 34 64 128 256), losses := [] }

theorem u22259 : Upper (D 7) (R 7) [36,40,65,192,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u22259
end Delivery.IrregularNine14.P07
