import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0136

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r26220 : Route 9 := (fun mask => (mask,id))

def c26220 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26220 : Upper (D 6) (R 6) [40,96,192,18,257,4] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18,257,4] 13 (by decide) (choices 1) [1,2,4] r26220 c26220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8178
  · exact u8179
  · exact u8180

def b26221 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 26 276 33 71 135 263), lower := (rows 41 98 196 26 276 33 64 128 256), losses := [] }

theorem u26221 : Upper (D 6) (R 6) [40,96,192,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26222 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 26 276 34 69 133 261), lower := (rows 41 98 196 26 276 34 64 128 256), losses := [] }

theorem u26222 : Upper (D 6) (R 6) [40,96,192,18,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26223 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 196 26 276 36 67 131 259), lower := (rows 41 98 196 26 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 52 64 128 256), good := (rows 40 98 230 58 318 38 64 128 256) }] }

theorem u26223 : Upper (D 6) (R 6) [40,96,192,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26224 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 196 28 19 33 326 390 262), lower := (rows 41 98 196 28 19 33 64 128 256), losses := [] }

theorem u26224 : Upper (D 6) (R 6) [40,96,192,20,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26225 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 196 28 19 34 325 389 261), lower := (rows 41 98 196 28 19 34 64 128 256), losses := [] }

theorem u26225 : Upper (D 6) (R 6) [40,96,192,20,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26226 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 196 28 19 36 323 387 259), lower := (rows 41 98 196 28 19 36 64 128 256), losses := [] }

theorem u26226 : Upper (D 6) (R 6) [40,96,192,20,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26227 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 41 98 196 28 19 288 71 135 263), lower := (rows 41 98 196 28 19 288 64 128 256), losses := [] }

theorem u26227 : Upper (D 6) (R 6) [40,96,192,20,3,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26227 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26228 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 28 273 33 70 134 262), lower := (rows 41 98 196 28 273 33 64 128 256), losses := [] }

theorem u26228 : Upper (D 6) (R 6) [40,96,192,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26229 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 28 273 34 71 135 263), lower := (rows 41 98 196 28 273 34 64 128 256), losses := [{ target := 2, region := (rows 9 70 0 8 16 110 64 128 256), good := (rows 41 98 226 59 273 34 98 128 256) }] }

theorem u26229 : Upper (D 6) (R 6) [40,96,192,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26230 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 196 28 273 36 67 131 259), lower := (rows 41 98 196 28 273 36 64 128 256), losses := [] }

theorem u26230 : Upper (D 6) (R 6) [40,96,192,20,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26231 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 28 274 33 71 135 263), lower := (rows 41 98 196 28 274 33 64 128 256), losses := [] }

theorem u26231 : Upper (D 6) (R 6) [40,96,192,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26232 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 41 98 196 28 274 34 69 133 261), lower := (rows 41 98 196 28 274 34 64 128 256), losses := [] }

theorem u26232 : Upper (D 6) (R 6) [40,96,192,20,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26233 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 196 28 274 36 67 131 259), lower := (rows 41 98 196 28 274 36 64 128 256), losses := [] }

theorem u26233 : Upper (D 6) (R 6) [40,96,192,20,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26234 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 265 21 34 86 150 278), lower := (rows 41 98 196 265 21 34 64 128 256), losses := [] }

theorem u26234 : Upper (D 6) (R 6) [40,96,192,257,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26235 : Route 9 := (fun mask => (mask,id))

def c26235 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26235 : Upper (D 6) (R 6) [40,96,192,257,5,4] 13 := by
  apply FastRouting.sound _ _ [40,96,192,257,5,4] 13 (by decide) (choices 1) [2,16] r26235 c26235
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8181
  · exact u8182

def b26236 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 196 265 21 48 70 134 262), lower := (rows 41 98 196 265 21 48 64 128 256), losses := [] }

theorem u26236 : Upper (D 6) (R 6) [40,96,192,257,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26236 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26237 : PairBound 9 := { available := 22, camps := [{ cop := 8, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 265 22 33 86 150 278), lower := (rows 41 98 196 265 22 33 64 128 256), losses := [] }

theorem u26237 : Upper (D 6) (R 6) [40,96,192,257,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26238 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 265 22 34 85 149 277), lower := (rows 41 98 196 265 22 34 64 128 256), losses := [] }

theorem u26238 : Upper (D 6) (R 6) [40,96,192,257,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26239 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 265 22 36 83 147 275), lower := (rows 41 98 196 265 22 36 64 128 256), losses := [] }

theorem u26239 : Upper (D 6) (R 6) [40,96,192,257,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26240 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 196 265 22 48 71 135 263), lower := (rows 41 98 196 265 22 48 64 128 256), losses := [] }

theorem u26240 : Upper (D 6) (R 6) [40,96,192,257,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26240 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26241 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 266 21 33 86 150 278), lower := (rows 41 98 196 266 21 33 64 128 256), losses := [] }

theorem u26241 : Upper (D 6) (R 6) [40,96,192,258,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26242 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 266 21 34 85 149 277), lower := (rows 41 98 196 266 21 34 64 128 256), losses := [] }

theorem u26242 : Upper (D 6) (R 6) [40,96,192,258,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26243 : Route 9 := (fun mask => (mask,id))

def c26243 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26243 : Upper (D 6) (R 6) [40,96,192,258,5,4] 13 := by
  apply FastRouting.sound _ _ [40,96,192,258,5,4] 13 (by decide) (choices 1) [1,2,16] r26243 c26243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8183
  · exact u8184
  · exact u8185

def r26244 : Route 9 := (fun mask => (mask,id))

def c26244 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26244 : Upper (D 6) (R 6) [40,96,192,258,5,16] 13 := by
  apply FastRouting.sound _ _ [40,96,192,258,5,16] 13 (by decide) (choices 1) [1,2,4] r26244 c26244
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8186
  · exact u8187
  · exact u8188

def b26245 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 266 22 33 85 149 277), lower := (rows 41 98 196 266 22 33 64 128 256), losses := [] }

theorem u26245 : Upper (D 6) (R 6) [40,96,192,258,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26246 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 266 22 36 81 145 273), lower := (rows 41 98 196 266 22 36 64 128 256), losses := [] }

theorem u26246 : Upper (D 6) (R 6) [40,96,192,258,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26247 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 98 196 266 22 48 69 133 261), lower := (rows 41 98 196 266 22 48 64 128 256), losses := [] }

theorem u26247 : Upper (D 6) (R 6) [40,96,192,258,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26247 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26248 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 196 268 19 33 86 150 278), lower := (rows 41 98 196 268 19 33 64 128 256), losses := [] }

theorem u26248 : Upper (D 6) (R 6) [40,96,192,260,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26249 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 196 268 19 34 85 149 277), lower := (rows 41 98 196 268 19 34 64 128 256), losses := [] }

theorem u26249 : Upper (D 6) (R 6) [40,96,192,260,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26250 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 196 268 19 36 83 147 275), lower := (rows 41 98 196 268 19 36 64 128 256), losses := [] }

theorem u26250 : Upper (D 6) (R 6) [40,96,192,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26251 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 41 98 196 268 19 48 71 135 263), lower := (rows 41 98 196 268 19 48 64 128 256), losses := [] }

theorem u26251 : Upper (D 6) (R 6) [40,96,192,260,3,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26251 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26252 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 196 268 21 33 82 146 274), lower := (rows 41 98 196 268 21 33 64 128 256), losses := [] }

theorem u26252 : Upper (D 6) (R 6) [40,96,192,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26253 : PairBound 9 := { available := 19, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 268 21 34 83 147 275), lower := (rows 41 98 196 268 21 34 64 128 256), losses := [{ target := 2, region := (rows 9 86 0 8 16 126 80 144 272), good := (rows 41 98 226 299 499 34 98 128 256) }] }

theorem u26253 : Upper (D 6) (R 6) [40,96,192,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26254 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 196 268 21 48 67 131 259), lower := (rows 41 98 196 268 21 48 64 128 256), losses := [] }

theorem u26254 : Upper (D 6) (R 6) [40,96,192,260,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26254 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26255 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 268 22 33 83 147 275), lower := (rows 41 98 196 268 22 33 64 128 256), losses := [] }

theorem u26255 : Upper (D 6) (R 6) [40,96,192,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26256 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 268 22 34 81 145 273), lower := (rows 41 98 196 268 22 34 64 128 256), losses := [] }

theorem u26256 : Upper (D 6) (R 6) [40,96,192,260,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26257 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 196 268 22 48 67 131 259), lower := (rows 41 98 196 268 22 48 64 128 256), losses := [] }

theorem u26257 : Upper (D 6) (R 6) [40,96,192,260,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26257 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26258 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 460, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 41 98 196 280 19 33 70 134 262), lower := (rows 41 98 196 280 19 33 64 128 256), losses := [] }

theorem u26258 : Upper (D 6) (R 6) [40,96,192,272,3,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26259 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 196 280 19 34 69 133 261), lower := (rows 41 98 196 280 19 34 64 128 256), losses := [] }

theorem u26259 : Upper (D 6) (R 6) [40,96,192,272,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26260 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 460, targets := 32 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 41 98 196 280 19 36 71 135 263), lower := (rows 41 98 196 280 19 36 64 128 256), losses := [] }

theorem u26260 : Upper (D 6) (R 6) [40,96,192,272,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26261 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 280 21 33 70 134 262), lower := (rows 41 98 196 280 21 33 64 128 256), losses := [] }

theorem u26261 : Upper (D 6) (R 6) [40,96,192,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26262 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 280 21 34 71 135 263), lower := (rows 41 98 196 280 21 34 64 128 256), losses := [{ target := 2, region := (rows 9 70 0 8 16 118 64 128 256), good := (rows 41 98 226 313 51 34 98 128 256) }] }

theorem u26262 : Upper (D 6) (R 6) [40,96,192,272,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26263 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 66, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,2)], upper := (rows 41 98 196 280 21 36 67 131 259), lower := (rows 41 98 196 280 21 36 64 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 52 64 128 256), good := (rows 41 96 228 313 53 36 64 128 256) }] }

theorem u26263 : Upper (D 6) (R 6) [40,96,192,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26264 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 280 22 33 71 135 263), lower := (rows 41 98 196 280 22 33 64 128 256), losses := [] }

theorem u26264 : Upper (D 6) (R 6) [40,96,192,272,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26265 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 41 98 196 280 22 34 69 133 261), lower := (rows 41 98 196 280 22 34 64 128 256), losses := [] }

theorem u26265 : Upper (D 6) (R 6) [40,96,192,272,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26266 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 280 22 36 67 131 259), lower := (rows 41 98 196 280 22 36 64 128 256), losses := [] }

theorem u26266 : Upper (D 6) (R 6) [40,96,192,272,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26267 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 388 13 22 33 82 210 338), lower := (rows 41 98 388 13 22 33 64 128 256), losses := [] }

theorem u26267 : Upper (D 6) (R 6) [40,96,384,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26268 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,6),(1,0),(3,6)], upper := (rows 41 98 388 13 22 34 81 209 337), lower := (rows 41 98 388 13 22 34 64 128 256), losses := [] }

theorem u26268 : Upper (D 6) (R 6) [40,96,384,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26269 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 388 13 22 48 67 195 323), lower := (rows 41 98 388 13 22 48 64 128 256), losses := [] }

theorem u26269 : Upper (D 6) (R 6) [40,96,384,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26269 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26270 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 388 13 22 96 83 147 275), lower := (rows 41 98 388 13 22 96 64 128 256), losses := [] }

theorem u26270 : Upper (D 6) (R 6) [40,96,384,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26271 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 422, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 388 13 81 34 86 150 278), lower := (rows 41 98 388 13 81 34 64 128 256), losses := [] }

theorem u26271 : Upper (D 6) (R 6) [40,96,384,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26272 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 388 13 81 36 82 146 274), lower := (rows 41 98 388 13 81 36 64 128 256), losses := [] }

theorem u26272 : Upper (D 6) (R 6) [40,96,384,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26273 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 388 13 81 48 70 134 262), lower := (rows 41 98 388 13 81 48 64 128 256), losses := [] }

theorem u26273 : Upper (D 6) (R 6) [40,96,384,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26273 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26274 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 388 13 84 33 82 146 274), lower := (rows 41 98 388 13 84 33 64 128 256), losses := [] }

theorem u26274 : Upper (D 6) (R 6) [40,96,384,5,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26275 : Route 9 := (fun mask => (mask,id))

def c26275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26275 : Upper (D 6) (R 6) [40,96,384,5,68,2] 13 := by
  apply FastRouting.sound _ _ [40,96,384,5,68,2] 13 (by decide) (choices 1) [1,2,16] r26275 c26275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8189
  · exact u8190
  · exact u8191

def b26276 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 388 13 84 48 67 131 259), lower := (rows 41 98 388 13 84 48 64 128 256), losses := [] }

theorem u26276 : Upper (D 6) (R 6) [40,96,384,5,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26276 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26277 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 388 14 21 33 82 210 338), lower := (rows 41 98 388 14 21 33 64 128 256), losses := [] }

theorem u26277 : Upper (D 6) (R 6) [40,96,384,6,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26278 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 388 14 21 34 81 209 337), lower := (rows 41 98 388 14 21 34 64 128 256), losses := [] }

theorem u26278 : Upper (D 6) (R 6) [40,96,384,6,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26279 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 388 14 21 48 67 195 323), lower := (rows 41 98 388 14 21 48 64 128 256), losses := [] }

theorem u26279 : Upper (D 6) (R 6) [40,96,384,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26279 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26279
end Delivery.IrregularNine14.P06
