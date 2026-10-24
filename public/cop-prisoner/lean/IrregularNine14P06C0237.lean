import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0051
import IrregularNine14P06C0052

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r14220 : Route 9 := (fun mask => (mask,id))

def c14220 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14220 : Upper (D 6) (R 6) [10,48,96,132,65,256] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,65,256] 13 (by decide) (choices 1) [1,2,4] r14220 c14220
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3101
  · exact u3102
  · exact u3103

def b14221 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 140 273 33 70 198 326), lower := (rows 11 50 100 140 273 33 64 128 256), losses := [] }

theorem u14221 : Upper (D 6) (R 6) [10,48,96,132,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14222 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 140 273 34 69 197 325), lower := (rows 11 50 100 140 273 34 64 128 256), losses := [] }

theorem u14222 : Upper (D 6) (R 6) [10,48,96,132,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14223 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 11 50 100 140 273 36 67 195 323), lower := (rows 11 50 100 140 273 36 64 128 256), losses := [] }

theorem u14223 : Upper (D 6) (R 6) [10,48,96,132,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14224 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 140 273 96 71 135 263), lower := (rows 11 50 100 140 273 96 64 128 256), losses := [] }

theorem u14224 : Upper (D 6) (R 6) [10,48,96,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14224 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14225 : Route 9 := (fun mask => (mask,id))

def c14225 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14225 : Upper (D 6) (R 6) [10,48,96,132,258,1] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,258,1] 13 (by decide) (choices 1) [1,4] r14225 c14225
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3104
  · exact u3105

def b14226 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 11 50 100 140 274 36 65 193 321), lower := (rows 11 50 100 140 274 36 64 128 256), losses := [] }

theorem u14226 : Upper (D 6) (R 6) [10,48,96,132,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14227 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 140 274 96 69 133 261), lower := (rows 11 50 100 140 274 96 64 128 256), losses := [] }

theorem u14227 : Upper (D 6) (R 6) [10,48,96,132,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14228 : Route 9 := (fun mask => (mask,id))

def c14228 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14228 : Upper (D 6) (R 6) [10,48,96,132,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,260,1] 13 (by decide) (choices 1) [1,2] r14228 c14228
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3106
  · exact u3107

def b14229 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 140 276 34 65 193 321), lower := (rows 11 50 100 140 276 34 64 128 256), losses := [] }

theorem u14229 : Upper (D 6) (R 6) [10,48,96,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14230 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 140 276 96 67 131 259), lower := (rows 11 50 100 140 276 96 64 128 256), losses := [] }

theorem u14230 : Upper (D 6) (R 6) [10,48,96,132,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14231 : Route 9 := (fun mask => (mask,id))

def c14231 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14231 : Upper (D 6) (R 6) [10,48,96,132,320,1] 13 := by
  apply FastRouting.sound _ _ [10,48,96,132,320,1] 13 (by decide) (choices 1) [1,2,4] r14231 c14231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3108
  · exact u3109
  · exact u3110

def b14232 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 140 336 34 69 133 261), lower := (rows 11 50 100 140 336 34 64 128 256), losses := [] }

theorem u14232 : Upper (D 6) (R 6) [10,48,96,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14233 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 38, targets := 1 }], pairs := [(1,0),(4,2),(4,5)], upper := (rows 11 50 100 140 336 36 67 131 259), lower := (rows 11 50 100 140 336 36 64 128 256), losses := [] }

theorem u14233 : Upper (D 6) (R 6) [10,48,96,132,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14234 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 200 21 33 326 390 262), lower := (rows 11 50 100 200 21 33 64 128 256), losses := [] }

theorem u14234 : Upper (D 6) (R 6) [10,48,96,192,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14235 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 34, targets := 5 },{ cop := 4, region := 456, targets := 2 }], pairs := [(1,0),(1,2),(3,1)], upper := (rows 11 50 100 200 21 34 325 389 261), lower := (rows 11 50 100 200 21 34 64 128 256), losses := [] }

theorem u14235 : Upper (D 6) (R 6) [10,48,96,192,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14235 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14236 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 200 21 36 323 387 259), lower := (rows 11 50 100 200 21 36 64 128 256), losses := [] }

theorem u14236 : Upper (D 6) (R 6) [10,48,96,192,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14237 : Route 9 := (fun mask => (mask,id))

def c14237 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14237 : Upper (D 6) (R 6) [10,48,96,192,5,256] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,5,256] 13 (by decide) (choices 1) [1,2,4] r14237 c14237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3111
  · exact u3112
  · exact u3113

def b14238 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 204, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 200 273 33 70 134 262), lower := (rows 11 50 100 200 273 33 64 128 256), losses := [] }

theorem u14238 : Upper (D 6) (R 6) [10,48,96,192,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14238 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14239 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 200 273 34 69 133 261), lower := (rows 11 50 100 200 273 34 64 128 256), losses := [] }

theorem u14239 : Upper (D 6) (R 6) [10,48,96,192,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14240 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 200 273 36 71 135 263), lower := (rows 11 50 100 200 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 76 8 16 109 64 128 256), good := (rows 46 50 100 236 306 36 100 128 256) }] }

theorem u14240 : Upper (D 6) (R 6) [10,48,96,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14241 : Route 9 := (fun mask => (mask,id))

def c14241 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14241 : Upper (D 6) (R 6) [10,48,96,192,258,1] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,258,1] 13 (by decide) (choices 1) [1,4] r14241 c14241
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3114
  · exact u3115

def b14242 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 3, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 50 100 200 274 36 69 133 261), lower := (rows 11 50 100 200 274 36 64 128 256), losses := [] }

theorem u14242 : Upper (D 6) (R 6) [10,48,96,192,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14243 : Route 9 := (fun mask => (mask,id))

def c14243 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14243 : Upper (D 6) (R 6) [10,48,96,192,260,1] 13 := by
  apply FastRouting.sound _ _ [10,48,96,192,260,1] 13 (by decide) (choices 1) [1,2,4] r14243 c14243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3116
  · exact u3117
  · exact u3118

def b14244 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 200 276 34 69 133 261), lower := (rows 11 50 100 200 276 34 64 128 256), losses := [] }

theorem u14244 : Upper (D 6) (R 6) [10,48,96,192,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14245 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 200 276 36 67 131 259), lower := (rows 11 50 100 200 276 36 64 128 256), losses := [] }

theorem u14245 : Upper (D 6) (R 6) [10,48,96,192,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14246 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 392 21 33 70 198 326), lower := (rows 11 50 100 392 21 33 64 128 256), losses := [] }

theorem u14246 : Upper (D 6) (R 6) [10,48,96,384,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14247 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 100 392 21 34 69 197 325), lower := (rows 11 50 100 392 21 34 64 128 256), losses := [] }

theorem u14247 : Upper (D 6) (R 6) [10,48,96,384,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14248 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 457, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 11 50 100 392 21 36 67 195 323), lower := (rows 11 50 100 392 21 36 64 128 256), losses := [] }

theorem u14248 : Upper (D 6) (R 6) [10,48,96,384,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14249 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 100 392 21 96 71 135 263), lower := (rows 11 50 100 392 21 96 64 128 256), losses := [] }

theorem u14249 : Upper (D 6) (R 6) [10,48,96,384,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14250 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 460, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,0),(3,0)], upper := (rows 11 50 100 392 81 33 70 134 262), lower := (rows 11 50 100 392 81 33 64 128 256), losses := [] }

theorem u14250 : Upper (D 6) (R 6) [10,48,96,384,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14251 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 11 50 100 392 81 34 69 133 261), lower := (rows 11 50 100 392 81 34 64 128 256), losses := [] }

theorem u14251 : Upper (D 6) (R 6) [10,48,96,384,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14252 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 38, targets := 1 },{ cop := 4, region := 36, targets := 2 }], pairs := [(1,0),(2,0),(2,1)], upper := (rows 11 50 100 392 81 36 71 135 263), lower := (rows 11 50 100 392 81 36 64 128 256), losses := [] }

theorem u14252 : Upper (D 6) (R 6) [10,48,96,384,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14253 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 44 81 34 324 452 324), lower := (rows 11 50 133 44 81 34 64 128 256), losses := [] }

theorem u14253 : Upper (D 6) (R 6) [10,48,129,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14254 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 133 44 81 36 322 450 322), lower := (rows 11 50 133 44 81 36 64 128 256), losses := [] }

theorem u14254 : Upper (D 6) (R 6) [10,48,129,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14255 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 44 81 96 326 390 262), lower := (rows 11 50 133 44 81 96 64 128 256), losses := [] }

theorem u14255 : Upper (D 6) (R 6) [10,48,129,36,65,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14256 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 133 44 81 288 70 198 326), lower := (rows 11 50 133 44 81 288 64 128 256), losses := [] }

theorem u14256 : Upper (D 6) (R 6) [10,48,129,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14256 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14257 : PairBound 9 := { available := 322, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 133 44 84 33 322 450 322), lower := (rows 11 50 133 44 84 33 64 128 256), losses := [] }

theorem u14257 : Upper (D 6) (R 6) [10,48,129,36,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14258 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 44 84 34 321 449 321), lower := (rows 11 50 133 44 84 34 64 128 256), losses := [] }

theorem u14258 : Upper (D 6) (R 6) [10,48,129,36,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14259 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 44 84 96 323 387 259), lower := (rows 11 50 133 44 84 96 64 128 256), losses := [] }

theorem u14259 : Upper (D 6) (R 6) [10,48,129,36,68,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14260 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 11 50 133 44 84 288 67 195 323), lower := (rows 11 50 133 44 84 288 64 128 256), losses := [] }

theorem u14260 : Upper (D 6) (R 6) [10,48,129,36,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14260 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14261 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 44 273 34 68 196 324), lower := (rows 11 50 133 44 273 34 64 128 256), losses := [] }

theorem u14261 : Upper (D 6) (R 6) [10,48,129,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14262 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 133 44 273 36 66 194 322), lower := (rows 11 50 133 44 273 36 64 128 256), losses := [] }

theorem u14262 : Upper (D 6) (R 6) [10,48,129,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14263 : Route 9 := (fun mask => (mask,id))

def c14263 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14263 : Upper (D 6) (R 6) [10,48,129,36,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,36,257,64] 13 (by decide) (choices 1) [2,4] r14263 c14263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3119
  · exact u3120

def b14264 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 50 133 44 276 33 66 194 322), lower := (rows 11 50 133 44 276 33 64 128 256), losses := [] }

theorem u14264 : Upper (D 6) (R 6) [10,48,129,36,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14265 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 44 276 34 65 193 321), lower := (rows 11 50 133 44 276 34 64 128 256), losses := [] }

theorem u14265 : Upper (D 6) (R 6) [10,48,129,36,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14266 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(1,2),(2,5),(4,5)], upper := (rows 11 50 133 44 276 96 67 195 323), lower := (rows 11 50 133 44 276 96 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 101 65 129 257), good := (rows 491 50 481 40 306 96 96 128 256) }] }

theorem u14266 : Upper (D 6) (R 6) [10,48,129,36,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14267 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 40, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 50 133 44 336 33 70 198 326), lower := (rows 11 50 133 44 336 33 64 128 256), losses := [] }

theorem u14267 : Upper (D 6) (R 6) [10,48,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14268 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 11 50 133 44 336 34 69 197 325), lower := (rows 11 50 133 44 336 34 64 128 256), losses := [] }

theorem u14268 : Upper (D 6) (R 6) [10,48,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14269 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 50 133 44 336 36 67 195 323), lower := (rows 11 50 133 44 336 36 64 128 256), losses := [] }

theorem u14269 : Upper (D 6) (R 6) [10,48,129,36,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14270 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 11 50 133 44 336 96 71 135 263), lower := (rows 11 50 133 44 336 96 64 128 256), losses := [] }

theorem u14270 : Upper (D 6) (R 6) [10,48,129,36,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14271 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 4, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 50 133 73 276 34 100 228 356), lower := (rows 11 50 133 73 276 34 64 128 256), losses := [] }

theorem u14271 : Upper (D 6) (R 6) [10,48,129,65,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14272 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 73, targets := 4 },{ cop := 2, region := 370, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 50 133 73 276 36 98 226 354), lower := (rows 11 50 133 73 276 36 64 128 256), losses := [] }

theorem u14272 : Upper (D 6) (R 6) [10,48,129,65,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14273 : Route 9 := (fun mask => (mask,id))

def c14273 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14273 : Upper (D 6) (R 6) [10,48,129,65,260,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,65,260,64] 13 (by decide) (choices 1) [2,4,32] r14273 c14273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3121
  · exact u3122
  · exact u3123

def b14274 : PairBound 9 := { available := 292, camps := [{ cop := 3, region := 51, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 50 133 76 81 34 356 420 292), lower := (rows 11 50 133 76 81 34 64 128 256), losses := [] }

theorem u14274 : Upper (D 6) (R 6) [10,48,129,68,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14275 : PairBound 9 := { available := 290, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6),(3,0)], upper := (rows 11 50 133 76 81 36 354 418 290), lower := (rows 11 50 133 76 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 16 44 67 131 259), good := (rows 490 498 492 108 464 44 64 128 256) }] }

theorem u14275 : Upper (D 6) (R 6) [10,48,129,68,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14276 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 11 50 133 76 81 288 102 166 294), lower := (rows 11 50 133 76 81 288 64 128 256), losses := [] }

theorem u14276 : Upper (D 6) (R 6) [10,48,129,68,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14276 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b14277 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 34, targets := 69 }], pairs := [(1,0),(1,2),(1,6)], upper := (rows 11 50 133 76 273 34 100 228 356), lower := (rows 11 50 133 76 273 34 64 128 256), losses := [] }

theorem u14277 : Upper (D 6) (R 6) [10,48,129,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b14277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r14278 : Route 9 := (fun mask => (mask,id))

def c14278 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14278 : Upper (D 6) (R 6) [10,48,129,68,257,4] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,257,4] 13 (by decide) (choices 1) [2,32] r14278 c14278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3124
  · exact u3125

def r14279 : Route 9 := (fun mask => (mask,id))

def c14279 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14279 : Upper (D 6) (R 6) [10,48,129,68,257,64] 13 := by
  apply FastRouting.sound _ _ [10,48,129,68,257,64] 13 (by decide) (choices 1) [2,4,32] r14279 c14279
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3126
  · exact u3127
  · exact u3128

#print axioms u14279
end Delivery.IrregularNine14.P06
