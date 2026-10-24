import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0015
import IrregularNine14P06C0016

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9240 : PairBound 9 := { available := 100, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 138 336 33 100 228 356), lower := (rows 7 26 37 138 336 33 64 128 256), losses := [] }

theorem u9240 : Upper (D 6) (R 6) [6,24,33,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9241 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 138 336 36 97 225 353), lower := (rows 7 26 37 138 336 36 64 128 256), losses := [] }

theorem u9241 : Upper (D 6) (R 6) [6,24,33,130,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9242 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 372, targets := 2 }], pairs := [(2,1),(3,6),(4,1)], upper := (rows 7 26 37 138 336 96 101 165 293), lower := (rows 7 26 37 138 336 96 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 16 32 0 132 260), good := (rows 399 26 429 138 272 32 0 128 256) }] }

theorem u9242 : Upper (D 6) (R 6) [6,24,33,130,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9243 : PairBound 9 := { available := 98, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 140 336 33 98 226 354), lower := (rows 7 26 37 140 336 33 64 128 256), losses := [] }

theorem u9243 : Upper (D 6) (R 6) [6,24,33,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9244 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 200, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 26 37 140 336 34 97 225 353), lower := (rows 7 26 37 140 336 34 64 128 256), losses := [] }

theorem u9244 : Upper (D 6) (R 6) [6,24,33,132,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9244 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9245 : Route 9 := (fun mask => (mask,id))

def c9245 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9245 : Upper (D 6) (R 6) [6,24,33,132,320,64] 13 := by
  apply FastRouting.sound _ _ [6,24,33,132,320,64] 13 (by decide) (choices 1) [1,2,32] r9245 c9245
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u932
  · exact u933
  · exact u934

def b9246 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 168 336 33 70 198 326), lower := (rows 7 26 37 168 336 33 64 128 256), losses := [] }

theorem u9246 : Upper (D 6) (R 6) [6,24,33,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9247 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(4,1),(4,5)], upper := (rows 7 26 37 168 336 34 69 197 325), lower := (rows 7 26 37 168 336 34 64 128 256), losses := [] }

theorem u9247 : Upper (D 6) (R 6) [6,24,33,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9248 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 168 336 36 67 195 323), lower := (rows 7 26 37 168 336 36 64 128 256), losses := [] }

theorem u9248 : Upper (D 6) (R 6) [6,24,33,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9249 : Route 9 := (fun mask => (mask,id))

def c9249 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9249 : Upper (D 6) (R 6) [6,24,33,160,320,64] 13 := by
  apply FastRouting.sound _ _ [6,24,33,160,320,64] 13 (by decide) (choices 1) [1,2,4] r9249 c9249
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u935
  · exact u936
  · exact u937

def b9250 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 37 200 336 33 102 166 294), lower := (rows 7 26 37 200 336 33 64 128 256), losses := [] }

theorem u9250 : Upper (D 6) (R 6) [6,24,33,192,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9251 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 200, targets := 2 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 7 26 37 200 336 34 101 165 293), lower := (rows 7 26 37 200 336 34 64 128 256), losses := [] }

theorem u9251 : Upper (D 6) (R 6) [6,24,33,192,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9252 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 474, targets := 4 }], pairs := [(1,2),(3,2),(4,2)], upper := (rows 7 26 37 200 336 36 99 163 291), lower := (rows 7 26 37 200 336 36 64 128 256), losses := [] }

theorem u9252 : Upper (D 6) (R 6) [6,24,33,192,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9253 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 26 100 41 400 33 70 198 326), lower := (rows 7 26 100 41 400 33 64 128 256), losses := [] }

theorem u9253 : Upper (D 6) (R 6) [6,24,96,33,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9253 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9254 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 26 100 41 400 34 69 197 325), lower := (rows 7 26 100 41 400 34 64 128 256), losses := [] }

theorem u9254 : Upper (D 6) (R 6) [6,24,96,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9255 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 466, targets := 36 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 7 26 100 41 400 36 67 195 323), lower := (rows 7 26 100 41 400 36 64 128 256), losses := [] }

theorem u9255 : Upper (D 6) (R 6) [6,24,96,33,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9256 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 41 400 96 71 135 263), lower := (rows 7 26 100 41 400 96 64 128 256), losses := [] }

theorem u9256 : Upper (D 6) (R 6) [6,24,96,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9257 : PairBound 9 := { available := 100, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 273 34 100 228 356), lower := (rows 7 26 100 137 273 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 100 164 292), good := (rows 477 24 484 153 281 484 64 128 256) }] }

theorem u9257 : Upper (D 6) (R 6) [6,24,96,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m9258_2 : Upper (D 6) (R 6) [6,24,96,129,257,4,2] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u938

def r9258 : Route 9 := (fun mask => (mask,id))

def c9258 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9258 : Upper (D 6) (R 6) [6,24,96,129,257,4] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257,4] 13 (by decide) (choices 1) [2,32] r9258 c9258
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9258_2
  · exact u939

def b9259 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 137 273 96 102 166 294), lower := (rows 7 26 100 137 273 96 64 128 256), losses := [] }

theorem u9259 : Upper (D 6) (R 6) [6,24,96,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9260 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 274 33 100 228 356), lower := (rows 7 26 100 137 274 33 64 128 256), losses := [] }

theorem u9260 : Upper (D 6) (R 6) [6,24,96,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9261 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 274 36 97 225 353), lower := (rows 7 26 100 137 274 36 64 128 256), losses := [] }

theorem u9261 : Upper (D 6) (R 6) [6,24,96,129,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9262 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 137 274 96 101 165 293), lower := (rows 7 26 100 137 274 96 64 128 256), losses := [] }

theorem u9262 : Upper (D 6) (R 6) [6,24,96,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9262 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9263 : Route 9 := (fun mask => (mask,id))

def c9263 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9263 : Upper (D 6) (R 6) [6,24,96,129,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260,1] 13 (by decide) (choices 1) [2,32] r9263 c9263
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u940
  · exact u941

theorem m9264_1 : Upper (D 6) (R 6) [6,24,96,129,260,2,1] 13 :=
  permutation_upper _ _ _ [6,24,96,129,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u940

def r9264 : Route 9 := (fun mask => (mask,id))

def c9264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9264 : Upper (D 6) (R 6) [6,24,96,129,260,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,260,2] 13 (by decide) (choices 1) [1,32] r9264 c9264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9264_1
  · exact u942

def b9265 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 137 276 96 99 163 291), lower := (rows 7 26 100 137 276 96 64 128 256), losses := [] }

theorem u9265 : Upper (D 6) (R 6) [6,24,96,129,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9266 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(2,0),(3,5),(4,0)], upper := (rows 7 26 100 137 304 33 70 198 326), lower := (rows 7 26 100 137 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 48 32 65 129 257), good := (rows 454 26 116 456 308 500 64 128 256) }] }

theorem u9266 : Upper (D 6) (R 6) [6,24,96,129,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9267 : Route 9 := (fun mask => (mask,id))

def c9267 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9267 : Upper (D 6) (R 6) [6,24,96,129,288,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,2] 13 (by decide) (choices 1) [1,4] r9267 c9267
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u943
  · exact u944

def b9268 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 200, targets := 36 },{ cop := 6, region := 36, targets := 1 }], pairs := [(2,0),(3,2),(3,5)], upper := (rows 7 26 100 137 304 36 67 195 323), lower := (rows 7 26 100 137 304 36 64 128 256), losses := [] }

theorem u9268 : Upper (D 6) (R 6) [6,24,96,129,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9269 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 137 304 96 71 135 263), lower := (rows 7 26 100 137 304 96 64 128 256), losses := [] }

theorem u9269 : Upper (D 6) (R 6) [6,24,96,129,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9270 : Route 9 := (fun mask => (mask,id))

def c9270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9270 : Upper (D 6) (R 6) [6,24,96,132,288,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132,288,1] 13 (by decide) (choices 1) [1,2] r9270 c9270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u945
  · exact u946

def b9271 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(3,5),(4,2)], upper := (rows 7 26 100 140 304 34 65 193 321), lower := (rows 7 26 100 140 304 34 64 128 256), losses := [] }

theorem u9271 : Upper (D 6) (R 6) [6,24,96,132,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9272 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 26 100 140 304 96 67 131 259), lower := (rows 7 26 100 140 304 96 64 128 256), losses := [] }

theorem u9272 : Upper (D 6) (R 6) [6,24,96,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9273 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 336, targets := 32 },{ cop := 0, region := 168, targets := 64 }], pairs := [(1,5),(3,6),(4,5)], upper := (rows 7 26 100 168 336 33 71 135 263), lower := (rows 7 26 100 168 336 33 64 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 49 0 65 129 257), good := (rows 471 26 84 154 336 465 64 128 256) }] }

theorem u9273 : Upper (D 6) (R 6) [6,24,96,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9274 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6),(4,1),(4,5)], upper := (rows 7 26 100 168 336 34 69 133 261), lower := (rows 7 26 100 168 336 34 64 128 256), losses := [] }

theorem u9274 : Upper (D 6) (R 6) [6,24,96,160,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9275 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 336, targets := 36 },{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0),(4,2),(4,5)], upper := (rows 7 26 100 168 336 36 67 131 259), lower := (rows 7 26 100 168 336 36 64 128 256), losses := [] }

theorem u9275 : Upper (D 6) (R 6) [6,24,96,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9276 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 40, targets := 68 },{ cop := 3, region := 196, targets := 2 }], pairs := [(2,1),(3,2),(3,6)], upper := (rows 7 26 133 41 336 34 100 228 356), lower := (rows 7 26 133 41 336 34 64 128 256), losses := [] }

theorem u9276 : Upper (D 6) (R 6) [6,24,129,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9277 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 41 336 36 98 226 354), lower := (rows 7 26 133 41 336 36 64 128 256), losses := [] }

theorem u9277 : Upper (D 6) (R 6) [6,24,129,33,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9278 : Route 9 := (fun mask => (mask,id))

def c9278 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9278 : Upper (D 6) (R 6) [6,24,129,33,320,64] 13 := by
  apply FastRouting.sound _ _ [6,24,129,33,320,64] 13 (by decide) (choices 1) [2,4,32] r9278 c9278
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u947
  · exact u948
  · exact u949

def b9279 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 40, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 133 42 336 33 100 228 356), lower := (rows 7 26 133 42 336 33 64 128 256), losses := [] }

theorem u9279 : Upper (D 6) (R 6) [6,24,129,34,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9280 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 40, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 133 42 336 36 97 225 353), lower := (rows 7 26 133 42 336 36 64 128 256), losses := [] }

theorem u9280 : Upper (D 6) (R 6) [6,24,129,34,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9281 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 133 42 336 96 101 165 293), lower := (rows 7 26 133 42 336 96 64 128 256), losses := [] }

theorem u9281 : Upper (D 6) (R 6) [6,24,129,34,320,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9282 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 338, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 44 336 33 98 226 354), lower := (rows 7 26 133 44 336 33 64 128 256), losses := [] }

theorem u9282 : Upper (D 6) (R 6) [6,24,129,36,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9283 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 40, targets := 1 },{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 40, targets := 64 }], pairs := [(3,0),(3,6),(4,2)], upper := (rows 7 26 133 44 336 34 97 225 353), lower := (rows 7 26 133 44 336 34 64 128 256), losses := [] }

theorem u9283 : Upper (D 6) (R 6) [6,24,129,36,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9284 : Route 9 := (fun mask => (mask,id))

def c9284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9284 : Upper (D 6) (R 6) [6,24,129,36,320,64] 13 := by
  apply FastRouting.sound _ _ [6,24,129,36,320,64] 13 (by decide) (choices 1) [1,2,32] r9284 c9284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u950
  · exact u951
  · exact u952

def r9285 : Route 9 := (fun mask => (mask,id))

def c9285 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9285 : Upper (D 6) (R 6) [6,24,129,96,257,2] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,257,2] 13 (by decide) (choices 1) [4,32] r9285 c9285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u953
  · exact u954

theorem m9286_2 : Upper (D 6) (R 6) [6,24,129,96,257,4,2] 13 :=
  permutation_upper _ _ _ [6,24,129,96,257,2,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u953

def r9286 : Route 9 := (fun mask => (mask,id))

def c9286 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9286 : Upper (D 6) (R 6) [6,24,129,96,257,4] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,257,4] 13 (by decide) (choices 1) [2,32] r9286 c9286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9286_2
  · exact u955

def b9287 : PairBound 9 := { available := 38, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 133 104 273 96 102 166 294), lower := (rows 7 26 133 104 273 96 64 128 256), losses := [] }

theorem u9287 : Upper (D 6) (R 6) [6,24,129,96,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9288 : Route 9 := (fun mask => (mask,id))

def c9288 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9288 : Upper (D 6) (R 6) [6,24,129,96,258,1] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,258,1] 13 (by decide) (choices 1) [4,32] r9288 c9288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u956
  · exact u957

theorem m9289_1 : Upper (D 6) (R 6) [6,24,129,96,258,4,1] 13 :=
  permutation_upper _ _ _ [6,24,129,96,258,1,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u956

def r9289 : Route 9 := (fun mask => (mask,id))

def c9289 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9289 : Upper (D 6) (R 6) [6,24,129,96,258,4] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,258,4] 13 (by decide) (choices 1) [1,32] r9289 c9289
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9289_1
  · exact u958

def b9290 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 133 104 274 96 101 165 293), lower := (rows 7 26 133 104 274 96 64 128 256), losses := [] }

theorem u9290 : Upper (D 6) (R 6) [6,24,129,96,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9291 : Route 9 := (fun mask => (mask,id))

def c9291 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9291 : Upper (D 6) (R 6) [6,24,129,96,260,1] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,260,1] 13 (by decide) (choices 1) [2,32] r9291 c9291
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u959
  · exact u960

theorem m9292_1 : Upper (D 6) (R 6) [6,24,129,96,260,2,1] 13 :=
  permutation_upper _ _ _ [6,24,129,96,260,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u959

def r9292 : Route 9 := (fun mask => (mask,id))

def c9292 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9292 : Upper (D 6) (R 6) [6,24,129,96,260,2] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,260,2] 13 (by decide) (choices 1) [1,32] r9292 c9292
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m9292_1
  · exact u961

def b9293 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 133 104 276 96 99 163 291), lower := (rows 7 26 133 104 276 96 64 128 256), losses := [] }

theorem u9293 : Upper (D 6) (R 6) [6,24,129,96,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9294 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 26 133 104 304 33 70 198 326), lower := (rows 7 26 133 104 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 58 4 40 48 32 65 129 257), good := (rows 454 26 452 122 314 506 64 128 256) }] }

theorem u9294 : Upper (D 6) (R 6) [6,24,129,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9295 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,1),(2,5)], upper := (rows 7 26 133 104 304 34 69 197 325), lower := (rows 7 26 133 104 304 34 64 128 256), losses := [] }

theorem u9295 : Upper (D 6) (R 6) [6,24,129,96,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9296 : Route 9 := (fun mask => (mask,id))

def c9296 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9296 : Upper (D 6) (R 6) [6,24,129,96,288,4] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,288,4] 13 (by decide) (choices 1) [1,2] r9296 c9296
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u962
  · exact u963

def b9297 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 133 104 304 96 71 135 263), lower := (rows 7 26 133 104 304 96 64 128 256), losses := [] }

theorem u9297 : Upper (D 6) (R 6) [6,24,129,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9298 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 40, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 7 26 164 41 336 33 70 198 326), lower := (rows 7 26 164 41 336 33 64 128 256), losses := [] }

theorem u9298 : Upper (D 6) (R 6) [6,24,160,33,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9299 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 336, targets := 34 },{ cop := 0, region := 40, targets := 4 }], pairs := [(3,2),(4,1),(4,5)], upper := (rows 7 26 164 41 336 34 69 197 325), lower := (rows 7 26 164 41 336 34 64 128 256), losses := [] }

theorem u9299 : Upper (D 6) (R 6) [6,24,160,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b9299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9299
end Delivery.IrregularNine14.P06
