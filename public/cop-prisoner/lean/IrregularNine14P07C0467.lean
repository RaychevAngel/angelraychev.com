import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0173

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28020 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 162 7 74 145 36 344 408 280), lower := (rows 97 162 7 74 145 36 64 128 256), losses := [] }

theorem u28020 : Upper (D 7) (R 7) [96,160,3,66,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28020 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28021 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 74 145 40 340 404 276), lower := (rows 97 162 7 74 145 40 64 128 256), losses := [] }

theorem u28021 : Upper (D 7) (R 7) [96,160,3,66,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28021 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28022 : Route 9 := (fun mask => (mask,id))

def c28022 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28022 : Upper (D 7) (R 7) [96,160,3,66,129,256] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,129,256] 13 (by decide) (choices 1) [4,8,16] r28022 c28022
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10391
  · exact u10392
  · exact u10393

def b28023 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 74 148 33 344 408 280), lower := (rows 97 162 7 74 148 33 64 128 256), losses := [] }

theorem u28023 : Upper (D 7) (R 7) [96,160,3,66,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28024 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 74 148 40 337 401 273), lower := (rows 97 162 7 74 148 40 64 128 256), losses := [] }

theorem u28024 : Upper (D 7) (R 7) [96,160,3,66,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28024 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28025 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 148 48 329 393 265), lower := (rows 97 162 7 74 148 48 64 128 256), losses := [] }

theorem u28025 : Upper (D 7) (R 7) [96,160,3,66,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28025 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28026 : Route 9 := (fun mask => (mask,id))

def c28026 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28026 : Upper (D 7) (R 7) [96,160,3,66,132,256] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,132,256] 13 (by decide) (choices 1) [1,8,16] r28026 c28026
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10394
  · exact u10395
  · exact u10396

def b28027 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 74 152 33 340 404 276), lower := (rows 97 162 7 74 152 33 64 128 256), losses := [] }

theorem u28027 : Upper (D 7) (R 7) [96,160,3,66,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28028 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 162 7 74 152 36 337 401 273), lower := (rows 97 162 7 74 152 36 64 128 256), losses := [] }

theorem u28028 : Upper (D 7) (R 7) [96,160,3,66,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28028 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28029 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 152 48 325 389 261), lower := (rows 97 162 7 74 152 48 64 128 256), losses := [] }

theorem u28029 : Upper (D 7) (R 7) [96,160,3,66,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28029 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28030 : Route 9 := (fun mask => (mask,id))

def c28030 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28030 : Upper (D 7) (R 7) [96,160,3,66,136,256] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,136,256] 13 (by decide) (choices 1) [1,4,16] r28030 c28030
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10397
  · exact u10398
  · exact u10399

def b28031 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 162 7 74 273 36 216 152 408), lower := (rows 97 162 7 74 273 36 64 128 256), losses := [] }

theorem u28031 : Upper (D 7) (R 7) [96,160,3,66,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28031 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28032 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 74 273 40 212 148 404), lower := (rows 97 162 7 74 273 40 64 128 256), losses := [] }

theorem u28032 : Upper (D 7) (R 7) [96,160,3,66,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28032 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28033 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 97 162 7 74 273 48 204 140 396), lower := (rows 97 162 7 74 273 48 64 128 256), losses := [] }

theorem u28033 : Upper (D 7) (R 7) [96,160,3,66,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28033 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28034 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 74 273 160 92 156 284), lower := (rows 97 162 7 74 273 160 64 128 256), losses := [] }

theorem u28034 : Upper (D 7) (R 7) [96,160,3,66,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28034 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28035 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 74 276 33 216 152 408), lower := (rows 97 162 7 74 276 33 64 128 256), losses := [] }

theorem u28035 : Upper (D 7) (R 7) [96,160,3,66,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28036 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 74 276 40 209 145 401), lower := (rows 97 162 7 74 276 40 64 128 256), losses := [] }

theorem u28036 : Upper (D 7) (R 7) [96,160,3,66,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28036 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28037 : Route 9 := (fun mask => (mask,id))

def c28037 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28037 : Upper (D 7) (R 7) [96,160,3,66,260,16] 13 := by
  apply FastRouting.sound _ _ [96,160,3,66,260,16] 13 (by decide) (choices 1) [1,8,128] r28037 c28037
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10400
  · exact u10401
  · exact u10402

def b28038 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 74 276 160 89 153 281), lower := (rows 97 162 7 74 276 160 64 128 256), losses := [] }

theorem u28038 : Upper (D 7) (R 7) [96,160,3,66,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28038 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28039 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 74 280 33 212 148 404), lower := (rows 97 162 7 74 280 33 64 128 256), losses := [] }

theorem u28039 : Upper (D 7) (R 7) [96,160,3,66,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28040 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 162 7 74 280 36 209 145 401), lower := (rows 97 162 7 74 280 36 64 128 256), losses := [] }

theorem u28040 : Upper (D 7) (R 7) [96,160,3,66,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28040 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28041 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 2, region := 200, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 162 7 74 280 48 197 133 389), lower := (rows 97 162 7 74 280 48 64 128 256), losses := [] }

theorem u28041 : Upper (D 7) (R 7) [96,160,3,66,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28042 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 74 280 160 85 149 277), lower := (rows 97 162 7 74 280 160 64 128 256), losses := [] }

theorem u28042 : Upper (D 7) (R 7) [96,160,3,66,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28043 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 74 400 33 92 156 284), lower := (rows 97 162 7 74 400 33 64 128 256), losses := [] }

theorem u28043 : Upper (D 7) (R 7) [96,160,3,66,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28044 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 3, region := 37, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 97 162 7 74 400 36 89 153 281), lower := (rows 97 162 7 74 400 36 64 128 256), losses := [] }

theorem u28044 : Upper (D 7) (R 7) [96,160,3,66,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28044 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28045 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 74 400 40 85 149 277), lower := (rows 97 162 7 74 400 40 64 128 256), losses := [] }

theorem u28045 : Upper (D 7) (R 7) [96,160,3,66,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28045 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28046 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 400 48 77 141 269), lower := (rows 97 162 7 74 400 48 64 128 256), losses := [] }

theorem u28046 : Upper (D 7) (R 7) [96,160,3,66,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28046 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28047 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 76 152 33 338 402 274), lower := (rows 97 162 7 76 152 33 64 128 256), losses := [] }

theorem u28047 : Upper (D 7) (R 7) [96,160,3,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28048 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 76 152 34 337 401 273), lower := (rows 97 162 7 76 152 34 64 128 256), losses := [] }

theorem u28048 : Upper (D 7) (R 7) [96,160,3,68,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28049 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 76 152 48 323 387 259), lower := (rows 97 162 7 76 152 48 64 128 256), losses := [] }

theorem u28049 : Upper (D 7) (R 7) [96,160,3,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28049 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28050 : Route 9 := (fun mask => (mask,id))

def c28050 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28050 : Upper (D 7) (R 7) [96,160,3,68,136,256] 13 := by
  apply FastRouting.sound _ _ [96,160,3,68,136,256] 13 (by decide) (choices 1) [1,2,16] r28050 c28050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10403
  · exact u10404
  · exact u10405

def b28051 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 76 273 34 216 152 408), lower := (rows 97 162 7 76 273 34 64 128 256), losses := [] }

theorem u28051 : Upper (D 7) (R 7) [96,160,3,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28052 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 76 273 40 210 146 402), lower := (rows 97 162 7 76 273 40 64 128 256), losses := [] }

theorem u28052 : Upper (D 7) (R 7) [96,160,3,68,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28052 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28053 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 200, targets := 1 }], pairs := [(3,0),(3,5),(4,5)], upper := (rows 97 162 7 76 273 48 202 138 394), lower := (rows 97 162 7 76 273 48 64 128 256), losses := [] }

theorem u28053 : Upper (D 7) (R 7) [96,160,3,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28053 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28054 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 76 273 160 90 154 282), lower := (rows 97 162 7 76 273 160 64 128 256), losses := [] }

theorem u28054 : Upper (D 7) (R 7) [96,160,3,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28055 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 76 274 33 216 152 408), lower := (rows 97 162 7 76 274 33 64 128 256), losses := [] }

theorem u28055 : Upper (D 7) (R 7) [96,160,3,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28056 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 76 274 40 209 145 401), lower := (rows 97 162 7 76 274 40 64 128 256), losses := [] }

theorem u28056 : Upper (D 7) (R 7) [96,160,3,68,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28056 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28057 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 2, region := 200, targets := 2 }], pairs := [(3,1),(3,5),(4,5)], upper := (rows 97 162 7 76 274 48 201 137 393), lower := (rows 97 162 7 76 274 48 64 128 256), losses := [] }

theorem u28057 : Upper (D 7) (R 7) [96,160,3,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28058 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 76 274 160 89 153 281), lower := (rows 97 162 7 76 274 160 64 128 256), losses := [] }

theorem u28058 : Upper (D 7) (R 7) [96,160,3,68,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28059 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 76 280 33 210 146 402), lower := (rows 97 162 7 76 280 33 64 128 256), losses := [] }

theorem u28059 : Upper (D 7) (R 7) [96,160,3,68,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28060 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 76 280 34 209 145 401), lower := (rows 97 162 7 76 280 34 64 128 256), losses := [] }

theorem u28060 : Upper (D 7) (R 7) [96,160,3,68,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28061 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 134, targets := 64 },{ cop := 2, region := 200, targets := 32 }], pairs := [(1,6),(2,6),(3,5)], upper := (rows 97 162 7 76 280 48 195 131 387), lower := (rows 97 162 7 76 280 48 64 128 256), losses := [] }

theorem u28061 : Upper (D 7) (R 7) [96,160,3,68,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28061 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28062 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 76 280 160 83 147 275), lower := (rows 97 162 7 76 280 160 64 128 256), losses := [] }

theorem u28062 : Upper (D 7) (R 7) [96,160,3,68,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28062 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28063 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 76 400 33 90 154 282), lower := (rows 97 162 7 76 400 33 64 128 256), losses := [] }

theorem u28063 : Upper (D 7) (R 7) [96,160,3,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28064 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 76 400 34 89 153 281), lower := (rows 97 162 7 76 400 34 64 128 256), losses := [] }

theorem u28064 : Upper (D 7) (R 7) [96,160,3,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28065 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 76 400 40 83 147 275), lower := (rows 97 162 7 76 400 40 64 128 256), losses := [] }

theorem u28065 : Upper (D 7) (R 7) [96,160,3,68,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28065 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28066 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 76 400 48 75 139 267), lower := (rows 97 162 7 76 400 48 64 128 256), losses := [] }

theorem u28066 : Upper (D 7) (R 7) [96,160,3,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28067 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 88 273 34 204 140 396), lower := (rows 97 162 7 88 273 34 64 128 256), losses := [] }

theorem u28067 : Upper (D 7) (R 7) [96,160,3,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28068 : Route 9 := (fun mask => (mask,id))

def c28068 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28068 : Upper (D 7) (R 7) [96,160,3,80,257,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,257,4] 13 (by decide) (choices 1) [2,8,128] r28068 c28068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10406
  · exact u10407
  · exact u10408

def b28069 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 88 273 40 198 134 390), lower := (rows 97 162 7 88 273 40 64 128 256), losses := [] }

theorem u28069 : Upper (D 7) (R 7) [96,160,3,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28069 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28070 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 88 273 160 78 142 270), lower := (rows 97 162 7 88 273 160 64 128 256), losses := [] }

theorem u28070 : Upper (D 7) (R 7) [96,160,3,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28071 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 88 274 33 204 140 396), lower := (rows 97 162 7 88 274 33 64 128 256), losses := [] }

theorem u28071 : Upper (D 7) (R 7) [96,160,3,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28071 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r28072 : Route 9 := (fun mask => (mask,id))

def c28072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u28072 : Upper (D 7) (R 7) [96,160,3,80,258,4] 13 := by
  apply FastRouting.sound _ _ [96,160,3,80,258,4] 13 (by decide) (choices 1) [1,8,128] r28072 c28072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u10409
  · exact u10410
  · exact u10411

def b28073 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 88 274 40 197 133 389), lower := (rows 97 162 7 88 274 40 64 128 256), losses := [] }

theorem u28073 : Upper (D 7) (R 7) [96,160,3,80,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28073 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28074 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 88 274 160 77 141 269), lower := (rows 97 162 7 88 274 160 64 128 256), losses := [] }

theorem u28074 : Upper (D 7) (R 7) [96,160,3,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28075 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 88 276 33 202 138 394), lower := (rows 97 162 7 88 276 33 64 128 256), losses := [] }

theorem u28075 : Upper (D 7) (R 7) [96,160,3,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28076 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 472, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 97 162 7 88 276 34 201 137 393), lower := (rows 97 162 7 88 276 34 64 128 256), losses := [] }

theorem u28076 : Upper (D 7) (R 7) [96,160,3,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28077 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6),(4,6)], upper := (rows 97 162 7 88 276 40 195 131 387), lower := (rows 97 162 7 88 276 40 64 128 256), losses := [] }

theorem u28077 : Upper (D 7) (R 7) [96,160,3,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28078 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 97 162 7 88 276 160 75 139 267), lower := (rows 97 162 7 88 276 160 64 128 256), losses := [] }

theorem u28078 : Upper (D 7) (R 7) [96,160,3,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28079 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 472, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5)], upper := (rows 97 162 7 88 400 33 78 142 270), lower := (rows 97 162 7 88 400 33 64 128 256), losses := [] }

theorem u28079 : Upper (D 7) (R 7) [96,160,3,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u28079
end Delivery.IrregularNine14.P07
