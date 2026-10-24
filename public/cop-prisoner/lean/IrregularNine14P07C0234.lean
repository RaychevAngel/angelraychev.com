import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0037

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b14040 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 88 34 464 400 400), lower := (rows 7 98 133 41 88 34 64 128 256), losses := [] }

theorem u14040 : Upper (D 7) (R 7) [6,96,129,33,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14040 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14041 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 88 48 450 386 386), lower := (rows 7 98 133 41 88 48 64 128 256), losses := [] }

theorem u14041 : Upper (D 7) (R 7) [6,96,129,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14041 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14042 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 7 98 133 41 88 160 338 402 274), lower := (rows 7 98 133 41 88 160 64 128 256), losses := [] }

theorem u14042 : Upper (D 7) (R 7) [6,96,129,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14043 : Route 9 := (fun mask => (mask,id))

def c14043 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14043 : Upper (D 7) (R 7) [6,96,129,33,72,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,72,256] 13 (by decide) (choices 1) [2,16,128] r14043 c14043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2229
  · exact u2230
  · exact u2231

def b14044 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 152 34 336 464 336), lower := (rows 7 98 133 41 152 34 64 128 256), losses := [] }

theorem u14044 : Upper (D 7) (R 7) [6,96,129,33,136,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14044 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14045 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 98 133 41 152 48 322 450 322), lower := (rows 7 98 133 41 152 48 64 128 256), losses := [] }

theorem u14045 : Upper (D 7) (R 7) [6,96,129,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14045 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14046 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 41 152 96 338 402 274), lower := (rows 7 98 133 41 152 96 64 128 256), losses := [] }

theorem u14046 : Upper (D 7) (R 7) [6,96,129,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14047 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 210, targets := 1 },{ cop := 4, region := 354, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 41 152 288 82 210 338), lower := (rows 7 98 133 41 152 288 64 128 256), losses := [] }

theorem u14047 : Upper (D 7) (R 7) [6,96,129,33,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14047 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14048 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 208 34 344 408 280), lower := (rows 7 98 133 41 208 34 64 128 256), losses := [] }

theorem u14048 : Upper (D 7) (R 7) [6,96,129,33,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14049 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 133 41 208 40 338 402 274), lower := (rows 7 98 133 41 208 40 64 128 256), losses := [] }

theorem u14049 : Upper (D 7) (R 7) [6,96,129,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14049 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14050 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 208 48 330 394 266), lower := (rows 7 98 133 41 208 48 64 128 256), losses := [] }

theorem u14050 : Upper (D 7) (R 7) [6,96,129,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14050 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14051 : Route 9 := (fun mask => (mask,id))

def c14051 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14051 : Upper (D 7) (R 7) [6,96,129,33,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,33,192,256] 13 (by decide) (choices 1) [2,8,16] r14051 c14051
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2232
  · exact u2233
  · exact u2234

def b14052 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 133 41 274 40 208 208 464), lower := (rows 7 98 133 41 274 40 64 128 256), losses := [] }

theorem u14052 : Upper (D 7) (R 7) [6,96,129,33,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14052 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14053 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 98 133 41 274 48 200 200 456), lower := (rows 7 98 133 41 274 48 64 128 256), losses := [] }

theorem u14053 : Upper (D 7) (R 7) [6,96,129,33,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14053 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14054 : PairBound 9 := { available := 152, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 41 274 96 216 152 408), lower := (rows 7 98 133 41 274 96 64 128 256), losses := [] }

theorem u14054 : Upper (D 7) (R 7) [6,96,129,33,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14055 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 7 98 133 41 274 160 88 216 344), lower := (rows 7 98 133 41 274 160 64 128 256), losses := [] }

theorem u14055 : Upper (D 7) (R 7) [6,96,129,33,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14056 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 280 34 208 208 464), lower := (rows 7 98 133 41 280 34 64 128 256), losses := [] }

theorem u14056 : Upper (D 7) (R 7) [6,96,129,33,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14056 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14057 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 133, targets := 32 },{ cop := 3, region := 194, targets := 1 }], pairs := [(0,5),(1,0),(2,5)], upper := (rows 7 98 133 41 280 48 194 194 450), lower := (rows 7 98 133 41 280 48 64 128 256), losses := [] }

theorem u14057 : Upper (D 7) (R 7) [6,96,129,33,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14057 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14058 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 41 280 96 210 146 402), lower := (rows 7 98 133 41 280 96 64 128 256), losses := [] }

theorem u14058 : Upper (D 7) (R 7) [6,96,129,33,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14058 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14059 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 7 98 133 41 280 160 82 210 338), lower := (rows 7 98 133 41 280 160 64 128 256), losses := [] }

theorem u14059 : Upper (D 7) (R 7) [6,96,129,33,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14060 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 336 34 216 152 408), lower := (rows 7 98 133 41 336 34 64 128 256), losses := [] }

theorem u14060 : Upper (D 7) (R 7) [6,96,129,33,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14060 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14061 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 133 41 336 40 210 146 402), lower := (rows 7 98 133 41 336 40 64 128 256), losses := [] }

theorem u14061 : Upper (D 7) (R 7) [6,96,129,33,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14061 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14062 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 133 41 336 48 202 138 394), lower := (rows 7 98 133 41 336 48 64 128 256), losses := [] }

theorem u14062 : Upper (D 7) (R 7) [6,96,129,33,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14062 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14063 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 40, targets := 66 },{ cop := 3, region := 338, targets := 1 }], pairs := [(1,0),(3,1),(3,6),(4,0)], upper := (rows 7 98 133 41 336 160 90 154 282), lower := (rows 7 98 133 41 336 160 64 128 256), losses := [] }

theorem u14063 : Upper (D 7) (R 7) [6,96,129,33,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14064 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 98 133 41 400 34 88 216 344), lower := (rows 7 98 133 41 400 34 64 128 256), losses := [] }

theorem u14064 : Upper (D 7) (R 7) [6,96,129,33,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14064 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14065 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 40, targets := 194 }], pairs := [(3,1),(3,6),(3,7)], upper := (rows 7 98 133 41 400 40 82 210 338), lower := (rows 7 98 133 41 400 40 64 128 256), losses := [] }

theorem u14065 : Upper (D 7) (R 7) [6,96,129,33,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14065 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14066 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 466, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 7 98 133 41 400 48 74 202 330), lower := (rows 7 98 133 41 400 48 64 128 256), losses := [] }

theorem u14066 : Upper (D 7) (R 7) [6,96,129,33,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14066 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14067 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 41 400 96 90 154 282), lower := (rows 7 98 133 41 400 96 64 128 256), losses := [] }

theorem u14067 : Upper (D 7) (R 7) [6,96,129,33,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14067 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14068 : PairBound 9 := { available := 266, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 7 98 133 56 208 33 330 394 266), lower := (rows 7 98 133 56 208 33 64 128 256), losses := [] }

theorem u14068 : Upper (D 7) (R 7) [6,96,129,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14069 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 56 208 34 329 393 265), lower := (rows 7 98 133 56 208 34 64 128 256), losses := [] }

theorem u14069 : Upper (D 7) (R 7) [6,96,129,48,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14070 : PairBound 9 := { available := 259, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 56 208 40 323 387 259), lower := (rows 7 98 133 56 208 40 64 128 256), losses := [] }

theorem u14070 : Upper (D 7) (R 7) [6,96,129,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14070 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14071 : Route 9 := (fun mask => (mask,id))

def c14071 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14071 : Upper (D 7) (R 7) [6,96,129,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,192,256] 13 (by decide) (choices 1) [1,2,8] r14071 c14071
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2235
  · exact u2236
  · exact u2237

def b14072 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(3,6)], upper := (rows 7 98 133 56 273 34 200 200 456), lower := (rows 7 98 133 56 273 34 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 24 16 35 0 128 256), good := (rows 39 34 165 56 313 34 0 128 256) }] }

theorem u14072 : Upper (D 7) (R 7) [6,96,129,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14073 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 405, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 7 98 133 56 273 40 194 194 450), lower := (rows 7 98 133 56 273 40 64 128 256), losses := [] }

theorem u14073 : Upper (D 7) (R 7) [6,96,129,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14073 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14074 : PairBound 9 := { available := 138, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 56 273 96 202 138 394), lower := (rows 7 98 133 56 273 96 64 128 256), losses := [] }

theorem u14074 : Upper (D 7) (R 7) [6,96,129,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14074 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14075 : Route 9 := (fun mask => (mask,id))

def c14075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14075 : Upper (D 7) (R 7) [6,96,129,48,257,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,257,128] 13 (by decide) (choices 1) [2,8] r14075 c14075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2238
  · exact u2239

def r14076 : Route 9 := (fun mask => (mask,id))

def c14076 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14076 : Upper (D 7) (R 7) [6,96,129,48,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,258,1] 13 (by decide) (choices 1) [8,128] r14076 c14076
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2240
  · exact u2241

def b14077 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 98 133 56 274 40 193 193 449), lower := (rows 7 98 133 56 274 40 64 128 256), losses := [] }

theorem u14077 : Upper (D 7) (R 7) [6,96,129,48,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14077 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14078 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 56 274 96 201 137 393), lower := (rows 7 98 133 56 274 96 64 128 256), losses := [] }

theorem u14078 : Upper (D 7) (R 7) [6,96,129,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14079 : Route 9 := (fun mask => (mask,id))

def c14079 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14079 : Upper (D 7) (R 7) [6,96,129,48,258,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,258,128] 13 (by decide) (choices 1) [1,8] r14079 c14079
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2242
  · exact u2243

def b14080 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 1, region := 133, targets := 32 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 98 133 56 280 33 194 194 450), lower := (rows 7 98 133 56 280 33 64 128 256), losses := [] }

theorem u14080 : Upper (D 7) (R 7) [6,96,129,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14081 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(2,1),(2,5)], upper := (rows 7 98 133 56 280 34 193 193 449), lower := (rows 7 98 133 56 280 34 64 128 256), losses := [] }

theorem u14081 : Upper (D 7) (R 7) [6,96,129,48,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14082 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 56 280 96 195 131 387), lower := (rows 7 98 133 56 280 96 64 128 256), losses := [] }

theorem u14082 : Upper (D 7) (R 7) [6,96,129,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14082 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14083 : Route 9 := (fun mask => (mask,id))

def c14083 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14083 : Upper (D 7) (R 7) [6,96,129,48,264,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,264,128] 13 (by decide) (choices 1) [1,2] r14083 c14083
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2244
  · exact u2245

def r14084 : Route 9 := (fun mask => (mask,id))

def c14084 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u14084 : Upper (D 7) (R 7) [6,96,129,48,320,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320,1] 13 (by decide) (choices 1) [2,8,128] r14084 c14084
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2246
  · exact u2247
  · exact u2248

def b14085 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 98 133 56 336 34 201 137 393), lower := (rows 7 98 133 56 336 34 64 128 256), losses := [] }

theorem u14085 : Upper (D 7) (R 7) [6,96,129,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14085 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14086 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 42, targets := 129 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 56 336 40 195 131 387), lower := (rows 7 98 133 56 336 40 64 128 256), losses := [] }

theorem u14086 : Upper (D 7) (R 7) [6,96,129,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14086 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14087 : Route 9 := (fun mask => (mask,id))

def c14087 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14087 : Upper (D 7) (R 7) [6,96,129,48,320,128] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,320,128] 13 (by decide) (choices 1) [1,2,8] r14087 c14087
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2249
  · exact u2250
  · exact u2251

def b14088 : PairBound 9 := { available := 74, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 7 98 133 56 400 33 74 202 330), lower := (rows 7 98 133 56 400 33 64 128 256), losses := [] }

theorem u14088 : Upper (D 7) (R 7) [6,96,129,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14089 : Route 9 := (fun mask => (mask,id))

def c14089 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14089 : Upper (D 7) (R 7) [6,96,129,48,384,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,48,384,2] 13 (by decide) (choices 1) [1,8] r14089 c14089
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2252
  · exact u2253

def b14090 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 98 133 56 400 40 67 195 323), lower := (rows 7 98 133 56 400 40 64 128 256), losses := [] }

theorem u14090 : Upper (D 7) (R 7) [6,96,129,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14090 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14091 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 56 400 96 75 139 267), lower := (rows 7 98 133 56 400 96 64 128 256), losses := [] }

theorem u14091 : Upper (D 7) (R 7) [6,96,129,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14091 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14092 : Route 9 := (fun mask => (mask,id))

def c14092 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14092 : Upper (D 7) (R 7) [6,96,129,144,257,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,257,2] 13 (by decide) (choices 1) [8,32] r14092 c14092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2254
  · exact u2255

def b14093 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 7 98 133 152 273 40 98 226 354), lower := (rows 7 98 133 152 273 40 64 128 256), losses := [] }

theorem u14093 : Upper (D 7) (R 7) [6,96,129,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14093 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14094 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 152 273 96 106 170 298), lower := (rows 7 98 133 152 273 96 64 128 256), losses := [] }

theorem u14094 : Upper (D 7) (R 7) [6,96,129,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r14095 : Route 9 := (fun mask => (mask,id))

def c14095 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14095 : Upper (D 7) (R 7) [6,96,129,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,258,1] 13 (by decide) (choices 1) [8,32] r14095 c14095
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2256
  · exact u2257

theorem m14096_1 : Upper (D 7) (R 7) [6,96,129,144,258,8,1] 13 :=
  permutation_upper _ _ _ [6,96,129,144,258,1,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2256

def r14096 : Route 9 := (fun mask => (mask,id))

def c14096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14096 : Upper (D 7) (R 7) [6,96,129,144,258,8] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,258,8] 13 (by decide) (choices 1) [1,32] r14096 c14096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14096_1
  · exact u2258

def b14097 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 7 98 133 152 274 96 105 169 297), lower := (rows 7 98 133 152 274 96 64 128 256), losses := [] }

theorem u14097 : Upper (D 7) (R 7) [6,96,129,144,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14098 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 98 133 152 280 33 98 226 354), lower := (rows 7 98 133 152 280 33 64 128 256), losses := [] }

theorem u14098 : Upper (D 7) (R 7) [6,96,129,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m14099_1 : Upper (D 7) (R 7) [6,96,129,144,264,2,1] 13 :=
  permutation_upper _ _ _ [6,96,129,144,264,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2259

def r14099 : Route 9 := (fun mask => (mask,id))

def c14099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u14099 : Upper (D 7) (R 7) [6,96,129,144,264,2] 13 := by
  apply FastRouting.sound _ _ [6,96,129,144,264,2] 13 (by decide) (choices 1) [1,32] r14099 c14099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m14099_1
  · exact u2260

#print axioms u14099
end Delivery.IrregularNine14.P07
