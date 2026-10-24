import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0007

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5940 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 4, region := 259, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 259 14 200 112 160 68 145 273), lower := (rows 35 259 14 200 112 160 68 128 256), losses := [] }

theorem u5940 : Upper (D 7) (R 7) [34,257,10,192,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5940 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5941 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 88, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 35 259 14 200 112 160 80 133 261), lower := (rows 35 259 14 200 112 160 80 128 256), losses := [] }

theorem u5941 : Upper (D 7) (R 7) [34,257,10,192,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5941 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5942 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 92, targets := 160 }], pairs := [(2,5),(2,7),(3,5)], upper := (rows 35 259 28 73 82 160 68 160 416), lower := (rows 35 259 28 73 82 160 68 128 256), losses := [] }

theorem u5942 : Upper (D 7) (R 7) [34,257,24,65,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5942 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5943 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 92, targets := 128 },{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 259 28 73 82 160 96 132 388), lower := (rows 35 259 28 73 82 160 96 128 256), losses := [] }

theorem u5943 : Upper (D 7) (R 7) [34,257,24,65,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5943 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5944 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 35 259 28 73 82 160 192 164 292), lower := (rows 35 259 28 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 236 236 140 268), good := (rows 114 274 508 508 114 224 224 224 256) }] }

theorem u5944 : Upper (D 7) (R 7) [34,257,24,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5944 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5945 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 73 112 160 66 132 388), lower := (rows 35 259 28 73 112 160 66 128 256), losses := [] }

theorem u5945 : Upper (D 7) (R 7) [34,257,24,65,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5945 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5946 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 28 73 112 160 68 130 386), lower := (rows 35 259 28 73 112 160 68 128 256), losses := [] }

theorem u5946 : Upper (D 7) (R 7) [34,257,24,65,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5946 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5947 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 28 73 112 160 192 134 262), lower := (rows 35 259 28 73 112 160 192 128 256), losses := [] }

theorem u5947 : Upper (D 7) (R 7) [34,257,24,65,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5947 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5948 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 259 28 73 146 96 68 160 416), lower := (rows 35 259 28 73 146 96 68 128 256), losses := [] }

theorem u5948 : Upper (D 7) (R 7) [34,257,24,65,130,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5948 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5949 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 96 }], pairs := [(1,5),(1,6),(2,5),(2,6)], upper := (rows 35 259 28 73 146 96 96 132 388), lower := (rows 35 259 28 73 146 96 96 128 256), losses := [] }

theorem u5949 : Upper (D 7) (R 7) [34,257,24,65,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5949 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5950 : Route 9 := (fun mask => (mask,id))

def c5950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5950 : Upper (D 7) (R 7) [34,257,24,65,130,64,128] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,130,64,128] 13 (by decide) (choices 1) [4,32] r5950 c5950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u442
  · exact u443

def r5951 : Route 9 := (fun mask => (mask,id))

def c5951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5951 : Upper (D 7) (R 7) [34,257,24,65,130,128,4] 13 := by
  apply FastRouting.sound _ _ [34,257,24,65,130,128,4] 13 (by decide) (choices 1) [32,64] r5951 c5951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u444
  · exact u445

def b5952 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 259 28 73 146 160 96 196 324), lower := (rows 35 259 28 73 146 160 96 128 256), losses := [] }

theorem u5952 : Upper (D 7) (R 7) [34,257,24,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5952 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5953 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 73 176 96 66 132 388), lower := (rows 35 259 28 73 176 96 66 128 256), losses := [] }

theorem u5953 : Upper (D 7) (R 7) [34,257,24,65,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5953 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5954 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 28 73 176 96 68 130 386), lower := (rows 35 259 28 73 176 96 68 128 256), losses := [] }

theorem u5954 : Upper (D 7) (R 7) [34,257,24,65,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5954 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5955 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 48, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 73 176 96 192 134 262), lower := (rows 35 259 28 73 176 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 208 252 208 128 256), good := (rows 34 258 124 124 240 112 240 240 256) },{ target := 1, region := (rows 1 0 12 8 208 252 208 128 256), good := (rows 33 257 124 125 240 112 240 240 256) }] }

theorem u5955 : Upper (D 7) (R 7) [34,257,24,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5955 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5956 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 73 208 160 66 164 292), lower := (rows 35 259 28 73 208 160 66 128 256), losses := [] }

theorem u5956 : Upper (D 7) (R 7) [34,257,24,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5956 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5957 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 259, targets := 128 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 28 73 208 160 68 162 290), lower := (rows 35 259 28 73 208 160 68 128 256), losses := [] }

theorem u5957 : Upper (D 7) (R 7) [34,257,24,65,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5957 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5958 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 259 28 73 208 160 96 134 262), lower := (rows 35 259 28 73 208 160 96 128 256), losses := [] }

theorem u5958 : Upper (D 7) (R 7) [34,257,24,65,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5958 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5959 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 74 112 160 65 132 388), lower := (rows 35 259 28 74 112 160 65 128 256), losses := [] }

theorem u5959 : Upper (D 7) (R 7) [34,257,24,66,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5959 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5960 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 92, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 259 28 74 112 160 68 129 385), lower := (rows 35 259 28 74 112 160 68 128 256), losses := [] }

theorem u5960 : Upper (D 7) (R 7) [34,257,24,66,96,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5960 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5961 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 259 28 74 112 160 192 133 261), lower := (rows 35 259 28 74 112 160 192 128 256), losses := [] }

theorem u5961 : Upper (D 7) (R 7) [34,257,24,66,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5962 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 74 176 96 65 132 388), lower := (rows 35 259 28 74 176 96 65 128 256), losses := [] }

theorem u5962 : Upper (D 7) (R 7) [34,257,24,66,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5963 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 403, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 28 74 176 96 68 129 385), lower := (rows 35 259 28 74 176 96 68 128 256), losses := [] }

theorem u5963 : Upper (D 7) (R 7) [34,257,24,66,160,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5963 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5964 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7),(2,0),(4,0),(4,1)], upper := (rows 35 259 28 74 176 96 192 133 261), lower := (rows 35 259 28 74 176 96 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 208 252 208 128 256), good := (rows 34 258 124 126 240 112 240 240 256) }] }

theorem u5964 : Upper (D 7) (R 7) [34,257,24,66,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5965 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 28 74 208 160 65 164 292), lower := (rows 35 259 28 74 208 160 65 128 256), losses := [] }

theorem u5965 : Upper (D 7) (R 7) [34,257,24,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5965 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5966 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 259, targets := 128 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 28 74 208 160 68 161 289), lower := (rows 35 259 28 74 208 160 68 128 256), losses := [] }

theorem u5966 : Upper (D 7) (R 7) [34,257,24,66,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5966 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5967 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 419, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 259 28 74 208 160 96 133 261), lower := (rows 35 259 28 74 208 160 96 128 256), losses := [] }

theorem u5967 : Upper (D 7) (R 7) [34,257,24,66,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5968 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 44 73 82 160 68 144 400), lower := (rows 35 259 44 73 82 160 68 128 256), losses := [] }

theorem u5968 : Upper (D 7) (R 7) [34,257,40,65,66,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5968 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5969 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 35 259 44 73 82 160 80 132 388), lower := (rows 35 259 44 73 82 160 80 128 256), losses := [] }

theorem u5969 : Upper (D 7) (R 7) [34,257,40,65,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5969 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5970 : PairBound 9 := { available := 20, camps := [], pairs := [(2,0),(2,1),(3,1),(4,0)], upper := (rows 35 259 44 73 82 160 192 148 276), lower := (rows 35 259 44 73 82 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 236 236 136 264), good := (rows 114 274 492 508 114 224 224 224 256) },{ target := 1, region := (rows 1 0 13 9 16 224 224 128 256), good := (rows 109 269 108 109 112 224 224 224 256) }] }

theorem u5970 : Upper (D 7) (R 7) [34,257,40,65,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5971 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 73 84 160 66 144 400), lower := (rows 35 259 44 73 84 160 66 128 256), losses := [] }

theorem u5971 : Upper (D 7) (R 7) [34,257,40,65,68,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5971 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5972 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 92, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 44 73 84 160 80 130 386), lower := (rows 35 259 44 73 84 160 80 128 256), losses := [] }

theorem u5972 : Upper (D 7) (R 7) [34,257,40,65,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5972 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5973 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 35 259 44 73 84 160 192 146 274), lower := (rows 35 259 44 73 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 28 224 224 128 256), good := (rows 98 258 124 124 116 224 224 224 256) }] }

theorem u5973 : Upper (D 7) (R 7) [34,257,40,65,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5973 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5974 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 44 73 146 160 68 208 336), lower := (rows 35 259 44 73 146 160 68 128 256), losses := [] }

theorem u5974 : Upper (D 7) (R 7) [34,257,40,65,130,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5974 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5975 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 164, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,0),(2,1)], upper := (rows 35 259 44 73 146 160 80 196 324), lower := (rows 35 259 44 73 146 160 80 128 256), losses := [] }

theorem u5975 : Upper (D 7) (R 7) [34,257,40,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5975 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5976 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 73 148 160 66 208 336), lower := (rows 35 259 44 73 148 160 66 128 256), losses := [] }

theorem u5976 : Upper (D 7) (R 7) [34,257,40,65,132,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5977 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 258, targets := 32 },{ cop := 3, region := 258, targets := 128 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 259 44 73 148 160 80 194 322), lower := (rows 35 259 44 73 148 160 80 128 256), losses := [{ target := 5, region := (rows 1 10 4 8 20 0 84 140 268), good := (rows 3 259 478 459 468 128 80 128 256) }] }

theorem u5977 : Upper (D 7) (R 7) [34,257,40,65,132,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5977 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5978 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 259 44 73 208 48 66 132 388), lower := (rows 35 259 44 73 208 48 66 128 256), losses := [] }

theorem u5978 : Upper (D 7) (R 7) [34,257,40,65,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5978 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5979 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 259 44 73 208 48 68 130 386), lower := (rows 35 259 44 73 208 48 68 128 256), losses := [] }

theorem u5979 : Upper (D 7) (R 7) [34,257,40,65,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5979 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5980 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 44 73 208 48 192 134 262), lower := (rows 35 259 44 73 208 48 192 128 256), losses := [] }

theorem u5980 : Upper (D 7) (R 7) [34,257,40,65,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5980 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5981 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 73 208 160 66 148 276), lower := (rows 35 259 44 73 208 160 66 128 256), losses := [] }

theorem u5981 : Upper (D 7) (R 7) [34,257,40,65,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5982 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 259 44 73 208 160 68 146 274), lower := (rows 35 259 44 73 208 160 68 128 256), losses := [] }

theorem u5982 : Upper (D 7) (R 7) [34,257,40,65,192,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5982 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5983 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 35 259 44 73 208 160 80 134 262), lower := (rows 35 259 44 73 208 160 80 128 256), losses := [] }

theorem u5983 : Upper (D 7) (R 7) [34,257,40,65,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5983 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5984 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 92, targets := 128 }], pairs := [(2,7),(3,7),(4,7)], upper := (rows 35 259 44 74 81 160 68 144 400), lower := (rows 35 259 44 74 81 160 68 128 256), losses := [] }

theorem u5984 : Upper (D 7) (R 7) [34,257,40,66,65,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5984 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5985 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 35 259 44 74 81 160 80 132 388), lower := (rows 35 259 44 74 81 160 80 128 256), losses := [] }

theorem u5985 : Upper (D 7) (R 7) [34,257,40,66,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5985 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5986 : PairBound 9 := { available := 20, camps := [], pairs := [(2,0),(2,1),(3,0),(4,1)], upper := (rows 35 259 44 74 81 160 192 148 276), lower := (rows 35 259 44 74 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 29 9 16 240 240 144 272), good := (rows 110 270 108 110 508 224 224 224 256) },{ target := 1, region := (rows 1 0 12 8 17 224 224 128 256), good := (rows 113 273 108 108 113 224 224 224 256) }] }

theorem u5986 : Upper (D 7) (R 7) [34,257,40,66,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5987 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 74 84 160 65 144 400), lower := (rows 35 259 44 74 84 160 65 128 256), losses := [] }

theorem u5987 : Upper (D 7) (R 7) [34,257,40,66,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5988 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 80, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 259 44 74 84 160 80 129 385), lower := (rows 35 259 44 74 84 160 80 128 256), losses := [] }

theorem u5988 : Upper (D 7) (R 7) [34,257,40,66,68,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5988 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5989 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(2,0),(3,0)], upper := (rows 35 259 44 74 84 160 192 145 273), lower := (rows 35 259 44 74 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 13 9 29 224 224 128 256), good := (rows 126 286 124 126 116 224 224 224 256) }] }

theorem u5989 : Upper (D 7) (R 7) [34,257,40,66,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5990 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 259 44 74 145 48 68 192 448), lower := (rows 35 259 44 74 145 48 68 128 256), losses := [] }

theorem u5990 : Upper (D 7) (R 7) [34,257,40,66,129,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5990 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5991 : Route 9 := (fun mask => (mask,id))

def c5991 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5991 : Upper (D 7) (R 7) [34,257,40,66,129,16,128] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,129,16,128] 13 (by decide) (choices 1) [4,64] r5991 c5991
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u446
  · exact u447

def b5992 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 1 },{ cop := 0, region := 76, targets := 128 }], pairs := [(2,0),(2,7),(3,0)], upper := (rows 35 259 44 74 145 160 68 208 336), lower := (rows 35 259 44 74 145 160 68 128 256), losses := [] }

theorem u5992 : Upper (D 7) (R 7) [34,257,40,66,129,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5992 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5993 : Route 9 := (fun mask => (mask,id))

def c5993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5993 : Upper (D 7) (R 7) [34,257,40,66,129,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,129,128,16] 13 (by decide) (choices 1) [4,64] r5993 c5993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u448
  · exact u449

def b5994 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 74 148 160 65 208 336), lower := (rows 35 259 44 74 148 160 65 128 256), losses := [] }

theorem u5994 : Upper (D 7) (R 7) [34,257,40,66,132,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r5995 : Route 9 := (fun mask => (mask,id))

def c5995 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u5995 : Upper (D 7) (R 7) [34,257,40,66,132,128,16] 13 := by
  apply FastRouting.sound _ _ [34,257,40,66,132,128,16] 13 (by decide) (choices 1) [1,64] r5995 c5995
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u450
  · exact u451

def b5996 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 259 44 74 208 48 65 132 388), lower := (rows 35 259 44 74 208 48 65 128 256), losses := [] }

theorem u5996 : Upper (D 7) (R 7) [34,257,40,66,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5996 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5997 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 76, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 259 44 74 208 48 68 129 385), lower := (rows 35 259 44 74 208 48 68 128 256), losses := [] }

theorem u5997 : Upper (D 7) (R 7) [34,257,40,66,192,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5997 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5998 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 44 74 208 48 192 133 261), lower := (rows 35 259 44 74 208 48 192 128 256), losses := [] }

theorem u5998 : Upper (D 7) (R 7) [34,257,40,66,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5998 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5999 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 180, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 35 259 44 74 208 160 65 148 276), lower := (rows 35 259 44 74 208 160 65 128 256), losses := [] }

theorem u5999 : Upper (D 7) (R 7) [34,257,40,66,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5999
end Delivery.IrregularNine14.P07
