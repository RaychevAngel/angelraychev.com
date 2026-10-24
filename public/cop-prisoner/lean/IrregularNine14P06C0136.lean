import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0010

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8160 : PairBound 9 := { available := 65, camps := [{ cop := 6, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 265 22 34 68 193 321), lower := (rows 41 98 148 265 22 34 68 128 256), losses := [] }

theorem u8160 : Upper (D 6) (R 6) [40,96,144,257,6,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8161 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 166, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 148 265 81 36 66 134 262), lower := (rows 41 98 148 265 81 36 66 128 256), losses := [] }

theorem u8161 : Upper (D 6) (R 6) [40,96,144,257,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8162 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 148 265 81 36 68 130 258), lower := (rows 41 98 148 265 81 36 68 128 256), losses := [] }

theorem u8162 : Upper (D 6) (R 6) [40,96,144,257,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8163 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 182, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 148 265 84 34 65 134 262), lower := (rows 41 98 148 265 84 34 65 128 256), losses := [] }

theorem u8163 : Upper (D 6) (R 6) [40,96,144,257,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8164 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 98 148 265 84 34 66 133 261), lower := (rows 41 98 148 265 84 34 66 128 256), losses := [] }

theorem u8164 : Upper (D 6) (R 6) [40,96,144,257,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8165 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 148 265 84 34 68 131 259), lower := (rows 41 98 148 265 84 34 68 128 256), losses := [] }

theorem u8165 : Upper (D 6) (R 6) [40,96,144,257,68,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8166 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 41 98 148 266 81 36 65 134 262), lower := (rows 41 98 148 266 81 36 65 128 256), losses := [] }

theorem u8166 : Upper (D 6) (R 6) [40,96,144,258,65,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8167 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 4, region := 132, targets := 2 }], pairs := [(1,2),(2,1),(4,2)], upper := (rows 41 98 148 266 81 36 66 133 261), lower := (rows 41 98 148 266 81 36 66 128 256), losses := [] }

theorem u8167 : Upper (D 6) (R 6) [40,96,144,258,65,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8168 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 41 98 148 266 81 36 68 131 259), lower := (rows 41 98 148 266 81 36 68 128 256), losses := [] }

theorem u8168 : Upper (D 6) (R 6) [40,96,144,258,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8169 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 196 13 274 48 65 134 262), lower := (rows 41 98 196 13 274 48 65 128 256), losses := [] }

theorem u8169 : Upper (D 6) (R 6) [40,96,192,5,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8169 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8170 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 114, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 196 13 274 48 66 133 261), lower := (rows 41 98 196 13 274 48 66 128 256), losses := [] }

theorem u8170 : Upper (D 6) (R 6) [40,96,192,5,258,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8170 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8171 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 98 196 13 274 48 68 131 259), lower := (rows 41 98 196 13 274 48 68 128 256), losses := [] }

theorem u8171 : Upper (D 6) (R 6) [40,96,192,5,258,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8171 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8172 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 196 25 274 36 65 134 262), lower := (rows 41 98 196 25 274 36 65 128 256), losses := [] }

theorem u8172 : Upper (D 6) (R 6) [40,96,192,17,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8173 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 25 274 36 66 133 261), lower := (rows 41 98 196 25 274 36 66 128 256), losses := [] }

theorem u8173 : Upper (D 6) (R 6) [40,96,192,17,258,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8174 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 25 274 36 68 131 259), lower := (rows 41 98 196 25 274 36 68 128 256), losses := [] }

theorem u8174 : Upper (D 6) (R 6) [40,96,192,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8175 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 196 26 21 288 65 134 262), lower := (rows 41 98 196 26 21 288 65 128 256), losses := [] }

theorem u8175 : Upper (D 6) (R 6) [40,96,192,18,5,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8175 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8176 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 196 26 21 288 66 133 261), lower := (rows 41 98 196 26 21 288 66 128 256), losses := [] }

theorem u8176 : Upper (D 6) (R 6) [40,96,192,18,5,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8176 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8177 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 41 98 196 26 21 288 68 131 259), lower := (rows 41 98 196 26 21 288 68 128 256), losses := [] }

theorem u8177 : Upper (D 6) (R 6) [40,96,192,18,5,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8177 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8178 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 166, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 26 273 36 65 134 262), lower := (rows 41 98 196 26 273 36 65 128 256), losses := [] }

theorem u8178 : Upper (D 6) (R 6) [40,96,192,18,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8179 : PairBound 9 := { available := 5, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 26 273 36 66 133 261), lower := (rows 41 98 196 26 273 36 66 128 256), losses := [] }

theorem u8179 : Upper (D 6) (R 6) [40,96,192,18,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8180 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 281, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 26 273 36 68 131 259), lower := (rows 41 98 196 26 273 36 68 128 256), losses := [] }

theorem u8180 : Upper (D 6) (R 6) [40,96,192,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8181 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 0, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 265 21 36 66 146 274), lower := (rows 41 98 196 265 21 36 66 128 256), losses := [] }

theorem u8181 : Upper (D 6) (R 6) [40,96,192,257,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8182 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 98 196 265 21 36 80 130 258), lower := (rows 41 98 196 265 21 36 80 128 256), losses := [] }

theorem u8182 : Upper (D 6) (R 6) [40,96,192,257,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8182 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8183 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 66, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 196 266 21 36 65 146 274), lower := (rows 41 98 196 266 21 36 65 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 52 64 144 272), good := (rows 40 98 230 266 446 38 64 128 256) }] }

theorem u8183 : Upper (D 6) (R 6) [40,96,192,258,5,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8184 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 66, targets := 5 },{ cop := 7, region := 102, targets := 1 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 266 21 36 66 145 273), lower := (rows 41 98 196 266 21 36 66 128 256), losses := [] }

theorem u8184 : Upper (D 6) (R 6) [40,96,192,258,5,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8185 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 98 196 266 21 36 80 131 259), lower := (rows 41 98 196 266 21 36 80 128 256), losses := [] }

theorem u8185 : Upper (D 6) (R 6) [40,96,192,258,5,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8185 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8186 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 132, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 41 98 196 266 21 48 65 134 262), lower := (rows 41 98 196 266 21 48 65 128 256), losses := [] }

theorem u8186 : Upper (D 6) (R 6) [40,96,192,258,5,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8186 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8187 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 98, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 41 98 196 266 21 48 66 133 261), lower := (rows 41 98 196 266 21 48 66 128 256), losses := [] }

theorem u8187 : Upper (D 6) (R 6) [40,96,192,258,5,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8187 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8188 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 265, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 41 98 196 266 21 48 68 131 259), lower := (rows 41 98 196 266 21 48 68 128 256), losses := [] }

theorem u8188 : Upper (D 6) (R 6) [40,96,192,258,5,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8188 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8189 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 41 98 388 13 84 34 65 146 274), lower := (rows 41 98 388 13 84 34 65 128 256), losses := [] }

theorem u8189 : Upper (D 6) (R 6) [40,96,384,5,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8190 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 41 98 388 13 84 34 66 145 273), lower := (rows 41 98 388 13 84 34 66 128 256), losses := [] }

theorem u8190 : Upper (D 6) (R 6) [40,96,384,5,68,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8191 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 41 98 388 13 84 34 80 131 259), lower := (rows 41 98 388 13 84 34 80 128 256), losses := [] }

theorem u8191 : Upper (D 6) (R 6) [40,96,384,5,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8191 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r8192 : Route 9 := (fun mask => (mask,id))

def c8192 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8192 : Upper (D 6) (R 6) [40,129,257,6,34,64,4] 13 := by
  apply FastRouting.sound _ _ [40,129,257,6,34,64,4] 13 (by decide) (choices 1) [16,64] r8192 c8192
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u641
  · exact u642

def b8193 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 112, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 41 131 261 14 50 96 80 196 324), lower := (rows 41 131 261 14 50 96 80 128 256), losses := [] }

theorem u8193 : Upper (D 6) (R 6) [40,129,257,6,34,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8193 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8194 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 80, targets := 1 },{ cop := 3, region := 97, targets := 2 },{ cop := 3, region := 80, targets := 32 }], pairs := [(0,1),(4,0),(4,5)], upper := (rows 41 131 261 14 82 96 68 176 304), lower := (rows 41 131 261 14 82 96 68 128 256), losses := [] }

theorem u8194 : Upper (D 6) (R 6) [40,129,257,6,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8195 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 261 14 82 96 80 164 292), lower := (rows 41 131 261 14 82 96 80 128 256), losses := [] }

theorem u8195 : Upper (D 6) (R 6) [40,129,257,6,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8195 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8196 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 112, targets := 5 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(4,0),(4,2)], upper := (rows 41 131 261 14 82 96 96 148 276), lower := (rows 41 131 261 14 82 96 96 128 256), losses := [] }

theorem u8196 : Upper (D 6) (R 6) [40,129,257,6,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8197 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 41 131 261 26 112 36 66 196 324), lower := (rows 41 131 261 26 112 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 17 36 74 128 256), good := (rows 120 218 308 90 112 36 74 128 256) }] }

theorem u8197 : Upper (D 6) (R 6) [40,129,257,18,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8198 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 261 26 112 36 68 194 322), lower := (rows 41 131 261 26 112 36 68 128 256), losses := [] }

theorem u8198 : Upper (D 6) (R 6) [40,129,257,18,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8199 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 293, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 131 261 74 22 36 80 224 352), lower := (rows 41 131 261 74 22 36 80 128 256), losses := [] }

theorem u8199 : Upper (D 6) (R 6) [40,129,257,66,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8199 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8200 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(1,5),(3,0),(3,2)], upper := (rows 41 131 261 74 22 36 96 208 336), lower := (rows 41 131 261 74 22 36 96 128 256), losses := [{ target := 2, region := (rows 1 2 0 10 16 32 97 128 256), good := (rows 105 203 321 74 26 96 96 128 256) },{ target := 5, region := (rows 1 3 5 8 23 0 64 136 264), good := (rows 415 151 279 474 22 20 64 128 256) }] }

theorem u8200 : Upper (D 6) (R 6) [40,129,257,66,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8201 : PairBound 9 := { available := 80, camps := [], pairs := [(0,1),(3,0),(4,0)], upper := (rows 41 131 261 74 50 36 68 208 336), lower := (rows 41 131 261 74 50 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 100 100 153 281), good := (rows 504 386 484 506 506 100 100 128 256) },{ target := 1, region := (rows 9 0 4 8 16 100 100 144 272), good := (rows 105 129 357 105 496 100 100 128 256) }] }

theorem u8201 : Upper (D 6) (R 6) [40,129,257,66,34,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8202 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 293, targets := 2 }], pairs := [(0,1),(2,1)], upper := (rows 41 131 261 74 50 36 80 196 324), lower := (rows 41 131 261 74 50 36 80 128 256), losses := [] }

theorem u8202 : Upper (D 6) (R 6) [40,129,257,66,34,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8202 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8203 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 261 74 84 36 66 176 304), lower := (rows 41 131 261 74 84 36 66 128 256), losses := [] }

theorem u8203 : Upper (D 6) (R 6) [40,129,257,66,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8204 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 261 74 84 36 80 162 290), lower := (rows 41 131 261 74 84 36 80 128 256), losses := [] }

theorem u8204 : Upper (D 6) (R 6) [40,129,257,66,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8204 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8205 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 41 131 261 74 84 36 96 146 274), lower := (rows 41 131 261 74 84 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 52 52 117 128 256), good := (rows 120 202 372 74 116 116 112 128 256) }] }

theorem u8205 : Upper (D 6) (R 6) [40,129,257,66,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8206 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 72, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 41 131 261 74 112 36 66 148 276), lower := (rows 41 131 261 74 112 36 66 128 256), losses := [] }

theorem u8206 : Upper (D 6) (R 6) [40,129,257,66,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8207 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 139, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 131 261 74 112 36 68 146 274), lower := (rows 41 131 261 74 112 36 68 128 256), losses := [] }

theorem u8207 : Upper (D 6) (R 6) [40,129,257,66,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8208 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 261 74 112 36 80 134 262), lower := (rows 41 131 261 74 112 36 80 128 256), losses := [] }

theorem u8208 : Upper (D 6) (R 6) [40,129,257,66,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8208 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8209 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 105, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 262 13 82 96 68 176 304), lower := (rows 41 131 262 13 82 96 68 128 256), losses := [] }

theorem u8209 : Upper (D 6) (R 6) [40,129,258,5,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8210 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 41 131 262 13 82 96 80 164 292), lower := (rows 41 131 262 13 82 96 80 128 256), losses := [] }

theorem u8210 : Upper (D 6) (R 6) [40,129,258,5,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8210 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8211 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 105, targets := 2 }], pairs := [(0,1),(2,0),(4,0)], upper := (rows 41 131 262 13 82 96 96 148 276), lower := (rows 41 131 262 13 82 96 96 128 256), losses := [] }

theorem u8211 : Upper (D 6) (R 6) [40,129,258,5,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8212 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 2, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 41 131 262 25 82 36 68 224 352), lower := (rows 41 131 262 25 82 36 68 128 256), losses := [] }

theorem u8212 : Upper (D 6) (R 6) [40,129,258,17,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8213 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 372, targets := 1 },{ cop := 4, region := 260, targets := 32 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 131 262 25 82 36 96 196 324), lower := (rows 41 131 262 25 82 36 96 128 256), losses := [] }

theorem u8213 : Upper (D 6) (R 6) [40,129,258,17,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8214 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(0,1),(1,2),(2,0)], upper := (rows 41 131 262 26 21 96 68 224 352), lower := (rows 41 131 262 26 21 96 68 128 256), losses := [{ target := 1, region := (rows 9 0 4 8 16 124 84 252 380), good := (rows 425 129 484 505 501 480 484 128 256) },{ target := 2, region := (rows 1 3 0 24 16 96 64 224 352), good := (rows 427 131 258 26 27 480 480 128 256) }] }

theorem u8214 : Upper (D 6) (R 6) [40,129,258,18,5,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8215 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 97, targets := 6 },{ cop := 1, region := 356, targets := 1 }], pairs := [(0,1),(0,2),(2,0)], upper := (rows 41 131 262 26 21 96 96 196 324), lower := (rows 41 131 262 26 21 96 96 128 256), losses := [] }

theorem u8215 : Upper (D 6) (R 6) [40,129,258,18,5,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8216 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 3, region := 97, targets := 2 }], pairs := [(0,1),(1,5),(2,5)], upper := (rows 41 131 262 26 52 96 65 196 324), lower := (rows 41 131 262 26 52 96 65 128 256), losses := [] }

theorem u8216 : Upper (D 6) (R 6) [40,129,258,18,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8217 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 454, targets := 32 },{ cop := 2, region := 120, targets := 1 }], pairs := [(1,5),(2,5),(3,0)], upper := (rows 41 131 262 26 52 96 68 193 321), lower := (rows 41 131 262 26 52 96 68 128 256), losses := [] }

theorem u8217 : Upper (D 6) (R 6) [40,129,258,18,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8218 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 356, targets := 1 }], pairs := [(2,0),(3,5),(4,1)], upper := (rows 41 131 262 26 81 36 68 224 352), lower := (rows 41 131 262 26 81 36 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 100 100 245 373), good := (rows 505 401 484 408 497 484 484 128 256) },{ target := 5, region := (rows 1 2 4 10 17 0 100 128 256), good := (rows 89 155 334 26 81 68 68 128 256) }] }

theorem u8218 : Upper (D 6) (R 6) [40,129,258,18,65,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b8219 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 41 131 262 26 81 36 96 196 324), lower := (rows 41 131 262 26 81 36 96 128 256), losses := [] }

theorem u8219 : Upper (D 6) (R 6) [40,129,258,18,65,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b8219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u8219
end Delivery.IrregularNine14.P06
