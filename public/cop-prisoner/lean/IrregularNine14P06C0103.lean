import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0007

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 100 25 148 288 68 131 259), lower := (rows 35 74 100 25 148 288 68 128 256), losses := [] }

theorem u6180 : Upper (D 6) (R 6) [34,72,96,17,132,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6180 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 100 25 400 36 65 134 262), lower := (rows 35 74 100 25 400 36 65 128 256), losses := [] }

theorem u6181 : Upper (D 6) (R 6) [34,72,96,17,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6182 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 35 74 100 25 400 36 66 133 261), lower := (rows 35 74 100 25 400 36 66 128 256), losses := [] }

theorem u6182 : Upper (D 6) (R 6) [34,72,96,17,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6183 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 25 400 36 68 131 259), lower := (rows 35 74 100 25 400 36 68 128 256), losses := [] }

theorem u6183 : Upper (D 6) (R 6) [34,72,96,17,384,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6184 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 68, targets := 2 },{ cop := 1, region := 292, targets := 1 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 28 145 288 65 134 262), lower := (rows 35 74 100 28 145 288 65 128 256), losses := [] }

theorem u6184 : Upper (D 6) (R 6) [34,72,96,20,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6184 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6185 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 100 28 145 288 66 133 261), lower := (rows 35 74 100 28 145 288 66 128 256), losses := [] }

theorem u6185 : Upper (D 6) (R 6) [34,72,96,20,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6185 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6186 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 289, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 100 28 145 288 68 131 259), lower := (rows 35 74 100 28 145 288 68 128 256), losses := [] }

theorem u6186 : Upper (D 6) (R 6) [34,72,96,20,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6186 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6187 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 28 400 33 65 134 262), lower := (rows 35 74 100 28 400 33 65 128 256), losses := [] }

theorem u6187 : Upper (D 6) (R 6) [34,72,96,20,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6188 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 100 28 400 33 66 133 261), lower := (rows 35 74 100 28 400 33 66 128 256), losses := [] }

theorem u6188 : Upper (D 6) (R 6) [34,72,96,20,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6189 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 100 28 400 33 68 131 259), lower := (rows 35 74 100 28 400 33 68 128 256), losses := [] }

theorem u6189 : Upper (D 6) (R 6) [34,72,96,20,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6190 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 35 74 100 137 273 36 66 148 276), lower := (rows 35 74 100 137 273 36 66 128 256), losses := [] }

theorem u6190 : Upper (D 6) (R 6) [34,72,96,129,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6191 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 137 273 36 68 146 274), lower := (rows 35 74 100 137 273 36 68 128 256), losses := [] }

theorem u6191 : Upper (D 6) (R 6) [34,72,96,129,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6192 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 137 273 36 80 134 262), lower := (rows 35 74 100 137 273 36 80 128 256), losses := [] }

theorem u6192 : Upper (D 6) (R 6) [34,72,96,129,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6192 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6193 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 100 137 274 36 65 148 276), lower := (rows 35 74 100 137 274 36 65 128 256), losses := [] }

theorem u6193 : Upper (D 6) (R 6) [34,72,96,129,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6194 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 137 274 36 68 145 273), lower := (rows 35 74 100 137 274 36 68 128 256), losses := [] }

theorem u6194 : Upper (D 6) (R 6) [34,72,96,129,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6195 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 100, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 137 274 36 80 133 261), lower := (rows 35 74 100 137 274 36 80 128 256), losses := [] }

theorem u6195 : Upper (D 6) (R 6) [34,72,96,129,258,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6195 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6196 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 35 74 100 137 276 36 65 146 274), lower := (rows 35 74 100 137 276 36 65 128 256), losses := [] }

theorem u6196 : Upper (D 6) (R 6) [34,72,96,129,260,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6197 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 35 74 100 137 276 36 66 145 273), lower := (rows 35 74 100 137 276 36 66 128 256), losses := [] }

theorem u6197 : Upper (D 6) (R 6) [34,72,96,129,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6197 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6198 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 137 276 36 80 131 259), lower := (rows 35 74 100 137 276 36 80 128 256), losses := [] }

theorem u6198 : Upper (D 6) (R 6) [34,72,96,129,260,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6198 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6199 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 308, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 35 74 100 137 276 48 65 134 262), lower := (rows 35 74 100 137 276 48 65 128 256), losses := [] }

theorem u6199 : Upper (D 6) (R 6) [34,72,96,129,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6199 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6200 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 100 137 276 48 66 133 261), lower := (rows 35 74 100 137 276 48 66 128 256), losses := [] }

theorem u6200 : Upper (D 6) (R 6) [34,72,96,129,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6200 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6201 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 35 74 100 137 276 48 68 131 259), lower := (rows 35 74 100 137 276 48 68 128 256), losses := [] }

theorem u6201 : Upper (D 6) (R 6) [34,72,96,129,260,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6201 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6202 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 100 140 273 33 66 148 276), lower := (rows 35 74 100 140 273 33 66 128 256), losses := [] }

theorem u6202 : Upper (D 6) (R 6) [34,72,96,132,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6203 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 100 140 273 33 68 146 274), lower := (rows 35 74 100 140 273 33 68 128 256), losses := [] }

theorem u6203 : Upper (D 6) (R 6) [34,72,96,132,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6203 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6204 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 100 140 273 33 80 134 262), lower := (rows 35 74 100 140 273 33 80 128 256), losses := [] }

theorem u6204 : Upper (D 6) (R 6) [34,72,96,132,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6204 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6205 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 100 140 273 48 65 134 262), lower := (rows 35 74 100 140 273 48 65 128 256), losses := [] }

theorem u6205 : Upper (D 6) (R 6) [34,72,96,132,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6205 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6206 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 100 140 273 48 66 133 261), lower := (rows 35 74 100 140 273 48 66 128 256), losses := [] }

theorem u6206 : Upper (D 6) (R 6) [34,72,96,132,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6206 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6207 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 100 140 273 48 68 131 259), lower := (rows 35 74 100 140 273 48 68 128 256), losses := [] }

theorem u6207 : Upper (D 6) (R 6) [34,72,96,132,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6207 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6208 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 140 274 33 65 148 276), lower := (rows 35 74 100 140 274 33 65 128 256), losses := [] }

theorem u6208 : Upper (D 6) (R 6) [34,72,96,132,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6209 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 68 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 100 140 274 33 68 145 273), lower := (rows 35 74 100 140 274 33 68 128 256), losses := [] }

theorem u6209 : Upper (D 6) (R 6) [34,72,96,132,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6210 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 100 140 274 33 80 133 261), lower := (rows 35 74 100 140 274 33 80 128 256), losses := [] }

theorem u6210 : Upper (D 6) (R 6) [34,72,96,132,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6210 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 140 276 33 65 146 274), lower := (rows 35 74 100 140 276 33 65 128 256), losses := [] }

theorem u6211 : Upper (D 6) (R 6) [34,72,96,132,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 100 140 276 33 66 145 273), lower := (rows 35 74 100 140 276 33 66 128 256), losses := [] }

theorem u6212 : Upper (D 6) (R 6) [34,72,96,132,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6213 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 74 100 140 276 33 80 131 259), lower := (rows 35 74 100 140 276 33 80 128 256), losses := [] }

theorem u6213 : Upper (D 6) (R 6) [34,72,96,132,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6213 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6214 : Route 9 := (fun mask => (mask,id))

def c6214 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6214 : Upper (D 6) (R 6) [34,72,96,132,260,16,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,132,260,16,1] 13 (by decide) (choices 1) [1,2] r6214 c6214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u455
  · exact u456

def b6215 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 66, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 35 74 100 140 276 48 66 129 257), lower := (rows 35 74 100 140 276 48 66 128 256), losses := [] }

theorem u6215 : Upper (D 6) (R 6) [34,72,96,132,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6215 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6216 : PairBound 9 := { available := 6, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 74 100 152 273 36 65 134 262), lower := (rows 35 74 100 152 273 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 70 24 16 103 64 131 259), good := (rows 422 494 100 152 440 36 484 128 256) }] }

theorem u6216 : Upper (D 6) (R 6) [34,72,96,144,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6217 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 35 74 100 152 273 36 66 133 261), lower := (rows 35 74 100 152 273 36 66 128 256), losses := [] }

theorem u6217 : Upper (D 6) (R 6) [34,72,96,144,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6218 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 152 273 36 68 131 259), lower := (rows 35 74 100 152 273 36 68 128 256), losses := [] }

theorem u6218 : Upper (D 6) (R 6) [34,72,96,144,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6219 : Route 9 := (fun mask => (mask,id))

def c6219 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6219 : Upper (D 6) (R 6) [34,72,96,144,258,4,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,258,4,1] 13 (by decide) (choices 1) [1,4] r6219 c6219
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u457
  · exact u458

def b6220 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 74 100 152 274 36 68 129 257), lower := (rows 35 74 100 152 274 36 68 128 256), losses := [] }

theorem u6220 : Upper (D 6) (R 6) [34,72,96,144,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6220 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6221 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 74 100 152 276 33 65 134 262), lower := (rows 35 74 100 152 276 33 65 128 256), losses := [] }

theorem u6221 : Upper (D 6) (R 6) [34,72,96,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6221 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 66, targets := 33 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,0),(1,5)], upper := (rows 35 74 100 152 276 33 66 133 261), lower := (rows 35 74 100 152 276 33 66 128 256), losses := [] }

theorem u6222 : Upper (D 6) (R 6) [34,72,96,144,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6222 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 5, region := 68, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 100 152 276 33 68 131 259), lower := (rows 35 74 100 152 276 33 68 128 256), losses := [] }

theorem u6223 : Upper (D 6) (R 6) [34,72,96,144,260,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6223 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r6224 : Route 9 := (fun mask => (mask,id))

def c6224 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6224 : Upper (D 6) (R 6) [34,72,96,144,260,4,1] 13 := by
  apply FastRouting.sound _ _ [34,72,96,144,260,4,1] 13 (by decide) (choices 1) [1,2] r6224 c6224
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u459
  · exact u460

def b6225 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 102, targets := 1 },{ cop := 3, region := 66, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 35 74 100 152 276 36 66 129 257), lower := (rows 35 74 100 152 276 36 66 128 256), losses := [] }

theorem u6225 : Upper (D 6) (R 6) [34,72,96,144,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6225 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6226 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(0,6),(2,1),(4,0)], upper := (rows 35 74 133 25 274 36 68 224 352), lower := (rows 35 74 133 25 274 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 19 100 100 231 359), good := (rows 498 506 500 408 402 484 484 128 256) },{ target := 6, region := (rows 3 2 4 24 16 100 0 128 256), good := (rows 35 43 165 25 283 36 36 128 256) }] }

theorem u6226 : Upper (D 6) (R 6) [34,72,129,17,258,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6226 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6227 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 35 74 133 25 274 36 96 196 324), lower := (rows 35 74 133 25 274 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 17 36 101 164 292), good := (rows 498 74 500 90 274 484 480 128 256) }] }

theorem u6227 : Upper (D 6) (R 6) [34,72,129,17,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6227 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6228 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 133 25 304 36 66 196 324), lower := (rows 35 74 133 25 304 36 66 128 256), losses := [] }

theorem u6228 : Upper (D 6) (R 6) [34,72,129,17,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6228 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6229 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(4,0)], upper := (rows 35 74 133 25 304 36 68 194 322), lower := (rows 35 74 133 25 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 23 100 100 131 259), good := (rows 498 506 500 408 368 116 116 128 256) }] }

theorem u6229 : Upper (D 6) (R 6) [34,72,129,17,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6229 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6230 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 25 336 36 66 164 292), lower := (rows 35 74 133 25 336 36 66 128 256), losses := [] }

theorem u6230 : Upper (D 6) (R 6) [34,72,129,17,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6230 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6231 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 35 74 133 25 336 36 68 162 290), lower := (rows 35 74 133 25 336 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 23 100 100 131 259), good := (rows 498 506 500 408 368 116 116 128 256) }] }

theorem u6231 : Upper (D 6) (R 6) [34,72,129,17,320,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6231 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6232 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 0, region := 132, targets := 32 }], pairs := [(0,6),(2,5),(2,6)], upper := (rows 35 74 133 25 336 36 96 134 262), lower := (rows 35 74 133 25 336 36 96 128 256), losses := [] }

theorem u6232 : Upper (D 6) (R 6) [34,72,129,17,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6232 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6233 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 74 133 26 273 36 68 224 352), lower := (rows 35 74 133 26 273 36 68 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 100 0 128 256), good := (rows 35 43 165 27 273 36 36 128 256) }] }

theorem u6233 : Upper (D 6) (R 6) [34,72,129,18,257,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6233 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6234 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 74 133 26 273 36 96 196 324), lower := (rows 35 74 133 26 273 36 96 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 36 101 164 292), good := (rows 482 74 484 26 346 484 480 128 256) }] }

theorem u6234 : Upper (D 6) (R 6) [34,72,129,18,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6234 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6235 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1)], upper := (rows 35 74 133 265 22 36 80 224 352), lower := (rows 35 74 133 265 22 36 80 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 16 61 80 210 338), good := (rows 429 488 173 301 500 36 496 128 256) }] }

theorem u6235 : Upper (D 6) (R 6) [34,72,129,257,6,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6235 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6236 : PairBound 9 := { available := 80, camps := [{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,2)], upper := (rows 35 74 133 265 22 36 96 208 336), lower := (rows 35 74 133 265 22 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 52 117 144 272), good := (rows 98 74 228 330 502 100 96 128 256) },{ target := 2, region := (rows 1 10 0 8 16 32 97 128 256), good := (rows 99 74 193 331 18 96 96 128 256) }] }

theorem u6236 : Upper (D 6) (R 6) [34,72,129,257,6,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6236 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6237 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 66, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 35 74 133 265 84 36 66 176 304), lower := (rows 35 74 133 265 84 36 66 128 256), losses := [] }

theorem u6237 : Upper (D 6) (R 6) [34,72,129,257,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6237 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6238 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 74 133 265 84 36 80 162 290), lower := (rows 35 74 133 265 84 36 80 128 256), losses := [] }

theorem u6238 : Upper (D 6) (R 6) [34,72,129,257,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6238 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b6239 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 35 74 133 265 84 36 96 146 274), lower := (rows 35 74 133 265 84 36 96 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 52 52 117 129 257), good := (rows 498 74 500 458 116 116 112 128 256) }] }

theorem u6239 : Upper (D 6) (R 6) [34,72,129,257,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b6239 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u6239
end Delivery.IrregularNine14.P06
