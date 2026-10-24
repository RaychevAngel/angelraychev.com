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

def b26160 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 41 98 148 268 19 34 69 197 325), lower := (rows 41 98 148 268 19 34 64 128 256), losses := [] }

theorem u26160 : Upper (D 6) (R 6) [40,96,144,260,3,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26161 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 268 19 36 67 195 323), lower := (rows 41 98 148 268 19 36 64 128 256), losses := [] }

theorem u26161 : Upper (D 6) (R 6) [40,96,144,260,3,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26162 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 268 19 96 71 135 263), lower := (rows 41 98 148 268 19 96 64 128 256), losses := [] }

theorem u26162 : Upper (D 6) (R 6) [40,96,144,260,3,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26163 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 49, targets := 66 }], pairs := [(0,1),(0,6),(4,1)], upper := (rows 41 98 148 268 21 33 66 194 322), lower := (rows 41 98 148 268 21 33 64 128 256), losses := [] }

theorem u26163 : Upper (D 6) (R 6) [40,96,144,260,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26164 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 268 21 34 67 195 323), lower := (rows 41 98 148 268 21 34 64 128 256), losses := [] }

theorem u26164 : Upper (D 6) (R 6) [40,96,144,260,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26165 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 268 21 96 67 131 259), lower := (rows 41 98 148 268 21 96 64 128 256), losses := [] }

theorem u26165 : Upper (D 6) (R 6) [40,96,144,260,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26166 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 268 22 33 67 195 323), lower := (rows 41 98 148 268 22 33 64 128 256), losses := [] }

theorem u26166 : Upper (D 6) (R 6) [40,96,144,260,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26167 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 268 22 34 65 193 321), lower := (rows 41 98 148 268 22 34 64 128 256), losses := [] }

theorem u26167 : Upper (D 6) (R 6) [40,96,144,260,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26167 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26168 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 41 98 148 268 22 96 67 131 259), lower := (rows 41 98 148 268 22 96 64 128 256), losses := [] }

theorem u26168 : Upper (D 6) (R 6) [40,96,144,260,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26169 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 268 81 33 70 134 262), lower := (rows 41 98 148 268 81 33 64 128 256), losses := [] }

theorem u26169 : Upper (D 6) (R 6) [40,96,144,260,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26170 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 268 81 34 71 135 263), lower := (rows 41 98 148 268 81 34 64 128 256), losses := [{ target := 2, region := (rows 9 82 0 8 16 118 64 128 256), good := (rows 41 98 178 297 115 34 98 128 256) }] }

theorem u26170 : Upper (D 6) (R 6) [40,96,144,260,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26171 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 82, targets := 4 },{ cop := 3, region := 33, targets := 2 }], pairs := [(0,1),(1,2),(4,2)], upper := (rows 41 98 148 268 81 36 67 131 259), lower := (rows 41 98 148 268 81 36 64 128 256), losses := [] }

theorem u26171 : Upper (D 6) (R 6) [40,96,144,260,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26172 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 268 84 33 67 131 259), lower := (rows 41 98 148 268 84 33 64 128 256), losses := [] }

theorem u26172 : Upper (D 6) (R 6) [40,96,144,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26173 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 268 84 34 67 131 259), lower := (rows 41 98 148 268 84 34 64 128 256), losses := [] }

theorem u26173 : Upper (D 6) (R 6) [40,96,144,260,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26174 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 328 21 33 70 134 262), lower := (rows 41 98 148 328 21 33 64 128 256), losses := [] }

theorem u26174 : Upper (D 6) (R 6) [40,96,144,320,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26175 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 328 21 34 71 135 263), lower := (rows 41 98 148 328 21 34 64 128 256), losses := [] }

theorem u26175 : Upper (D 6) (R 6) [40,96,144,320,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26176 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 328 21 36 67 131 259), lower := (rows 41 98 148 328 21 36 64 128 256), losses := [] }

theorem u26176 : Upper (D 6) (R 6) [40,96,144,320,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26177 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 33, targets := 66 },{ cop := 3, region := 33, targets := 4 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 148 328 22 33 71 135 263), lower := (rows 41 98 148 328 22 33 64 128 256), losses := [] }

theorem u26177 : Upper (D 6) (R 6) [40,96,144,320,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26178 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 35, targets := 4 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 148 328 22 34 69 133 261), lower := (rows 41 98 148 328 22 34 64 128 256), losses := [] }

theorem u26178 : Upper (D 6) (R 6) [40,96,144,320,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26179 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 41 98 148 328 22 36 67 131 259), lower := (rows 41 98 148 328 22 36 64 128 256), losses := [] }

theorem u26179 : Upper (D 6) (R 6) [40,96,144,320,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26180 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 196 13 22 33 338 402 274), lower := (rows 41 98 196 13 22 33 64 128 256), losses := [] }

theorem u26180 : Upper (D 6) (R 6) [40,96,192,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26180 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26181 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 41, targets := 64 }], pairs := [(0,6),(1,0),(4,0)], upper := (rows 41 98 196 13 22 34 337 401 273), lower := (rows 41 98 196 13 22 34 64 128 256), losses := [] }

theorem u26181 : Upper (D 6) (R 6) [40,96,192,5,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26181 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26182 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 41 98 196 13 22 48 323 387 259), lower := (rows 41 98 196 13 22 48 64 128 256), losses := [] }

theorem u26182 : Upper (D 6) (R 6) [40,96,192,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26182 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26183 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 98 196 13 22 288 83 147 275), lower := (rows 41 98 196 13 22 288 64 128 256), losses := [] }

theorem u26183 : Upper (D 6) (R 6) [40,96,192,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26183 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26184 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,0),(1,2),(2,0)], upper := (rows 41 98 196 13 273 34 86 150 278), lower := (rows 41 98 196 13 273 34 64 128 256), losses := [] }

theorem u26184 : Upper (D 6) (R 6) [40,96,192,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26185 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 196 13 273 36 82 146 274), lower := (rows 41 98 196 13 273 36 64 128 256), losses := [] }

theorem u26185 : Upper (D 6) (R 6) [40,96,192,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26186 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 198, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 41 98 196 13 273 48 70 134 262), lower := (rows 41 98 196 13 273 48 64 128 256), losses := [] }

theorem u26186 : Upper (D 6) (R 6) [40,96,192,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26186 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26187 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 196 13 274 33 86 150 278), lower := (rows 41 98 196 13 274 33 64 128 256), losses := [] }

theorem u26187 : Upper (D 6) (R 6) [40,96,192,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26187 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26188 : PairBound 9 := { available := 21, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 13 274 34 85 149 277), lower := (rows 41 98 196 13 274 34 64 128 256), losses := [{ target := 2, region := (rows 9 70 0 8 16 126 64 128 256), good := (rows 41 98 226 43 306 34 98 128 256) }] }

theorem u26188 : Upper (D 6) (R 6) [40,96,192,5,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26189 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 196 13 274 36 83 147 275), lower := (rows 41 98 196 13 274 36 64 128 256), losses := [] }

theorem u26189 : Upper (D 6) (R 6) [40,96,192,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26190 : Route 9 := (fun mask => (mask,id))

def c26190 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26190 : Upper (D 6) (R 6) [40,96,192,5,258,16] 13 := by
  apply FastRouting.sound _ _ [40,96,192,5,258,16] 13 (by decide) (choices 1) [1,2,4] r26190 c26190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8169
  · exact u8170
  · exact u8171

def b26191 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 196 13 276 33 82 146 274), lower := (rows 41 98 196 13 276 33 64 128 256), losses := [] }

theorem u26191 : Upper (D 6) (R 6) [40,96,192,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26192 : PairBound 9 := { available := 19, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 13 276 34 83 147 275), lower := (rows 41 98 196 13 276 34 64 128 256), losses := [{ target := 2, region := (rows 9 70 0 8 16 126 64 128 256), good := (rows 41 98 226 43 306 34 98 128 256) }] }

theorem u26192 : Upper (D 6) (R 6) [40,96,192,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26193 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6)], upper := (rows 41 98 196 13 276 48 67 131 259), lower := (rows 41 98 196 13 276 48 64 128 256), losses := [] }

theorem u26193 : Upper (D 6) (R 6) [40,96,192,5,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26193 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26194 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 14 273 33 86 150 278), lower := (rows 41 98 196 14 273 33 64 128 256), losses := [] }

theorem u26194 : Upper (D 6) (R 6) [40,96,192,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26195 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 14 273 34 85 149 277), lower := (rows 41 98 196 14 273 34 64 128 256), losses := [] }

theorem u26195 : Upper (D 6) (R 6) [40,96,192,6,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26196 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 196 14 273 36 83 147 275), lower := (rows 41 98 196 14 273 36 64 128 256), losses := [] }

theorem u26196 : Upper (D 6) (R 6) [40,96,192,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26197 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 41 98 196 14 273 48 71 135 263), lower := (rows 41 98 196 14 273 48 64 128 256), losses := [] }

theorem u26197 : Upper (D 6) (R 6) [40,96,192,6,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26197 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26198 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 14 274 33 85 149 277), lower := (rows 41 98 196 14 274 33 64 128 256), losses := [] }

theorem u26198 : Upper (D 6) (R 6) [40,96,192,6,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26199 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 338, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(4,2)], upper := (rows 41 98 196 14 274 36 81 145 273), lower := (rows 41 98 196 14 274 36 64 128 256), losses := [] }

theorem u26199 : Upper (D 6) (R 6) [40,96,192,6,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26200 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 196, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 41 98 196 14 274 48 69 133 261), lower := (rows 41 98 196 14 274 48 64 128 256), losses := [] }

theorem u26200 : Upper (D 6) (R 6) [40,96,192,6,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26200 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26201 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 6 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 14 276 33 83 147 275), lower := (rows 41 98 196 14 276 33 64 128 256), losses := [] }

theorem u26201 : Upper (D 6) (R 6) [40,96,192,6,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26201 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26202 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 14 276 34 81 145 273), lower := (rows 41 98 196 14 276 34 64 128 256), losses := [] }

theorem u26202 : Upper (D 6) (R 6) [40,96,192,6,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26203 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 41 98 196 14 276 48 67 131 259), lower := (rows 41 98 196 14 276 48 64 128 256), losses := [] }

theorem u26203 : Upper (D 6) (R 6) [40,96,192,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26203 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26204 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 41 98 196 25 22 33 326 390 262), lower := (rows 41 98 196 25 22 33 64 128 256), losses := [] }

theorem u26204 : Upper (D 6) (R 6) [40,96,192,17,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26204 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26205 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 452, targets := 34 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 41 98 196 25 22 34 325 389 261), lower := (rows 41 98 196 25 22 34 64 128 256), losses := [] }

theorem u26205 : Upper (D 6) (R 6) [40,96,192,17,6,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26205 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26206 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 50, targets := 1 },{ cop := 4, region := 41, targets := 2 }], pairs := [(0,1),(1,0),(4,0)], upper := (rows 41 98 196 25 22 36 323 387 259), lower := (rows 41 98 196 25 22 36 64 128 256), losses := [] }

theorem u26206 : Upper (D 6) (R 6) [40,96,192,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26207 : PairBound 9 := { available := 7, camps := [{ cop := 4, region := 297, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 41 98 196 25 22 288 71 135 263), lower := (rows 41 98 196 25 22 288 64 128 256), losses := [] }

theorem u26207 : Upper (D 6) (R 6) [40,96,192,17,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26207 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26208 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 25 274 33 70 134 262), lower := (rows 41 98 196 25 274 33 64 128 256), losses := [] }

theorem u26208 : Upper (D 6) (R 6) [40,96,192,17,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26208 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26209 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 41, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 41 98 196 25 274 34 69 133 261), lower := (rows 41 98 196 25 274 34 64 128 256), losses := [] }

theorem u26209 : Upper (D 6) (R 6) [40,96,192,17,258,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26209 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26210 : Route 9 := (fun mask => (mask,id))

def c26210 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26210 : Upper (D 6) (R 6) [40,96,192,17,258,4] 13 := by
  apply FastRouting.sound _ _ [40,96,192,17,258,4] 13 (by decide) (choices 1) [1,2,4] r26210 c26210
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8172
  · exact u8173
  · exact u8174

def b26211 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 41, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 25 276 33 70 134 262), lower := (rows 41 98 196 25 276 33 64 128 256), losses := [] }

theorem u26211 : Upper (D 6) (R 6) [40,96,192,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26211 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26212 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 34, targets := 5 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 41 98 196 25 276 34 71 135 263), lower := (rows 41 98 196 25 276 34 64 128 256), losses := [{ target := 2, region := (rows 25 70 0 24 16 118 64 128 256), good := (rows 41 98 226 57 315 34 98 128 256) }] }

theorem u26212 : Upper (D 6) (R 6) [40,96,192,17,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26212 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26213 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 41, targets := 66 }], pairs := [(0,1),(0,6),(3,1)], upper := (rows 41 98 196 25 276 36 67 131 259), lower := (rows 41 98 196 25 276 36 64 128 256), losses := [] }

theorem u26213 : Upper (D 6) (R 6) [40,96,192,17,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26214 : PairBound 9 := { available := 262, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 26 21 33 326 390 262), lower := (rows 41 98 196 26 21 33 64 128 256), losses := [] }

theorem u26214 : Upper (D 6) (R 6) [40,96,192,18,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26215 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 26 21 34 325 389 261), lower := (rows 41 98 196 26 21 34 64 128 256), losses := [] }

theorem u26215 : Upper (D 6) (R 6) [40,96,192,18,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26215 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26216 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 322, targets := 4 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 41 98 196 26 21 36 323 387 259), lower := (rows 41 98 196 26 21 36 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 52 64 128 256), good := (rows 40 98 230 58 62 38 64 128 256) }] }

theorem u26216 : Upper (D 6) (R 6) [40,96,192,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26216 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r26217 : Route 9 := (fun mask => (mask,id))

def c26217 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u26217 : Upper (D 6) (R 6) [40,96,192,18,5,256] 13 := by
  apply FastRouting.sound _ _ [40,96,192,18,5,256] 13 (by decide) (choices 1) [1,2,4] r26217 c26217
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8175
  · exact u8176
  · exact u8177

def b26218 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 33, targets := 70 }], pairs := [(0,1),(0,2),(0,6)], upper := (rows 41 98 196 26 273 33 70 134 262), lower := (rows 41 98 196 26 273 33 64 128 256), losses := [] }

theorem u26218 : Upper (D 6) (R 6) [40,96,192,18,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b26219 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 468, targets := 34 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 41 98 196 26 273 34 69 133 261), lower := (rows 41 98 196 26 273 34 64 128 256), losses := [] }

theorem u26219 : Upper (D 6) (R 6) [40,96,192,18,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b26219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u26219
end Delivery.IrregularNine14.P06
