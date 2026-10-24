import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0086

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19020 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(3,1),(4,6),(4,7)], upper := (rows 35 70 28 200 274 160 97 161 289), lower := (rows 35 70 28 200 274 160 64 128 256), losses := [] }

theorem u19020 : Upper (D 7) (R 7) [34,68,24,192,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19020 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19021 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,5),(4,6)], upper := (rows 35 70 28 200 304 33 195 131 387), lower := (rows 35 70 28 200 304 33 64 128 256), losses := [] }

theorem u19021 : Upper (D 7) (R 7) [34,68,24,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19021 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19022 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 70 28 200 304 34 193 129 385), lower := (rows 35 70 28 200 304 34 64 128 256), losses := [] }

theorem u19022 : Upper (D 7) (R 7) [34,68,24,192,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19022 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19023 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 272, targets := 128 }], pairs := [(0,6),(3,5),(4,6),(4,7)], upper := (rows 35 70 28 200 304 160 67 131 259), lower := (rows 35 70 28 200 304 160 64 128 256), losses := [] }

theorem u19023 : Upper (D 7) (R 7) [34,68,24,192,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19023 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19024 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 25 400 33 194 194 450), lower := (rows 35 70 44 25 400 33 64 128 256), losses := [] }

theorem u19024 : Upper (D 7) (R 7) [34,68,40,17,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19024 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19025 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 25 400 34 193 193 449), lower := (rows 35 70 44 25 400 34 64 128 256), losses := [] }

theorem u19025 : Upper (D 7) (R 7) [34,68,40,17,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19025 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19026 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 25 400 96 195 131 387), lower := (rows 35 70 44 25 400 96 64 128 256), losses := [] }

theorem u19026 : Upper (D 7) (R 7) [34,68,40,17,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19026 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19027 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 25 400 160 67 195 323), lower := (rows 35 70 44 25 400 160 64 128 256), losses := [] }

theorem u19027 : Upper (D 7) (R 7) [34,68,40,17,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19027 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19028 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 26 400 33 193 193 449), lower := (rows 35 70 44 26 400 33 64 128 256), losses := [] }

theorem u19028 : Upper (D 7) (R 7) [34,68,40,18,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19028 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19029 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 26 400 96 193 129 385), lower := (rows 35 70 44 26 400 96 64 128 256), losses := [] }

theorem u19029 : Upper (D 7) (R 7) [34,68,40,18,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19029 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19030 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(1,7),(3,5),(4,5)], upper := (rows 35 70 44 26 400 160 65 193 321), lower := (rows 35 70 44 26 400 160 64 128 256), losses := [] }

theorem u19030 : Upper (D 7) (R 7) [34,68,40,18,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19030 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19031 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 137 81 34 464 400 400), lower := (rows 35 70 44 137 81 34 64 128 256), losses := [] }

theorem u19031 : Upper (D 7) (R 7) [34,68,40,129,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19031 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19032 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 137 81 48 450 386 386), lower := (rows 35 70 44 137 81 48 64 128 256), losses := [] }

theorem u19032 : Upper (D 7) (R 7) [34,68,40,129,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19032 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19033 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 137 81 160 338 402 274), lower := (rows 35 70 44 137 81 160 64 128 256), losses := [] }

theorem u19033 : Upper (D 7) (R 7) [34,68,40,129,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19033 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19034 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 70 44 137 81 288 210 146 402), lower := (rows 35 70 44 137 81 288 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 69 133 261), good := (rows 475 454 478 473 473 256 64 128 256) }] }

theorem u19034 : Upper (D 7) (R 7) [34,68,40,129,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19034 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19035 : PairBound 9 := { available := 274, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 208 33 338 402 274), lower := (rows 35 70 44 137 208 33 64 128 256), losses := [] }

theorem u19035 : Upper (D 7) (R 7) [34,68,40,129,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19035 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19036 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 137 208 34 337 401 273), lower := (rows 35 70 44 137 208 34 64 128 256), losses := [] }

theorem u19036 : Upper (D 7) (R 7) [34,68,40,129,192,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19036 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19037 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 137 208 48 323 387 259), lower := (rows 35 70 44 137 208 48 64 128 256), losses := [] }

theorem u19037 : Upper (D 7) (R 7) [34,68,40,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19037 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r19038 : Route 9 := (fun mask => (mask,id))

def c19038 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19038 : Upper (D 7) (R 7) [34,68,40,129,192,256] 13 := by
  apply FastRouting.sound _ _ [34,68,40,129,192,256] 13 (by decide) (choices 1) [1,2,16] r19038 c19038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5215
  · exact u5216
  · exact u5217

def b19039 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 137 273 34 208 208 464), lower := (rows 35 70 44 137 273 34 64 128 256), losses := [] }

theorem u19039 : Upper (D 7) (R 7) [34,68,40,129,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19039 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19040 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 44 137 273 48 194 194 450), lower := (rows 35 70 44 137 273 48 64 128 256), losses := [] }

theorem u19040 : Upper (D 7) (R 7) [34,68,40,129,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19040 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19041 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 137 273 96 210 146 402), lower := (rows 35 70 44 137 273 96 64 128 256), losses := [] }

theorem u19041 : Upper (D 7) (R 7) [34,68,40,129,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19041 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19042 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 137 273 160 82 210 338), lower := (rows 35 70 44 137 273 160 64 128 256), losses := [] }

theorem u19042 : Upper (D 7) (R 7) [34,68,40,129,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19042 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19043 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 274 33 208 208 464), lower := (rows 35 70 44 137 274 33 64 128 256), losses := [] }

theorem u19043 : Upper (D 7) (R 7) [34,68,40,129,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19043 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19044 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,1),(3,5)], upper := (rows 35 70 44 137 274 48 193 193 449), lower := (rows 35 70 44 137 274 48 64 128 256), losses := [] }

theorem u19044 : Upper (D 7) (R 7) [34,68,40,129,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19044 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19045 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 137 274 96 209 145 401), lower := (rows 35 70 44 137 274 96 64 128 256), losses := [] }

theorem u19045 : Upper (D 7) (R 7) [34,68,40,129,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19045 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19046 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 137 274 160 81 209 337), lower := (rows 35 70 44 137 274 160 64 128 256), losses := [] }

theorem u19046 : Upper (D 7) (R 7) [34,68,40,129,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19046 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19047 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 336 33 210 146 402), lower := (rows 35 70 44 137 336 33 64 128 256), losses := [] }

theorem u19047 : Upper (D 7) (R 7) [34,68,40,129,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19047 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19048 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 137 336 34 209 145 401), lower := (rows 35 70 44 137 336 34 64 128 256), losses := [] }

theorem u19048 : Upper (D 7) (R 7) [34,68,40,129,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19048 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19049 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 137 336 48 195 131 387), lower := (rows 35 70 44 137 336 48 64 128 256), losses := [] }

theorem u19049 : Upper (D 7) (R 7) [34,68,40,129,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19049 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19050 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 137 336 160 83 147 275), lower := (rows 35 70 44 137 336 160 64 128 256), losses := [] }

theorem u19050 : Upper (D 7) (R 7) [34,68,40,129,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19050 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19051 : PairBound 9 := { available := 82, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 44 137 400 33 82 210 338), lower := (rows 35 70 44 137 400 33 64 128 256), losses := [] }

theorem u19051 : Upper (D 7) (R 7) [34,68,40,129,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19051 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19052 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 137 400 34 81 209 337), lower := (rows 35 70 44 137 400 34 64 128 256), losses := [] }

theorem u19052 : Upper (D 7) (R 7) [34,68,40,129,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19052 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19053 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 44 137 400 48 67 195 323), lower := (rows 35 70 44 137 400 48 64 128 256), losses := [] }

theorem u19053 : Upper (D 7) (R 7) [34,68,40,129,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19053 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19054 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 137 400 96 83 147 275), lower := (rows 35 70 44 137 400 96 64 128 256), losses := [] }

theorem u19054 : Upper (D 7) (R 7) [34,68,40,129,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19054 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19055 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 138 81 33 464 400 400), lower := (rows 35 70 44 138 81 33 64 128 256), losses := [] }

theorem u19055 : Upper (D 7) (R 7) [34,68,40,130,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19055 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19056 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 138 81 48 449 385 385), lower := (rows 35 70 44 138 81 48 64 128 256), losses := [] }

theorem u19056 : Upper (D 7) (R 7) [34,68,40,130,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19056 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19057 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 35 70 44 138 81 160 337 401 273), lower := (rows 35 70 44 138 81 160 64 128 256), losses := [] }

theorem u19057 : Upper (D 7) (R 7) [34,68,40,130,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19057 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19058 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 138 81 288 209 145 401), lower := (rows 35 70 44 138 81 288 64 128 256), losses := [] }

theorem u19058 : Upper (D 7) (R 7) [34,68,40,130,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19058 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19059 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 53, targets := 64 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,6),(2,6),(3,5),(4,6)], upper := (rows 35 70 44 138 145 33 336 464 336), lower := (rows 35 70 44 138 145 33 64 128 256), losses := [] }

theorem u19059 : Upper (D 7) (R 7) [34,68,40,130,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19059 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19060 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 53, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 44 138 145 48 321 449 321), lower := (rows 35 70 44 138 145 48 64 128 256), losses := [] }

theorem u19060 : Upper (D 7) (R 7) [34,68,40,130,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19060 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19061 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 138 145 96 337 401 273), lower := (rows 35 70 44 138 145 96 64 128 256), losses := [] }

theorem u19061 : Upper (D 7) (R 7) [34,68,40,130,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19061 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19062 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 138 145 288 81 209 337), lower := (rows 35 70 44 138 145 288 64 128 256), losses := [] }

theorem u19062 : Upper (D 7) (R 7) [34,68,40,130,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19062 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19063 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 138 208 33 337 401 273), lower := (rows 35 70 44 138 208 33 64 128 256), losses := [] }

theorem u19063 : Upper (D 7) (R 7) [34,68,40,130,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19063 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19064 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 46, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 70 44 138 208 48 321 385 257), lower := (rows 35 70 44 138 208 48 64 128 256), losses := [] }

theorem u19064 : Upper (D 7) (R 7) [34,68,40,130,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19064 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19065 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 0, region := 208, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 138 208 288 81 145 273), lower := (rows 35 70 44 138 208 288 64 128 256), losses := [] }

theorem u19065 : Upper (D 7) (R 7) [34,68,40,130,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19065 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19066 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 138 273 33 208 208 464), lower := (rows 35 70 44 138 273 33 64 128 256), losses := [] }

theorem u19066 : Upper (D 7) (R 7) [34,68,40,130,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19066 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19067 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 464, targets := 2 }], pairs := [(3,5),(4,1),(4,5)], upper := (rows 35 70 44 138 273 48 193 193 449), lower := (rows 35 70 44 138 273 48 64 128 256), losses := [] }

theorem u19067 : Upper (D 7) (R 7) [34,68,40,130,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19067 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19068 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 138 273 96 209 145 401), lower := (rows 35 70 44 138 273 96 64 128 256), losses := [] }

theorem u19068 : Upper (D 7) (R 7) [34,68,40,130,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19068 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19069 : PairBound 9 := { available := 81, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 35 70 44 138 273 160 81 209 337), lower := (rows 35 70 44 138 273 160 64 128 256), losses := [] }

theorem u19069 : Upper (D 7) (R 7) [34,68,40,130,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19069 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19070 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 138 336 33 209 145 401), lower := (rows 35 70 44 138 336 33 64 128 256), losses := [] }

theorem u19070 : Upper (D 7) (R 7) [34,68,40,130,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19070 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19071 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,5),(4,5)], upper := (rows 35 70 44 138 336 48 193 129 385), lower := (rows 35 70 44 138 336 48 64 128 256), losses := [] }

theorem u19071 : Upper (D 7) (R 7) [34,68,40,130,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19071 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19072 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(3,5),(4,7)], upper := (rows 35 70 44 138 336 160 81 145 273), lower := (rows 35 70 44 138 336 160 64 128 256), losses := [] }

theorem u19072 : Upper (D 7) (R 7) [34,68,40,130,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19072 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19073 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 37, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 70 44 138 400 33 81 209 337), lower := (rows 35 70 44 138 400 33 64 128 256), losses := [] }

theorem u19073 : Upper (D 7) (R 7) [34,68,40,130,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19073 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19074 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 44 138 400 48 65 193 321), lower := (rows 35 70 44 138 400 48 64 128 256), losses := [] }

theorem u19074 : Upper (D 7) (R 7) [34,68,40,130,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19074 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19075 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 138 400 96 81 145 273), lower := (rows 35 70 44 138 400 96 64 128 256), losses := [] }

theorem u19075 : Upper (D 7) (R 7) [34,68,40,130,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19075 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19076 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(3,5),(4,5)], upper := (rows 35 70 44 152 273 33 194 194 450), lower := (rows 35 70 44 152 273 33 64 128 256), losses := [] }

theorem u19076 : Upper (D 7) (R 7) [34,68,40,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19076 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19077 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 0, region := 472, targets := 32 }], pairs := [(2,1),(3,1),(3,5),(4,1)], upper := (rows 35 70 44 152 273 34 193 193 449), lower := (rows 35 70 44 152 273 34 64 128 256), losses := [] }

theorem u19077 : Upper (D 7) (R 7) [34,68,40,144,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19077 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19078 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(2,6),(3,5),(3,6),(4,6)], upper := (rows 35 70 44 152 273 96 195 131 387), lower := (rows 35 70 44 152 273 96 64 128 256), losses := [] }

theorem u19078 : Upper (D 7) (R 7) [34,68,40,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19078 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19079 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 339, targets := 128 },{ cop := 3, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 70 44 152 273 160 67 195 323), lower := (rows 35 70 44 152 273 160 64 128 256), losses := [] }

theorem u19079 : Upper (D 7) (R 7) [34,68,40,144,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19079 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u19079
end Delivery.IrregularNine14.P07
