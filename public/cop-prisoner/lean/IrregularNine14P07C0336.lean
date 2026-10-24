import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0092
import IrregularNine14P07C0093

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20160 : PairBound 9 := { available := 386, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 84 33 450 386 386), lower := (rows 35 194 13 56 84 33 64 128 256), losses := [] }

theorem u20160 : Upper (D 7) (R 7) [34,192,9,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20160 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20161 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 84 34 449 385 385), lower := (rows 35 194 13 56 84 34 64 128 256), losses := [] }

theorem u20161 : Upper (D 7) (R 7) [34,192,9,48,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20161 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20162 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 84 160 323 387 259), lower := (rows 35 194 13 56 84 160 64 128 256), losses := [] }

theorem u20162 : Upper (D 7) (R 7) [34,192,9,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20162 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20163 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 210, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(4,5)], upper := (rows 35 194 13 56 84 288 195 131 387), lower := (rows 35 194 13 56 84 288 64 128 256), losses := [] }

theorem u20163 : Upper (D 7) (R 7) [34,192,9,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20163 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20164 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 56 273 34 196 196 452), lower := (rows 35 194 13 56 273 34 64 128 256), losses := [] }

theorem u20164 : Upper (D 7) (R 7) [34,192,9,48,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20164 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20165 : PairBound 9 := { available := 194, camps := [{ cop := 4, region := 44, targets := 194 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 35 194 13 56 273 36 194 194 450), lower := (rows 35 194 13 56 273 36 64 128 256), losses := [] }

theorem u20165 : Upper (D 7) (R 7) [34,192,9,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20165 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20166 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 56 273 96 198 134 390), lower := (rows 35 194 13 56 273 96 64 128 256), losses := [] }

theorem u20166 : Upper (D 7) (R 7) [34,192,9,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20166 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20167 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 56 274 33 196 196 452), lower := (rows 35 194 13 56 274 33 64 128 256), losses := [] }

theorem u20167 : Upper (D 7) (R 7) [34,192,9,48,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20167 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20168 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 45, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 194 13 56 274 36 193 193 449), lower := (rows 35 194 13 56 274 36 64 128 256), losses := [] }

theorem u20168 : Upper (D 7) (R 7) [34,192,9,48,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20168 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20169 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 56 274 96 197 133 389), lower := (rows 35 194 13 56 274 96 64 128 256), losses := [] }

theorem u20169 : Upper (D 7) (R 7) [34,192,9,48,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20169 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20170 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 276 33 194 194 450), lower := (rows 35 194 13 56 276 33 64 128 256), losses := [] }

theorem u20170 : Upper (D 7) (R 7) [34,192,9,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20170 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20171 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 56 276 34 193 193 449), lower := (rows 35 194 13 56 276 34 64 128 256), losses := [] }

theorem u20171 : Upper (D 7) (R 7) [34,192,9,48,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20171 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20172 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 56 276 96 195 131 387), lower := (rows 35 194 13 56 276 96 64 128 256), losses := [] }

theorem u20172 : Upper (D 7) (R 7) [34,192,9,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20172 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20173 : PairBound 9 := { available := 134, camps := [{ cop := 2, region := 466, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 336 33 198 134 390), lower := (rows 35 194 13 56 336 33 64 128 256), losses := [] }

theorem u20173 : Upper (D 7) (R 7) [34,192,9,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20173 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20174 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 56 336 34 197 133 389), lower := (rows 35 194 13 56 336 34 64 128 256), losses := [] }

theorem u20174 : Upper (D 7) (R 7) [34,192,9,48,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20174 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20175 : Route 9 := (fun mask => (mask,id))

def c20175 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20175 : Upper (D 7) (R 7) [34,192,9,48,320,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,48,320,4] 13 (by decide) (choices 1) [1,2,128] r20175 c20175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5575
  · exact u5576
  · exact u5577

def b20176 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 336 160 71 135 263), lower := (rows 35 194 13 56 336 160 64 128 256), losses := [] }

theorem u20176 : Upper (D 7) (R 7) [34,192,9,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20176 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20177 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 76 145 34 368 432 304), lower := (rows 35 194 13 76 145 34 64 128 256), losses := [] }

theorem u20177 : Upper (D 7) (R 7) [34,192,9,68,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20177 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20178 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 13 76 145 48 354 418 290), lower := (rows 35 194 13 76 145 48 64 128 256), losses := [] }

theorem u20178 : Upper (D 7) (R 7) [34,192,9,68,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20178 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20179 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 194 13 76 145 288 114 178 306), lower := (rows 35 194 13 76 145 288 64 128 256), losses := [] }

theorem u20179 : Upper (D 7) (R 7) [34,192,9,68,129,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20179 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20180 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 76 176 33 338 402 274), lower := (rows 35 194 13 76 176 33 64 128 256), losses := [] }

theorem u20180 : Upper (D 7) (R 7) [34,192,9,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20180 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20181 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 76 176 34 337 401 273), lower := (rows 35 194 13 76 176 34 64 128 256), losses := [] }

theorem u20181 : Upper (D 7) (R 7) [34,192,9,68,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20181 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20182 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 13 76 176 48 323 387 259), lower := (rows 35 194 13 76 176 48 64 128 256), losses := [] }

theorem u20182 : Upper (D 7) (R 7) [34,192,9,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20182 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20183 : Route 9 := (fun mask => (mask,id))

def c20183 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20183 : Upper (D 7) (R 7) [34,192,9,68,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,68,160,256] 13 (by decide) (choices 1) [1,2,16] r20183 c20183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5578
  · exact u5579
  · exact u5580

def b20184 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 76 273 34 240 176 432), lower := (rows 35 194 13 76 273 34 64 128 256), losses := [] }

theorem u20184 : Upper (D 7) (R 7) [34,192,9,68,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20184 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20185 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 194, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 194 13 76 273 48 226 162 418), lower := (rows 35 194 13 76 273 48 64 128 256), losses := [] }

theorem u20185 : Upper (D 7) (R 7) [34,192,9,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20185 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20186 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 76 273 160 114 178 306), lower := (rows 35 194 13 76 273 160 64 128 256), losses := [] }

theorem u20186 : Upper (D 7) (R 7) [34,192,9,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20186 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20187 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 76 274 33 240 176 432), lower := (rows 35 194 13 76 274 33 64 128 256), losses := [] }

theorem u20187 : Upper (D 7) (R 7) [34,192,9,68,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20187 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20188 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 204, targets := 2 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 13 76 274 48 225 161 417), lower := (rows 35 194 13 76 274 48 64 128 256), losses := [] }

theorem u20188 : Upper (D 7) (R 7) [34,192,9,68,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20188 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20189 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 76 274 160 113 177 305), lower := (rows 35 194 13 76 274 160 64 128 256), losses := [] }

theorem u20189 : Upper (D 7) (R 7) [34,192,9,68,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20189 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20190 : PairBound 9 := { available := 146, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 76 304 33 210 146 402), lower := (rows 35 194 13 76 304 33 64 128 256), losses := [] }

theorem u20190 : Upper (D 7) (R 7) [34,192,9,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20190 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20191 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 76 304 34 209 145 401), lower := (rows 35 194 13 76 304 34 64 128 256), losses := [] }

theorem u20191 : Upper (D 7) (R 7) [34,192,9,68,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20191 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20192 : PairBound 9 := { available := 131, camps := [{ cop := 8, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 13 76 304 48 195 131 387), lower := (rows 35 194 13 76 304 48 64 128 256), losses := [] }

theorem u20192 : Upper (D 7) (R 7) [34,192,9,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20192 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20193 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 76 304 160 83 147 275), lower := (rows 35 194 13 76 304 160 64 128 256), losses := [] }

theorem u20193 : Upper (D 7) (R 7) [34,192,9,68,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20193 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20194 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 45, targets := 128 },{ cop := 0, region := 466, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 76 400 33 114 178 306), lower := (rows 35 194 13 76 400 33 64 128 256), losses := [] }

theorem u20194 : Upper (D 7) (R 7) [34,192,9,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20194 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20195 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 76 400 34 113 177 305), lower := (rows 35 194 13 76 400 34 64 128 256), losses := [] }

theorem u20195 : Upper (D 7) (R 7) [34,192,9,68,384,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20195 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20196 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 76, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 13 76 400 48 99 163 291), lower := (rows 35 194 13 76 400 48 64 128 256), losses := [] }

theorem u20196 : Upper (D 7) (R 7) [34,192,9,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20196 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20197 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 22 33 480 416 416), lower := (rows 35 194 13 88 22 33 64 128 256), losses := [] }

theorem u20197 : Upper (D 7) (R 7) [34,192,9,80,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20197 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20198 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 22 160 353 417 289), lower := (rows 35 194 13 88 22 160 64 128 256), losses := [] }

theorem u20198 : Upper (D 7) (R 7) [34,192,9,80,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20198 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20199 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(2,6),(3,1)], upper := (rows 35 194 13 88 22 288 225 161 417), lower := (rows 35 194 13 88 22 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 309 69 133 261), good := (rows 481 192 493 120 508 288 64 128 288) },{ target := 6, region := (rows 19 2 12 8 16 319 0 159 287), good := (rows 419 419 429 445 439 288 0 128 288) }] }

theorem u20199 : Upper (D 7) (R 7) [34,192,9,80,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20199 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20200 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 145 34 356 420 292), lower := (rows 35 194 13 88 145 34 64 128 256), losses := [] }

theorem u20200 : Upper (D 7) (R 7) [34,192,9,80,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20201 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 35 194 13 88 145 36 354 418 290), lower := (rows 35 194 13 88 145 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 194 494 90 474 486 64 128 256) }] }

theorem u20201 : Upper (D 7) (R 7) [34,192,9,80,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20201 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20202 : Route 9 := (fun mask => (mask,id))

def c20202 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20202 : Upper (D 7) (R 7) [34,192,9,80,129,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,129,256] 13 (by decide) (choices 1) [2,4,32] r20202 c20202
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5581
  · exact u5582
  · exact u5583

def b20203 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 450, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 88 148 33 354 418 290), lower := (rows 35 194 13 88 148 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 194 478 88 158 482 64 128 256) }] }

theorem u20203 : Upper (D 7) (R 7) [34,192,9,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20204 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 148 34 353 417 289), lower := (rows 35 194 13 88 148 34 64 128 256), losses := [] }

theorem u20204 : Upper (D 7) (R 7) [34,192,9,80,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20205 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 13 88 148 288 99 163 291), lower := (rows 35 194 13 88 148 288 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 20 295 0 131 259), good := (rows 419 419 445 24 180 288 0 128 288) }] }

theorem u20205 : Upper (D 7) (R 7) [34,192,9,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20205 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20206 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 2, region := 450, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 13 88 176 33 326 390 262), lower := (rows 35 194 13 88 176 33 64 128 256), losses := [] }

theorem u20206 : Upper (D 7) (R 7) [34,192,9,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20207 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 56, targets := 1 }], pairs := [(2,1),(3,0),(3,1),(4,1)], upper := (rows 35 194 13 88 176 34 325 389 261), lower := (rows 35 194 13 88 176 34 64 128 256), losses := [] }

theorem u20207 : Upper (D 7) (R 7) [34,192,9,80,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20208 : Route 9 := (fun mask => (mask,id))

def c20208 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u20208 : Upper (D 7) (R 7) [34,192,9,80,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160,4] 13 (by decide) (choices 1) [1,2,256] r20208 c20208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5584
  · exact u5585
  · exact u5586

def r20209 : Route 9 := (fun mask => (mask,id))

def c20209 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20209 : Upper (D 7) (R 7) [34,192,9,80,160,256] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,160,256] 13 (by decide) (choices 1) [1,2,4] r20209 c20209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5587
  · exact u5588
  · exact u5589

def b20210 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 273 34 228 164 420), lower := (rows 35 194 13 88 273 34 64 128 256), losses := [] }

theorem u20210 : Upper (D 7) (R 7) [34,192,9,80,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20211 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 35 194 13 88 273 36 226 162 418), lower := (rows 35 194 13 88 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 194 494 90 474 486 64 128 256) }] }

theorem u20211 : Upper (D 7) (R 7) [34,192,9,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20211 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20212 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 273 160 102 166 294), lower := (rows 35 194 13 88 273 160 64 128 256), losses := [] }

theorem u20212 : Upper (D 7) (R 7) [34,192,9,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20213 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 35 194 13 88 274 33 228 164 420), lower := (rows 35 194 13 88 274 33 64 128 256), losses := [{ target := 6, region := (rows 19 2 12 8 16 63 0 140 268), good := (rows 35 163 429 445 307 33 0 128 256) },{ target := 7, region := (rows 19 2 12 8 16 63 64 0 256), good := (rows 35 99 45 125 307 33 64 0 256) }] }

theorem u20213 : Upper (D 7) (R 7) [34,192,9,80,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20214 : Route 9 := (fun mask => (mask,id))

def c20214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20214 : Upper (D 7) (R 7) [34,192,9,80,258,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,258,4] 13 (by decide) (choices 1) [1,32,128] r20214 c20214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5590
  · exact u5591
  · exact u5592

def b20215 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 274 160 101 165 293), lower := (rows 35 194 13 88 274 160 64 128 256), losses := [] }

theorem u20215 : Upper (D 7) (R 7) [34,192,9,80,258,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20216 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 88 276 33 226 162 418), lower := (rows 35 194 13 88 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 194 478 88 286 482 64 128 256) }] }

theorem u20216 : Upper (D 7) (R 7) [34,192,9,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20217 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 88 276 34 225 161 417), lower := (rows 35 194 13 88 276 34 64 128 256), losses := [] }

theorem u20217 : Upper (D 7) (R 7) [34,192,9,80,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20218 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 276 160 99 163 291), lower := (rows 35 194 13 88 276 160 64 128 256), losses := [] }

theorem u20218 : Upper (D 7) (R 7) [34,192,9,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20218 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20219 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 13 88 304 33 198 134 390), lower := (rows 35 194 13 88 304 33 64 128 256), losses := [] }

theorem u20219 : Upper (D 7) (R 7) [34,192,9,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20219 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20219
end Delivery.IrregularNine14.P07
