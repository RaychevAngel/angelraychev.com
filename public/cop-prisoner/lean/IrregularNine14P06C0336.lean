import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0100

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20160 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 56, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 133 26 112 36 329 393 265), lower := (rows 35 70 133 26 112 36 64 128 256), losses := [] }

theorem u20160 : Upper (D 6) (R 6) [34,68,129,18,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20161 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 133 26 112 40 325 389 261), lower := (rows 35 70 133 26 112 40 64 128 256), losses := [] }

theorem u20161 : Upper (D 6) (R 6) [34,68,129,18,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20161 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20162 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 133 26 112 288 77 141 269), lower := (rows 35 70 133 26 112 288 64 128 256), losses := [] }

theorem u20162 : Upper (D 6) (R 6) [34,68,129,18,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20162 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20163 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 26 273 36 104 232 360), lower := (rows 35 70 133 26 273 36 64 128 256), losses := [] }

theorem u20163 : Upper (D 6) (R 6) [34,68,129,18,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20164 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 133 26 273 40 100 228 356), lower := (rows 35 70 133 26 273 40 64 128 256), losses := [] }

theorem u20164 : Upper (D 6) (R 6) [34,68,129,18,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20164 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20165 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 273 96 108 172 300), lower := (rows 35 70 133 26 273 96 64 128 256), losses := [] }

theorem u20165 : Upper (D 6) (R 6) [34,68,129,18,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20165 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20166 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 26 276 33 104 232 360), lower := (rows 35 70 133 26 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 30 20 32 65 129 257), good := (rows 490 94 478 26 286 480 64 128 256) }] }

theorem u20166 : Upper (D 6) (R 6) [34,68,129,18,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20166 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20167 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 133 26 276 40 97 225 353), lower := (rows 35 70 133 26 276 40 64 128 256), losses := [] }

theorem u20167 : Upper (D 6) (R 6) [34,68,129,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20167 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20168 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 276 96 105 169 297), lower := (rows 35 70 133 26 276 96 64 128 256), losses := [] }

theorem u20168 : Upper (D 6) (R 6) [34,68,129,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20168 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20169 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 2 }], pairs := [(0,2),(0,6),(2,1)], upper := (rows 35 70 133 26 280 33 100 228 356), lower := (rows 35 70 133 26 280 33 64 128 256), losses := [] }

theorem u20169 : Upper (D 6) (R 6) [34,68,129,18,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20170 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,2),(4,2)], upper := (rows 35 70 133 26 280 36 97 225 353), lower := (rows 35 70 133 26 280 36 64 128 256), losses := [] }

theorem u20170 : Upper (D 6) (R 6) [34,68,129,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20171 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 280 96 101 165 293), lower := (rows 35 70 133 26 280 96 64 128 256), losses := [] }

theorem u20171 : Upper (D 6) (R 6) [34,68,129,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20172 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 26 304 33 76 204 332), lower := (rows 35 70 133 26 304 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 13 17 32 70 134 262), good := (rows 506 462 478 474 304 56 64 128 256) }] }

theorem u20172 : Upper (D 6) (R 6) [34,68,129,18,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20172 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20173 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 26 304 36 73 201 329), lower := (rows 35 70 133 26 304 36 64 128 256), losses := [] }

theorem u20173 : Upper (D 6) (R 6) [34,68,129,18,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20174 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 133 26 304 40 69 197 325), lower := (rows 35 70 133 26 304 40 64 128 256), losses := [] }

theorem u20174 : Upper (D 6) (R 6) [34,68,129,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20174 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20175 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 26 304 96 77 141 269), lower := (rows 35 70 133 26 304 96 64 128 256), losses := [] }

theorem u20175 : Upper (D 6) (R 6) [34,68,129,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20175 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20176 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,2),(0,6),(2,6)], upper := (rows 35 70 133 26 336 33 108 172 300), lower := (rows 35 70 133 26 336 33 64 128 256), losses := [] }

theorem u20176 : Upper (D 6) (R 6) [34,68,129,18,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20177 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 35 70 133 26 336 36 105 169 297), lower := (rows 35 70 133 26 336 36 64 128 256), losses := [] }

theorem u20177 : Upper (D 6) (R 6) [34,68,129,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20178 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 70 133 26 336 40 101 165 293), lower := (rows 35 70 133 26 336 40 64 128 256), losses := [] }

theorem u20178 : Upper (D 6) (R 6) [34,68,129,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20178 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20179 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 81 34 360 424 296), lower := (rows 35 70 133 28 81 34 64 128 256), losses := [] }

theorem u20179 : Upper (D 6) (R 6) [34,68,129,20,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20179 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20180 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 0, region := 388, targets := 64 }], pairs := [(2,6),(4,2)], upper := (rows 35 70 133 28 81 40 354 418 290), lower := (rows 35 70 133 28 81 40 64 128 256), losses := [] }

theorem u20180 : Upper (D 6) (R 6) [34,68,129,20,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20180 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20181 : Route 9 := (fun mask => (mask,id))

def c20181 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20181 : Upper (D 6) (R 6) [34,68,129,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,65,256] 13 (by decide) (choices 1) [2,8,32] r20181 c20181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6010
  · exact u6011
  · exact u6012

def b20182 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 3, region := 322, targets := 1 }], pairs := [(0,2),(1,0),(4,2)], upper := (rows 35 70 133 28 112 33 330 394 266), lower := (rows 35 70 133 28 112 33 64 128 256), losses := [] }

theorem u20182 : Upper (D 6) (R 6) [34,68,129,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20182 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20183 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 112 34 329 393 265), lower := (rows 35 70 133 28 112 34 64 128 256), losses := [] }

theorem u20183 : Upper (D 6) (R 6) [34,68,129,20,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20184 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 28 112 40 323 387 259), lower := (rows 35 70 133 28 112 40 64 128 256), losses := [] }

theorem u20184 : Upper (D 6) (R 6) [34,68,129,20,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20184 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20185 : Route 9 := (fun mask => (mask,id))

def c20185 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20185 : Upper (D 6) (R 6) [34,68,129,20,96,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,20,96,256] 13 (by decide) (choices 1) [1,2,8] r20185 c20185
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6013
  · exact u6014
  · exact u6015

def b20186 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 273 34 104 232 360), lower := (rows 35 70 133 28 273 34 64 128 256), losses := [] }

theorem u20186 : Upper (D 6) (R 6) [34,68,129,20,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20186 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20187 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(4,2)], upper := (rows 35 70 133 28 273 40 98 226 354), lower := (rows 35 70 133 28 273 40 64 128 256), losses := [] }

theorem u20187 : Upper (D 6) (R 6) [34,68,129,20,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20187 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20188 : PairBound 9 := { available := 42, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 28 273 96 106 170 298), lower := (rows 35 70 133 28 273 96 64 128 256), losses := [] }

theorem u20188 : Upper (D 6) (R 6) [34,68,129,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20188 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20189 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 28 274 33 104 232 360), lower := (rows 35 70 133 28 274 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 21 32 65 129 257), good := (rows 506 94 478 30 282 496 64 128 256) }] }

theorem u20189 : Upper (D 6) (R 6) [34,68,129,20,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20189 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20190 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 196, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,2)], upper := (rows 35 70 133 28 274 40 97 225 353), lower := (rows 35 70 133 28 274 40 64 128 256), losses := [] }

theorem u20190 : Upper (D 6) (R 6) [34,68,129,20,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20190 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20191 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 28 274 96 105 169 297), lower := (rows 35 70 133 28 274 96 64 128 256), losses := [] }

theorem u20191 : Upper (D 6) (R 6) [34,68,129,20,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20191 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20192 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 33, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 28 280 33 98 226 354), lower := (rows 35 70 133 28 280 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 21 32 65 129 257), good := (rows 506 94 478 30 280 496 64 128 256) }] }

theorem u20192 : Upper (D 6) (R 6) [34,68,129,20,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20193 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 280 34 97 225 353), lower := (rows 35 70 133 28 280 34 64 128 256), losses := [] }

theorem u20193 : Upper (D 6) (R 6) [34,68,129,20,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20193 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20194 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 28 280 96 99 163 291), lower := (rows 35 70 133 28 280 96 64 128 256), losses := [] }

theorem u20194 : Upper (D 6) (R 6) [34,68,129,20,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20195 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 28 304 33 74 202 330), lower := (rows 35 70 133 28 304 33 64 128 256), losses := [] }

theorem u20195 : Upper (D 6) (R 6) [34,68,129,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20195 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20196 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 304 34 73 201 329), lower := (rows 35 70 133 28 304 34 64 128 256), losses := [] }

theorem u20196 : Upper (D 6) (R 6) [34,68,129,20,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20196 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20197 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 28 304 40 67 195 323), lower := (rows 35 70 133 28 304 40 64 128 256), losses := [] }

theorem u20197 : Upper (D 6) (R 6) [34,68,129,20,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20197 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20198 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 28 304 96 75 139 267), lower := (rows 35 70 133 28 304 96 64 128 256), losses := [] }

theorem u20198 : Upper (D 6) (R 6) [34,68,129,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20198 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20199 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(1,0)], upper := (rows 35 70 133 28 336 33 106 170 298), lower := (rows 35 70 133 28 336 33 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 14 53 32 65 129 257), good := (rows 506 94 478 30 336 496 64 128 256) }] }

theorem u20199 : Upper (D 6) (R 6) [34,68,129,20,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20199 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20200 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 28 336 34 105 169 297), lower := (rows 35 70 133 28 336 34 64 128 256), losses := [] }

theorem u20200 : Upper (D 6) (R 6) [34,68,129,20,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20200 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20201 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6),(4,2)], upper := (rows 35 70 133 28 336 40 99 163 291), lower := (rows 35 70 133 28 336 40 64 128 256), losses := [] }

theorem u20201 : Upper (D 6) (R 6) [34,68,129,20,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20201 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20202 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 44 81 34 344 408 280), lower := (rows 35 70 133 44 81 34 64 128 256), losses := [] }

theorem u20202 : Upper (D 6) (R 6) [34,68,129,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20202 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20203 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 81 40 338 402 274), lower := (rows 35 70 133 44 81 40 64 128 256), losses := [] }

theorem u20203 : Upper (D 6) (R 6) [34,68,129,36,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20203 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20204 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 44 81 48 330 394 266), lower := (rows 35 70 133 44 81 48 64 128 256), losses := [] }

theorem u20204 : Upper (D 6) (R 6) [34,68,129,36,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20204 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20205 : Route 9 := (fun mask => (mask,id))

def c20205 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20205 : Upper (D 6) (R 6) [34,68,129,36,65,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,65,256] 13 (by decide) (choices 1) [2,8,16] r20205 c20205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6016
  · exact u6017
  · exact u6018

def b20206 : PairBound 9 := { available := 274, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 133 44 88 33 338 402 274), lower := (rows 35 70 133 44 88 33 64 128 256), losses := [] }

theorem u20206 : Upper (D 6) (R 6) [34,68,129,36,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20206 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20207 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 44 88 34 337 401 273), lower := (rows 35 70 133 44 88 34 64 128 256), losses := [] }

theorem u20207 : Upper (D 6) (R 6) [34,68,129,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20207 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20208 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 88 48 323 387 259), lower := (rows 35 70 133 44 88 48 64 128 256), losses := [] }

theorem u20208 : Upper (D 6) (R 6) [34,68,129,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20208 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20209 : Route 9 := (fun mask => (mask,id))

def c20209 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20209 : Upper (D 6) (R 6) [34,68,129,36,72,256] 13 := by
  apply FastRouting.sound _ _ [34,68,129,36,72,256] 13 (by decide) (choices 1) [1,2,16] r20209 c20209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6019
  · exact u6020
  · exact u6021

def b20210 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 44 273 34 88 216 344), lower := (rows 35 70 133 44 273 34 64 128 256), losses := [] }

theorem u20210 : Upper (D 6) (R 6) [34,68,129,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20210 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20211 : PairBound 9 := { available := 82, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 273 40 82 210 338), lower := (rows 35 70 133 44 273 40 64 128 256), losses := [] }

theorem u20211 : Upper (D 6) (R 6) [34,68,129,36,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20211 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20212 : PairBound 9 := { available := 74, camps := [{ cop := 3, region := 66, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 133 44 273 48 74 202 330), lower := (rows 35 70 133 44 273 48 64 128 256), losses := [] }

theorem u20212 : Upper (D 6) (R 6) [34,68,129,36,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20212 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20213 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 44 273 96 90 154 282), lower := (rows 35 70 133 44 273 96 64 128 256), losses := [] }

theorem u20213 : Upper (D 6) (R 6) [34,68,129,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20213 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20214 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 133 44 274 33 88 216 344), lower := (rows 35 70 133 44 274 33 64 128 256), losses := [] }

theorem u20214 : Upper (D 6) (R 6) [34,68,129,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20214 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20215 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 44 274 40 81 209 337), lower := (rows 35 70 133 44 274 40 64 128 256), losses := [] }

theorem u20215 : Upper (D 6) (R 6) [34,68,129,36,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20215 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20216 : PairBound 9 := { available := 73, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 44 274 48 73 201 329), lower := (rows 35 70 133 44 274 48 64 128 256), losses := [] }

theorem u20216 : Upper (D 6) (R 6) [34,68,129,36,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20216 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20217 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 133 44 274 96 89 153 281), lower := (rows 35 70 133 44 274 96 64 128 256), losses := [] }

theorem u20217 : Upper (D 6) (R 6) [34,68,129,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20217 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20218 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 338, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 133 44 280 33 82 210 338), lower := (rows 35 70 133 44 280 33 64 128 256), losses := [] }

theorem u20218 : Upper (D 6) (R 6) [34,68,129,36,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20218 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20219 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 44 280 34 81 209 337), lower := (rows 35 70 133 44 280 34 64 128 256), losses := [] }

theorem u20219 : Upper (D 6) (R 6) [34,68,129,36,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20219 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20219
end Delivery.IrregularNine14.P06
