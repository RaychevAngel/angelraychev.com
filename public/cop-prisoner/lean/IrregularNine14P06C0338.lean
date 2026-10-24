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

def b20280 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 133 104 273 36 90 154 282), lower := (rows 35 70 133 104 273 36 64 128 256), losses := [] }

theorem u20280 : Upper (D 6) (R 6) [34,68,129,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20281 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 104 273 40 86 150 278), lower := (rows 35 70 133 104 273 40 64 128 256), losses := [] }

theorem u20281 : Upper (D 6) (R 6) [34,68,129,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20281 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20282 : Route 9 := (fun mask => (mask,id))

def c20282 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20282 : Upper (D 6) (R 6) [34,68,129,96,257,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257,16] 13 (by decide) (choices 1) [2,4,8] r20282 c20282
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6028
  · exact u6029
  · exact u6030

def b20283 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 133 104 274 33 92 156 284), lower := (rows 35 70 133 104 274 33 64 128 256), losses := [] }

theorem u20283 : Upper (D 6) (R 6) [34,68,129,96,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20284 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 133 104 274 36 89 153 281), lower := (rows 35 70 133 104 274 36 64 128 256), losses := [] }

theorem u20284 : Upper (D 6) (R 6) [34,68,129,96,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20285 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 104 274 40 85 149 277), lower := (rows 35 70 133 104 274 40 64 128 256), losses := [] }

theorem u20285 : Upper (D 6) (R 6) [34,68,129,96,258,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20285 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20286 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 133 104 274 48 77 141 269), lower := (rows 35 70 133 104 274 48 64 128 256), losses := [] }

theorem u20286 : Upper (D 6) (R 6) [34,68,129,96,258,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20286 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20287 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 133 104 276 33 90 154 282), lower := (rows 35 70 133 104 276 33 64 128 256), losses := [] }

theorem u20287 : Upper (D 6) (R 6) [34,68,129,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20288 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 276 34 89 153 281), lower := (rows 35 70 133 104 276 34 64 128 256), losses := [] }

theorem u20288 : Upper (D 6) (R 6) [34,68,129,96,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20289 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 470, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 104 276 40 83 147 275), lower := (rows 35 70 133 104 276 40 64 128 256), losses := [] }

theorem u20289 : Upper (D 6) (R 6) [34,68,129,96,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20289 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20290 : Route 9 := (fun mask => (mask,id))

def c20290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20290 : Upper (D 6) (R 6) [34,68,129,96,260,16] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,260,16] 13 (by decide) (choices 1) [1,2,8] r20290 c20290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6031
  · exact u6032
  · exact u6033

def b20291 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 41, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 133 104 280 33 86 150 278), lower := (rows 35 70 133 104 280 33 64 128 256), losses := [] }

theorem u20291 : Upper (D 6) (R 6) [34,68,129,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20292 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 70 133 104 280 34 85 149 277), lower := (rows 35 70 133 104 280 34 64 128 256), losses := [] }

theorem u20292 : Upper (D 6) (R 6) [34,68,129,96,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20293 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 344, targets := 4 },{ cop := 1, region := 40, targets := 1 }], pairs := [(3,0),(3,2),(4,2)], upper := (rows 35 70 133 104 280 36 83 147 275), lower := (rows 35 70 133 104 280 36 64 128 256), losses := [] }

theorem u20293 : Upper (D 6) (R 6) [34,68,129,96,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20294 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 133 104 280 48 71 135 263), lower := (rows 35 70 133 104 280 48 64 128 256), losses := [] }

theorem u20294 : Upper (D 6) (R 6) [34,68,129,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20294 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20295 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 13 56 33 336 464 336), lower := (rows 35 70 134 13 56 33 64 128 256), losses := [] }

theorem u20295 : Upper (D 6) (R 6) [34,68,130,5,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20296 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 13 56 48 321 449 321), lower := (rows 35 70 134 13 56 48 64 128 256), losses := [] }

theorem u20296 : Upper (D 6) (R 6) [34,68,130,5,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20296 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20297 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 13 56 96 337 401 273), lower := (rows 35 70 134 13 56 96 64 128 256), losses := [] }

theorem u20297 : Upper (D 6) (R 6) [34,68,130,5,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20298 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 56 288 81 209 337), lower := (rows 35 70 134 13 56 288 64 128 256), losses := [] }

theorem u20298 : Upper (D 6) (R 6) [34,68,130,5,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20298 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20299 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 81 40 368 432 304), lower := (rows 35 70 134 13 81 40 64 128 256), losses := [] }

theorem u20299 : Upper (D 6) (R 6) [34,68,130,5,65,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20299 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20300 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 134 13 81 48 360 424 296), lower := (rows 35 70 134 13 81 48 64 128 256), losses := [] }

theorem u20300 : Upper (D 6) (R 6) [34,68,130,5,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20300 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20301 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 81 288 120 184 312), lower := (rows 35 70 134 13 81 288 64 128 256), losses := [] }

theorem u20301 : Upper (D 6) (R 6) [34,68,130,5,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20301 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20302 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 70 134 13 88 33 368 432 304), lower := (rows 35 70 134 13 88 33 64 128 256), losses := [] }

theorem u20302 : Upper (D 6) (R 6) [34,68,130,5,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20302 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20303 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 134 13 88 48 353 417 289), lower := (rows 35 70 134 13 88 48 64 128 256), losses := [] }

theorem u20303 : Upper (D 6) (R 6) [34,68,130,5,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20303 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20304 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 88 288 113 177 305), lower := (rows 35 70 134 13 88 288 64 128 256), losses := [] }

theorem u20304 : Upper (D 6) (R 6) [34,68,130,5,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20304 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20305 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 70 134 13 112 33 344 408 280), lower := (rows 35 70 134 13 112 33 64 128 256), losses := [] }

theorem u20305 : Upper (D 6) (R 6) [34,68,130,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20305 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20306 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 112 40 337 401 273), lower := (rows 35 70 134 13 112 40 64 128 256), losses := [] }

theorem u20306 : Upper (D 6) (R 6) [34,68,130,5,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20306 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20307 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 13 112 48 329 393 265), lower := (rows 35 70 134 13 112 48 64 128 256), losses := [] }

theorem u20307 : Upper (D 6) (R 6) [34,68,130,5,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20307 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20308 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 112 288 89 153 281), lower := (rows 35 70 134 13 112 288 64 128 256), losses := [] }

theorem u20308 : Upper (D 6) (R 6) [34,68,130,5,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20308 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20309 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 273 40 112 240 368), lower := (rows 35 70 134 13 273 40 64 128 256), losses := [] }

theorem u20309 : Upper (D 6) (R 6) [34,68,130,5,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20309 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20310 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 273 48 104 232 360), lower := (rows 35 70 134 13 273 48 64 128 256), losses := [] }

theorem u20310 : Upper (D 6) (R 6) [34,68,130,5,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20310 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20311 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 13 273 96 120 184 312), lower := (rows 35 70 134 13 273 96 64 128 256), losses := [] }

theorem u20311 : Upper (D 6) (R 6) [34,68,130,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20311 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20312 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 70 134 13 280 33 112 240 368), lower := (rows 35 70 134 13 280 33 64 128 256), losses := [] }

theorem u20312 : Upper (D 6) (R 6) [34,68,130,5,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20312 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20313 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 368, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 280 48 97 225 353), lower := (rows 35 70 134 13 280 48 64 128 256), losses := [] }

theorem u20313 : Upper (D 6) (R 6) [34,68,130,5,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20313 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20314 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 13 280 96 113 177 305), lower := (rows 35 70 134 13 280 96 64 128 256), losses := [] }

theorem u20314 : Upper (D 6) (R 6) [34,68,130,5,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20314 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20315 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 70 134 13 304 33 88 216 344), lower := (rows 35 70 134 13 304 33 64 128 256), losses := [] }

theorem u20315 : Upper (D 6) (R 6) [34,68,130,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20315 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20316 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 304 40 81 209 337), lower := (rows 35 70 134 13 304 40 64 128 256), losses := [] }

theorem u20316 : Upper (D 6) (R 6) [34,68,130,5,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20316 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20317 : PairBound 9 := { available := 73, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 70 134 13 304 48 73 201 329), lower := (rows 35 70 134 13 304 48 64 128 256), losses := [] }

theorem u20317 : Upper (D 6) (R 6) [34,68,130,5,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20317 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20318 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 13 304 96 89 153 281), lower := (rows 35 70 134 13 304 96 64 128 256), losses := [] }

theorem u20318 : Upper (D 6) (R 6) [34,68,130,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20318 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20319 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 41, targets := 64 },{ cop := 3, region := 368, targets := 2 }], pairs := [(0,6),(3,6),(4,1)], upper := (rows 35 70 134 13 336 33 120 184 312), lower := (rows 35 70 134 13 336 33 64 128 256), losses := [] }

theorem u20319 : Upper (D 6) (R 6) [34,68,130,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20319 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20320 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 336, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 70 134 13 336 40 113 177 305), lower := (rows 35 70 134 13 336 40 64 128 256), losses := [] }

theorem u20320 : Upper (D 6) (R 6) [34,68,130,5,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20320 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20321 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 134 13 336 48 105 169 297), lower := (rows 35 70 134 13 336 48 64 128 256), losses := [] }

theorem u20321 : Upper (D 6) (R 6) [34,68,130,5,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20321 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20322 : PairBound 9 := { available := 352, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 134 25 28 33 352 480 352), lower := (rows 35 70 134 25 28 33 64 128 256), losses := [] }

theorem u20322 : Upper (D 6) (R 6) [34,68,130,17,12,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20322 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20323 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 25 28 96 353 417 289), lower := (rows 35 70 134 25 28 96 64 128 256), losses := [] }

theorem u20323 : Upper (D 6) (R 6) [34,68,130,17,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20323 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20324 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 289, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 134 25 28 288 97 225 353), lower := (rows 35 70 134 25 28 288 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 319 95 159 287), good := (rows 483 483 483 505 505 288 64 128 288) }] }

theorem u20324 : Upper (D 6) (R 6) [34,68,130,17,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20324 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20325 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 52 33 328 456 328), lower := (rows 35 70 134 25 52 33 64 128 256), losses := [] }

theorem u20325 : Upper (D 6) (R 6) [34,68,130,17,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20325 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20326 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 57, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 70 134 25 52 40 321 449 321), lower := (rows 35 70 134 25 52 40 64 128 256), losses := [] }

theorem u20326 : Upper (D 6) (R 6) [34,68,130,17,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20326 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20327 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 25 52 96 329 393 265), lower := (rows 35 70 134 25 52 96 64 128 256), losses := [] }

theorem u20327 : Upper (D 6) (R 6) [34,68,130,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20328 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 25 52 288 73 201 329), lower := (rows 35 70 134 25 52 288 64 128 256), losses := [] }

theorem u20328 : Upper (D 6) (R 6) [34,68,130,17,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20328 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20329 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2),(4,2)], upper := (rows 35 70 134 25 88 33 356 420 292), lower := (rows 35 70 134 25 88 33 64 128 256), losses := [] }

theorem u20329 : Upper (D 6) (R 6) [34,68,130,17,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20329 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20330 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 25 88 36 353 417 289), lower := (rows 35 70 134 25 88 36 64 128 256), losses := [] }

theorem u20330 : Upper (D 6) (R 6) [34,68,130,17,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20330 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20331 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 134 25 88 288 101 165 293), lower := (rows 35 70 134 25 88 288 64 128 256), losses := [] }

theorem u20331 : Upper (D 6) (R 6) [34,68,130,17,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20331 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20332 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 454, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 112 33 332 396 268), lower := (rows 35 70 134 25 112 33 64 128 256), losses := [] }

theorem u20332 : Upper (D 6) (R 6) [34,68,130,17,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20332 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20333 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2),(4,1)], upper := (rows 35 70 134 25 112 36 329 393 265), lower := (rows 35 70 134 25 112 36 64 128 256), losses := [] }

theorem u20333 : Upper (D 6) (R 6) [34,68,130,17,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20333 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20334 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 57, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 35 70 134 25 112 40 325 389 261), lower := (rows 35 70 134 25 112 40 64 128 256), losses := [] }

theorem u20334 : Upper (D 6) (R 6) [34,68,130,17,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20334 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20335 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 70 134 25 112 288 77 141 269), lower := (rows 35 70 134 25 112 288 64 128 256), losses := [] }

theorem u20335 : Upper (D 6) (R 6) [34,68,130,17,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20335 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20336 : PairBound 9 := { available := 104, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 35 70 134 25 276 33 104 232 360), lower := (rows 35 70 134 25 276 33 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 24 16 63 88 152 280), good := (rows 35 99 163 505 505 33 64 128 256) }] }

theorem u20336 : Upper (D 6) (R 6) [34,68,130,17,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r20337 : Route 9 := (fun mask => (mask,id))

def c20337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20337 : Upper (D 6) (R 6) [34,68,130,17,260,8] 13 := by
  apply FastRouting.sound _ _ [34,68,130,17,260,8] 13 (by decide) (choices 1) [1,32] r20337 c20337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6034
  · exact u6035

def b20338 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 70 134 25 276 96 105 169 297), lower := (rows 35 70 134 25 276 96 64 128 256), losses := [] }

theorem u20338 : Upper (D 6) (R 6) [34,68,130,17,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b20339 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 198, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(1,0),(2,0)], upper := (rows 35 70 134 25 280 33 100 228 356), lower := (rows 35 70 134 25 280 33 64 128 256), losses := [] }

theorem u20339 : Upper (D 6) (R 6) [34,68,130,17,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b20339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u20339
end Delivery.IrregularNine14.P06
