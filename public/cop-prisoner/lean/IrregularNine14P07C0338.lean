import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0093

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b20280 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 }], pairs := [(1,0),(2,6),(3,0)], upper := (rows 35 194 13 280 81 36 226 162 418), lower := (rows 35 194 13 280 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 55 4 24 16 36 101 165 293), good := (rows 482 194 494 282 474 486 64 128 256) },{ target := 6, region := (rows 1 2 20 24 16 60 0 129 257), good := (rows 419 130 429 316 445 36 0 128 256) }] }

theorem u20280 : Upper (D 7) (R 7) [34,192,9,272,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20280 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20281 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 81 160 102 166 294), lower := (rows 35 194 13 280 81 160 64 128 256), losses := [] }

theorem u20281 : Upper (D 7) (R 7) [34,192,9,272,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20282 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 194, targets := 1 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(3,0)], upper := (rows 35 194 13 280 84 33 226 162 418), lower := (rows 35 194 13 280 84 33 64 128 256), losses := [{ target := 0, region := (rows 0 39 4 12 20 32 97 161 289), good := (rows 482 194 478 280 94 482 64 128 256) }] }

theorem u20282 : Upper (D 7) (R 7) [34,192,9,272,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20283 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 280 84 34 225 161 417), lower := (rows 35 194 13 280 84 34 64 128 256), losses := [] }

theorem u20283 : Upper (D 7) (R 7) [34,192,9,272,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20284 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 84 160 99 163 291), lower := (rows 35 194 13 280 84 160 64 128 256), losses := [] }

theorem u20284 : Upper (D 7) (R 7) [34,192,9,272,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20284 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20285 : PairBound 9 := { available := 134, camps := [{ cop := 1, region := 49, targets := 128 },{ cop := 2, region := 194, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(4,7)], upper := (rows 35 194 13 280 112 33 198 134 390), lower := (rows 35 194 13 280 112 33 64 128 256), losses := [] }

theorem u20285 : Upper (D 7) (R 7) [34,192,9,272,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20286 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 280 112 34 197 133 389), lower := (rows 35 194 13 280 112 34 64 128 256), losses := [] }

theorem u20286 : Upper (D 7) (R 7) [34,192,9,272,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20287 : Route 9 := (fun mask => (mask,id))

def c20287 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20287 : Upper (D 7) (R 7) [34,192,9,272,96,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96,4] 13 (by decide) (choices 1) [1,2,128] r20287 c20287
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5608
  · exact u5609
  · exact u5610

def b20288 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 48, targets := 1 }], pairs := [(2,7),(3,7),(4,0),(4,7)], upper := (rows 35 194 13 280 112 160 71 135 263), lower := (rows 35 194 13 280 112 160 64 128 256), losses := [] }

theorem u20288 : Upper (D 7) (R 7) [34,192,9,272,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20289 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 22 33 208 208 464), lower := (rows 35 194 13 296 22 33 64 128 256), losses := [] }

theorem u20289 : Upper (D 7) (R 7) [34,192,9,288,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20290 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,1),(3,1)], upper := (rows 35 194 13 296 22 48 193 193 449), lower := (rows 35 194 13 296 22 48 64 128 256), losses := [] }

theorem u20290 : Upper (D 7) (R 7) [34,192,9,288,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20290 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20291 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,6),(3,6),(4,6)], upper := (rows 35 194 13 296 22 96 209 145 401), lower := (rows 35 194 13 296 22 96 64 128 256), losses := [] }

theorem u20291 : Upper (D 7) (R 7) [34,192,9,288,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20291 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20292 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 296 81 34 212 148 404), lower := (rows 35 194 13 296 81 34 64 128 256), losses := [] }

theorem u20292 : Upper (D 7) (R 7) [34,192,9,288,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20292 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20293 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 210, targets := 32 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(1,5),(4,5)], upper := (rows 35 194 13 296 81 36 210 146 402), lower := (rows 35 194 13 296 81 36 64 128 256), losses := [] }

theorem u20293 : Upper (D 7) (R 7) [34,192,9,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20293 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20294 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 1, region := 49, targets := 128 }], pairs := [(0,7),(2,6),(3,6)], upper := (rows 35 194 13 296 81 48 198 134 390), lower := (rows 35 194 13 296 81 48 64 128 256), losses := [] }

theorem u20294 : Upper (D 7) (R 7) [34,192,9,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20294 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20295 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 296 81 160 86 150 278), lower := (rows 35 194 13 296 81 160 64 128 256), losses := [] }

theorem u20295 : Upper (D 7) (R 7) [34,192,9,288,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20295 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20296 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 210, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 84 33 210 146 402), lower := (rows 35 194 13 296 84 33 64 128 256), losses := [] }

theorem u20296 : Upper (D 7) (R 7) [34,192,9,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20296 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20297 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 296 84 34 209 145 401), lower := (rows 35 194 13 296 84 34 64 128 256), losses := [] }

theorem u20297 : Upper (D 7) (R 7) [34,192,9,288,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20297 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20298 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 396, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5),(2,6),(3,6)], upper := (rows 35 194 13 296 84 48 195 131 387), lower := (rows 35 194 13 296 84 48 64 128 256), losses := [] }

theorem u20298 : Upper (D 7) (R 7) [34,192,9,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20299 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 296 84 160 83 147 275), lower := (rows 35 194 13 296 84 160 64 128 256), losses := [] }

theorem u20299 : Upper (D 7) (R 7) [34,192,9,288,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20299 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20300 : Route 9 := (fun mask => (mask,id))

def c20300 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u20300 : Upper (D 7) (R 7) [34,192,9,320,6,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,6,1] 13 (by decide) (choices 1) [16,32,128] r20300 c20300
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5611
  · exact u5612
  · exact u5613

def b20301 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 460, targets := 2 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1)], upper := (rows 35 194 13 328 22 48 225 161 417), lower := (rows 35 194 13 328 22 48 64 128 256), losses := [] }

theorem u20301 : Upper (D 7) (R 7) [34,192,9,320,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20301 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20302 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 22 160 113 177 305), lower := (rows 35 194 13 328 22 160 64 128 256), losses := [] }

theorem u20302 : Upper (D 7) (R 7) [34,192,9,320,6,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20302 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20303 : PairBound 9 := { available := 146, camps := [{ cop := 4, region := 458, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 328 52 33 210 146 402), lower := (rows 35 194 13 328 52 33 64 128 256), losses := [] }

theorem u20303 : Upper (D 7) (R 7) [34,192,9,320,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20304 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 328 52 34 209 145 401), lower := (rows 35 194 13 328 52 34 64 128 256), losses := [] }

theorem u20304 : Upper (D 7) (R 7) [34,192,9,320,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20305 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 194 13 328 52 48 195 131 387), lower := (rows 35 194 13 328 52 48 64 128 256), losses := [] }

theorem u20305 : Upper (D 7) (R 7) [34,192,9,320,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20305 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20306 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 52 160 83 147 275), lower := (rows 35 194 13 328 52 160 64 128 256), losses := [] }

theorem u20306 : Upper (D 7) (R 7) [34,192,9,320,36,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20306 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20307 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 328 145 34 116 180 308), lower := (rows 35 194 13 328 145 34 64 128 256), losses := [] }

theorem u20307 : Upper (D 7) (R 7) [34,192,9,320,129,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20307 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20308 : Route 9 := (fun mask => (mask,id))

def c20308 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20308 : Upper (D 7) (R 7) [34,192,9,320,129,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,129,4] 13 (by decide) (choices 1) [2,16,32] r20308 c20308
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5614
  · exact u5615
  · exact u5616

def b20309 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 49, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 13 328 145 48 102 166 294), lower := (rows 35 194 13 328 145 48 64 128 256), losses := [] }

theorem u20309 : Upper (D 7) (R 7) [34,192,9,320,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20309 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20310 : Route 9 := (fun mask => (mask,id))

def c20310 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20310 : Upper (D 7) (R 7) [34,192,9,320,132,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,132,1] 13 (by decide) (choices 1) [2,16,32] r20310 c20310
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5617
  · exact u5618
  · exact u5619

def b20311 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 328 148 34 113 177 305), lower := (rows 35 194 13 328 148 34 64 128 256), losses := [] }

theorem u20311 : Upper (D 7) (R 7) [34,192,9,320,132,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20311 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20312 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7),(3,7),(4,6)], upper := (rows 35 194 13 328 148 48 99 163 291), lower := (rows 35 194 13 328 148 48 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 20 52 0 129 257), good := (rows 419 130 445 264 180 48 0 128 256) }] }

theorem u20312 : Upper (D 7) (R 7) [34,192,9,320,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20313 : Route 9 := (fun mask => (mask,id))

def c20313 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20313 : Upper (D 7) (R 7) [34,192,9,320,160,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160,1] 13 (by decide) (choices 1) [2,4,16] r20313 c20313
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5620
  · exact u5621
  · exact u5622

def b20314 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(3,1),(4,1)], upper := (rows 35 194 13 328 176 34 85 149 277), lower := (rows 35 194 13 328 176 34 64 128 256), losses := [] }

theorem u20314 : Upper (D 7) (R 7) [34,192,9,320,160,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20315 : Route 9 := (fun mask => (mask,id))

def c20315 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u20315 : Upper (D 7) (R 7) [34,192,9,320,160,4] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160,4] 13 (by decide) (choices 1) [1,2,16] r20315 c20315
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5623
  · exact u5624
  · exact u5625

def b20316 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 194 13 328 176 48 71 135 263), lower := (rows 35 194 13 328 176 48 64 128 256), losses := [] }

theorem u20316 : Upper (D 7) (R 7) [34,192,9,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20316 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20317 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 28 81 33 480 416 416), lower := (rows 35 194 14 28 81 33 64 128 256), losses := [] }

theorem u20317 : Upper (D 7) (R 7) [34,192,10,20,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20318 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 336, targets := 2 }], pairs := [(2,7),(3,7),(4,1),(4,7)], upper := (rows 35 194 14 28 81 160 353 417 289), lower := (rows 35 194 14 28 81 160 64 128 256), losses := [] }

theorem u20318 : Upper (D 7) (R 7) [34,192,10,20,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20318 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20319 : Route 9 := (fun mask => (mask,id))

def c20319 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20319 : Upper (D 7) (R 7) [34,192,10,20,65,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,65,256] 13 (by decide) (choices 1) [1,32,128] r20319 c20319
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5626
  · exact u5627
  · exact u5628

def b20320 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 28 112 33 449 385 385), lower := (rows 35 194 14 28 112 33 64 128 256), losses := [] }

theorem u20320 : Upper (D 7) (R 7) [34,192,10,20,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20321 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 28 112 160 321 385 257), lower := (rows 35 194 14 28 112 160 64 128 256), losses := [] }

theorem u20321 : Upper (D 7) (R 7) [34,192,10,20,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20321 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20322 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 208, targets := 2 },{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(4,1)], upper := (rows 35 194 14 28 112 288 193 129 385), lower := (rows 35 194 14 28 112 288 64 128 256), losses := [] }

theorem u20322 : Upper (D 7) (R 7) [34,192,10,20,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20322 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20323 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 194, targets := 1 },{ cop := 0, region := 464, targets := 2 }], pairs := [(0,6),(0,7),(1,0),(4,1)], upper := (rows 35 194 14 28 273 33 224 224 480), lower := (rows 35 194 14 28 273 33 64 128 256), losses := [] }

theorem u20323 : Upper (D 7) (R 7) [34,192,10,20,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20324 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 194 14 28 273 96 225 161 417), lower := (rows 35 194 14 28 273 96 64 128 256), losses := [] }

theorem u20324 : Upper (D 7) (R 7) [34,192,10,20,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20325 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 464, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(4,1)], upper := (rows 35 194 14 28 304 33 193 193 449), lower := (rows 35 194 14 28 304 33 64 128 256), losses := [] }

theorem u20325 : Upper (D 7) (R 7) [34,192,10,20,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20325 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20326 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 0, region := 400, targets := 2 }], pairs := [(2,6),(3,6),(4,1),(4,6)], upper := (rows 35 194 14 28 304 96 193 129 385), lower := (rows 35 194 14 28 304 96 64 128 256), losses := [] }

theorem u20326 : Upper (D 7) (R 7) [34,192,10,20,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20327 : Route 9 := (fun mask => (mask,id))

def c20327 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u20327 : Upper (D 7) (R 7) [34,192,10,20,320,1] 13 := by
  apply FastRouting.sound _ _ [34,192,10,20,320,1] 13 (by decide) (choices 1) [1,32,128] r20327 c20327
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5629
  · exact u5630
  · exact u5631

def b20328 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 0, region := 336, targets := 2 }], pairs := [(2,7),(3,7),(4,1),(4,7)], upper := (rows 35 194 14 28 336 160 97 161 289), lower := (rows 35 194 14 28 336 160 64 128 256), losses := [] }

theorem u20328 : Upper (D 7) (R 7) [34,192,10,20,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20329 : PairBound 9 := { available := 388, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 81 33 452 388 388), lower := (rows 35 194 14 56 81 33 64 128 256), losses := [] }

theorem u20329 : Upper (D 7) (R 7) [34,192,10,48,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20329 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20330 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 14 56 81 36 449 385 385), lower := (rows 35 194 14 56 81 36 64 128 256), losses := [] }

theorem u20330 : Upper (D 7) (R 7) [34,192,10,48,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20330 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20331 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 81 160 325 389 261), lower := (rows 35 194 14 56 81 160 64 128 256), losses := [] }

theorem u20331 : Upper (D 7) (R 7) [34,192,10,48,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20331 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r20332 : Route 9 := (fun mask => (mask,id))

def c20332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u20332 : Upper (D 7) (R 7) [34,192,10,48,65,256] 13 := by
  apply FastRouting.sound _ _ [34,192,10,48,65,256] 13 (by decide) (choices 1) [1,4,128] r20332 c20332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u5632
  · exact u5633
  · exact u5634

def b20333 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 61, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 84 33 449 385 385), lower := (rows 35 194 14 56 84 33 64 128 256), losses := [] }

theorem u20333 : Upper (D 7) (R 7) [34,192,10,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20334 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 348, targets := 128 },{ cop := 1, region := 60, targets := 1 }], pairs := [(2,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 14 56 84 160 321 385 257), lower := (rows 35 194 14 56 84 160 64 128 256), losses := [] }

theorem u20334 : Upper (D 7) (R 7) [34,192,10,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20334 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20335 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(3,6)], upper := (rows 35 194 14 56 84 288 193 129 385), lower := (rows 35 194 14 56 84 288 64 128 256), losses := [{ target := 6, region := (rows 7 2 4 24 16 319 0 151 279), good := (rows 419 419 431 440 445 288 0 128 288) }] }

theorem u20335 : Upper (D 7) (R 7) [34,192,10,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20335 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20336 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 198, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 14 56 273 33 196 196 452), lower := (rows 35 194 14 56 273 33 64 128 256), losses := [] }

theorem u20336 : Upper (D 7) (R 7) [34,192,10,48,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20337 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 194 14 56 273 36 193 193 449), lower := (rows 35 194 14 56 273 36 64 128 256), losses := [] }

theorem u20337 : Upper (D 7) (R 7) [34,192,10,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20337 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20338 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(2,6),(3,6),(4,6)], upper := (rows 35 194 14 56 273 96 197 133 389), lower := (rows 35 194 14 56 273 96 64 128 256), losses := [] }

theorem u20338 : Upper (D 7) (R 7) [34,192,10,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20339 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 192 },{ cop := 0, region := 194, targets := 32 }], pairs := [(0,6),(0,7),(1,5),(2,5)], upper := (rows 35 194 14 56 276 33 193 193 449), lower := (rows 35 194 14 56 276 33 64 128 256), losses := [{ target := 5, region := (rows 1 43 12 8 24 0 97 161 289), good := (rows 451 194 30 478 276 451 64 128 256) }] }

theorem u20339 : Upper (D 7) (R 7) [34,192,10,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u20339
end Delivery.IrregularNine14.P07
