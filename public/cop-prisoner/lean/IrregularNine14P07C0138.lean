import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0010
import IrregularNine14P07C0011

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8280 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 98, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 268 88 145 34 192 131 259), lower := (rows 37 98 268 88 145 34 192 128 256), losses := [] }

theorem u8280 : Upper (D 7) (R 7) [36,96,264,80,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8280 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8281 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 88 146 33 65 130 386), lower := (rows 37 98 268 88 146 33 65 128 256), losses := [] }

theorem u8281 : Upper (D 7) (R 7) [36,96,264,80,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8281 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8282 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 268 88 146 33 66 129 385), lower := (rows 37 98 268 88 146 33 66 128 256), losses := [] }

theorem u8282 : Upper (D 7) (R 7) [36,96,264,80,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8282 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8283 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(3,0)], upper := (rows 37 98 268 88 146 33 192 131 259), lower := (rows 37 98 268 88 146 33 192 128 256), losses := [] }

theorem u8283 : Upper (D 7) (R 7) [36,96,264,80,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8283 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8284 : Route 9 := (fun mask => (mask,id))

def c8284 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8284 : Upper (D 7) (R 7) [36,96,264,80,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,264,80,130,128,1] 13 (by decide) (choices 1) [1,2] r8284 c8284
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u658
  · exact u659

def b8285 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 98 268 88 146 160 66 129 257), lower := (rows 37 98 268 88 146 160 66 128 256), losses := [] }

theorem u8285 : Upper (D 7) (R 7) [36,96,264,80,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8285 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8286 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 396, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 268 137 81 34 66 144 400), lower := (rows 37 98 268 137 81 34 66 128 256), losses := [] }

theorem u8286 : Upper (D 7) (R 7) [36,96,264,129,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8286 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8287 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 137 81 34 80 130 386), lower := (rows 37 98 268 137 81 34 80 128 256), losses := [] }

theorem u8287 : Upper (D 7) (R 7) [36,96,264,129,65,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8287 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8288 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 80, targets := 34 },{ cop := 6, region := 34, targets := 129 }], pairs := [(1,0),(1,7),(4,1),(4,5)], upper := (rows 37 98 268 137 81 34 192 146 274), lower := (rows 37 98 268 137 81 34 192 128 256), losses := [] }

theorem u8288 : Upper (D 7) (R 7) [36,96,264,129,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8288 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8289 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 6, region := 178, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 37 98 268 137 146 34 65 208 336), lower := (rows 37 98 268 137 146 34 65 128 256), losses := [] }

theorem u8289 : Upper (D 7) (R 7) [36,96,264,129,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8289 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8290 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 268 137 146 34 80 193 321), lower := (rows 37 98 268 137 146 34 80 128 256), losses := [] }

theorem u8290 : Upper (D 7) (R 7) [36,96,264,129,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8290 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8291 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 178, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(4,0)], upper := (rows 37 98 268 137 146 48 65 194 322), lower := (rows 37 98 268 137 146 48 65 128 256), losses := [] }

theorem u8291 : Upper (D 7) (R 7) [36,96,264,129,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8291 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8292 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 268 137 146 48 66 193 321), lower := (rows 37 98 268 137 146 48 66 128 256), losses := [] }

theorem u8292 : Upper (D 7) (R 7) [36,96,264,129,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8292 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8293 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 3, region := 80, targets := 34 }], pairs := [(0,7),(1,7),(4,1),(4,5)], upper := (rows 37 98 268 137 208 34 65 146 274), lower := (rows 37 98 268 137 208 34 65 128 256), losses := [] }

theorem u8293 : Upper (D 7) (R 7) [36,96,264,129,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8293 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8294 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 268 137 208 34 66 145 273), lower := (rows 37 98 268 137 208 34 66 128 256), losses := [] }

theorem u8294 : Upper (D 7) (R 7) [36,96,264,129,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8294 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8295 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 137 208 34 80 131 259), lower := (rows 37 98 268 137 208 34 80 128 256), losses := [] }

theorem u8295 : Upper (D 7) (R 7) [36,96,264,129,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8295 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8296 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 268 138 19 48 65 192 448), lower := (rows 37 98 268 138 19 48 65 128 256), losses := [] }

theorem u8296 : Upper (D 7) (R 7) [36,96,264,130,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8296 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8297 : Route 9 := (fun mask => (mask,id))

def c8297 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u8297 : Upper (D 7) (R 7) [36,96,264,130,3,16,128] 13 := by
  apply FastRouting.sound _ _ [36,96,264,130,3,16,128] 13 (by decide) (choices 1) [1,64] r8297 c8297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u660
  · exact u661

def b8298 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 268 138 145 48 65 194 322), lower := (rows 37 98 268 138 145 48 65 128 256), losses := [] }

theorem u8298 : Upper (D 7) (R 7) [36,96,264,130,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8298 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8299 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 268 138 145 48 66 193 321), lower := (rows 37 98 268 138 145 48 66 128 256), losses := [] }

theorem u8299 : Upper (D 7) (R 7) [36,96,264,130,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8299 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8300 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 138 208 33 65 146 274), lower := (rows 37 98 268 138 208 33 65 128 256), losses := [] }

theorem u8300 : Upper (D 7) (R 7) [36,96,264,130,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8300 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8301 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 268 138 208 33 66 145 273), lower := (rows 37 98 268 138 208 33 66 128 256), losses := [] }

theorem u8301 : Upper (D 7) (R 7) [36,96,264,130,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8301 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8302 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 37 98 268 138 208 33 80 131 259), lower := (rows 37 98 268 138 208 33 80 128 256), losses := [] }

theorem u8302 : Upper (D 7) (R 7) [36,96,264,130,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8302 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8303 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 4, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(4,7)], upper := (rows 37 98 268 152 81 34 65 130 386), lower := (rows 37 98 268 152 81 34 65 128 256), losses := [] }

theorem u8303 : Upper (D 7) (R 7) [36,96,264,144,65,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8303 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8304 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 396, targets := 98 }], pairs := [(2,1),(2,5),(2,6),(3,1)], upper := (rows 37 98 268 152 81 34 66 129 385), lower := (rows 37 98 268 152 81 34 66 128 256), losses := [] }

theorem u8304 : Upper (D 7) (R 7) [36,96,264,144,65,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8304 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8305 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 34, targets := 129 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 268 152 81 34 192 131 259), lower := (rows 37 98 268 152 81 34 192 128 256), losses := [{ target := 7, region := (rows 13 82 12 8 16 122 64 0 280), good := (rows 37 98 301 319 371 34 98 0 256) }] }

theorem u8305 : Upper (D 7) (R 7) [36,96,264,144,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8305 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8306 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 268 200 19 48 65 130 386), lower := (rows 37 98 268 200 19 48 65 128 256), losses := [] }

theorem u8306 : Upper (D 7) (R 7) [36,96,264,192,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8306 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8307 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 98 268 200 19 48 66 129 385), lower := (rows 37 98 268 200 19 48 66 128 256), losses := [] }

theorem u8307 : Upper (D 7) (R 7) [36,96,264,192,3,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8307 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8308 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 268 200 19 48 192 131 259), lower := (rows 37 98 268 200 19 48 192 128 256), losses := [] }

theorem u8308 : Upper (D 7) (R 7) [36,96,264,192,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8308 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8309 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 99, targets := 128 },{ cop := 4, region := 72, targets := 34 }], pairs := [(0,7),(1,7),(3,1),(3,5)], upper := (rows 37 98 268 200 145 34 65 146 274), lower := (rows 37 98 268 200 145 34 65 128 256), losses := [] }

theorem u8309 : Upper (D 7) (R 7) [36,96,264,192,129,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8309 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8310 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 37 98 268 200 145 34 66 145 273), lower := (rows 37 98 268 200 145 34 66 128 256), losses := [] }

theorem u8310 : Upper (D 7) (R 7) [36,96,264,192,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8310 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8311 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 37 98 268 200 145 34 80 131 259), lower := (rows 37 98 268 200 145 34 80 128 256), losses := [] }

theorem u8311 : Upper (D 7) (R 7) [36,96,264,192,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8311 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8312 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 396, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 37 98 268 200 145 48 65 130 258), lower := (rows 37 98 268 200 145 48 65 128 256), losses := [] }

theorem u8312 : Upper (D 7) (R 7) [36,96,264,192,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8312 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8313 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(3,0)], upper := (rows 37 98 268 200 145 48 66 131 259), lower := (rows 37 98 268 200 145 48 66 128 256), losses := [] }

theorem u8313 : Upper (D 7) (R 7) [36,96,264,192,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8313 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8314 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 37 98 268 200 146 33 65 146 274), lower := (rows 37 98 268 200 146 33 65 128 256), losses := [] }

theorem u8314 : Upper (D 7) (R 7) [36,96,264,192,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8314 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8315 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 33, targets := 66 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,1),(0,6),(0,7),(1,7)], upper := (rows 37 98 268 200 146 33 66 145 273), lower := (rows 37 98 268 200 146 33 66 128 256), losses := [] }

theorem u8315 : Upper (D 7) (R 7) [36,96,264,192,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8315 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8316 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 }], pairs := [(0,1),(0,6),(0,7)], upper := (rows 37 98 268 200 146 33 80 131 259), lower := (rows 37 98 268 200 146 33 80 128 256), losses := [] }

theorem u8316 : Upper (D 7) (R 7) [36,96,264,192,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8316 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8317 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 66 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 98 324 11 145 160 66 152 280), lower := (rows 37 98 324 11 145 160 66 128 256), losses := [] }

theorem u8317 : Upper (D 7) (R 7) [36,96,320,3,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8317 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8318 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 324 11 145 160 72 146 274), lower := (rows 37 98 324 11 145 160 72 128 256), losses := [] }

theorem u8318 : Upper (D 7) (R 7) [36,96,320,3,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8318 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8319 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 324 11 145 160 80 138 266), lower := (rows 37 98 324 11 145 160 80 128 256), losses := [] }

theorem u8319 : Upper (D 7) (R 7) [36,96,320,3,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8319 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8320 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 65 }], pairs := [(1,7),(3,7),(4,0),(4,6)], upper := (rows 37 98 324 11 146 160 65 152 280), lower := (rows 37 98 324 11 146 160 65 128 256), losses := [] }

theorem u8320 : Upper (D 7) (R 7) [36,96,320,3,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8320 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8321 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 468, targets := 32 }], pairs := [(1,7),(2,5),(3,7)], upper := (rows 37 98 324 11 146 160 72 145 273), lower := (rows 37 98 324 11 146 160 72 128 256), losses := [] }

theorem u8321 : Upper (D 7) (R 7) [36,96,320,3,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8321 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8322 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 324 11 146 160 80 137 265), lower := (rows 37 98 324 11 146 160 80 128 256), losses := [] }

theorem u8322 : Upper (D 7) (R 7) [36,96,320,3,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8322 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8323 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 65 }], pairs := [(1,7),(3,7),(4,0),(4,6)], upper := (rows 37 98 324 11 152 160 65 146 274), lower := (rows 37 98 324 11 152 160 65 128 256), losses := [] }

theorem u8323 : Upper (D 7) (R 7) [36,96,320,3,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8323 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8324 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 74, targets := 128 },{ cop := 3, region := 144, targets := 66 }], pairs := [(1,7),(3,7),(4,1),(4,6)], upper := (rows 37 98 324 11 152 160 66 145 273), lower := (rows 37 98 324 11 152 160 66 128 256), losses := [] }

theorem u8324 : Upper (D 7) (R 7) [36,96,320,3,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8324 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8325 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 269, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 98 324 11 152 160 80 131 259), lower := (rows 37 98 324 11 152 160 80 128 256), losses := [] }

theorem u8325 : Upper (D 7) (R 7) [36,96,320,3,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8325 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8326 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(1,0),(1,7),(3,7),(4,7)], upper := (rows 37 98 324 25 26 160 65 130 386), lower := (rows 37 98 324 25 26 160 65 128 256), losses := [] }

theorem u8326 : Upper (D 7) (R 7) [36,96,320,17,10,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8326 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8327 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 90, targets := 128 },{ cop := 1, region := 389, targets := 2 }], pairs := [(0,1),(1,7),(3,7),(4,7)], upper := (rows 37 98 324 25 26 160 66 129 385), lower := (rows 37 98 324 25 26 160 66 128 256), losses := [] }

theorem u8327 : Upper (D 7) (R 7) [36,96,320,17,10,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8327 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8328 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 98 324 25 26 160 192 131 259), lower := (rows 37 98 324 25 26 160 192 128 256), losses := [] }

theorem u8328 : Upper (D 7) (R 7) [36,96,320,17,10,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8328 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8329 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 37 98 324 25 146 40 65 130 386), lower := (rows 37 98 324 25 146 40 65 128 256), losses := [] }

theorem u8329 : Upper (D 7) (R 7) [36,96,320,17,130,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8329 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8330 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 389, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,1),(1,0),(2,1)], upper := (rows 37 98 324 25 146 40 66 129 385), lower := (rows 37 98 324 25 146 40 66 128 256), losses := [] }

theorem u8330 : Upper (D 7) (R 7) [36,96,320,17,130,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8330 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8331 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 324 25 146 40 192 131 259), lower := (rows 37 98 324 25 146 40 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 40 208 128 256), good := (rows 36 98 324 122 210 42 192 192 256) }] }

theorem u8331 : Upper (D 7) (R 7) [36,96,320,17,130,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8331 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r8332 : Route 9 := (fun mask => (mask,id))

def c8332 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8332 : Upper (D 7) (R 7) [36,96,320,17,130,128,1] 13 := by
  apply FastRouting.sound _ _ [36,96,320,17,130,128,1] 13 (by decide) (choices 1) [2,8] r8332 c8332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u662
  · exact u663

def b8333 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 82, targets := 1 },{ cop := 0, region := 66, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(4,0)], upper := (rows 37 98 324 25 146 160 66 137 265), lower := (rows 37 98 324 25 146 160 66 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 16 0 82 136 264), good := (rows 5 66 324 477 210 128 66 128 256) }] }

theorem u8333 : Upper (D 7) (R 7) [36,96,320,17,130,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8333 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8334 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 261, targets := 128 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 37 98 324 25 146 160 72 131 259), lower := (rows 37 98 324 25 146 160 72 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 72 128 256), good := (rows 36 98 324 122 178 160 74 160 256) }] }

theorem u8334 : Upper (D 7) (R 7) [36,96,320,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8334 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8335 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 103, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 25 152 34 65 130 386), lower := (rows 37 98 324 25 152 34 65 128 256), losses := [] }

theorem u8335 : Upper (D 7) (R 7) [36,96,320,17,136,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8335 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8336 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 152, targets := 98 }], pairs := [(3,1),(3,5),(3,6),(4,1)], upper := (rows 37 98 324 25 152 34 66 129 385), lower := (rows 37 98 324 25 152 34 66 128 256), losses := [] }

theorem u8336 : Upper (D 7) (R 7) [36,96,320,17,136,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8336 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8337 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 295, targets := 128 },{ cop := 2, region := 34, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 25 152 34 192 131 259), lower := (rows 37 98 324 25 152 34 192 128 256), losses := [] }

theorem u8337 : Upper (D 7) (R 7) [36,96,320,17,136,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8337 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8338 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 6, region := 162, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 25 152 160 65 130 258), lower := (rows 37 98 324 25 152 160 65 128 256), losses := [] }

theorem u8338 : Upper (D 7) (R 7) [36,96,320,17,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8338 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8339 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 327, targets := 128 },{ cop := 0, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 37 98 324 25 152 160 66 131 259), lower := (rows 37 98 324 25 152 160 66 128 256), losses := [] }

theorem u8339 : Upper (D 7) (R 7) [36,96,320,17,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8339 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8339
end Delivery.IrregularNine14.P07
