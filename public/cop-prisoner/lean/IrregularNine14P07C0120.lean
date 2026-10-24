import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0008

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7200 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 77, targets := 2 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,1),(1,5),(2,1),(3,1)], upper := (rows 37 74 84 137 176 34 65 386 258), lower := (rows 37 74 84 137 176 34 65 128 256), losses := [] }

theorem u7200 : Upper (D 7) (R 7) [36,72,80,129,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7200 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7201 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 137 176 34 66 385 257), lower := (rows 37 74 84 137 176 34 66 128 256), losses := [] }

theorem u7201 : Upper (D 7) (R 7) [36,72,80,129,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7201 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7202 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 37 74 84 137 176 34 320 131 259), lower := (rows 37 74 84 137 176 34 320 128 256), losses := [] }

theorem u7202 : Upper (D 7) (R 7) [36,72,80,129,160,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7202 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7203 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 137 273 34 66 160 416), lower := (rows 37 74 84 137 273 34 66 128 256), losses := [] }

theorem u7203 : Upper (D 7) (R 7) [36,72,80,129,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7203 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7204 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 74 84 137 273 34 96 130 386), lower := (rows 37 74 84 137 273 34 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 42 107 170 298), good := (rows 484 490 84 490 340 482 480 128 256) },{ target := 1, region := (rows 1 0 20 8 16 32 97 128 256), good := (rows 101 72 84 201 341 96 96 128 256) }] }

theorem u7204 : Upper (D 7) (R 7) [36,72,80,129,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7204 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7205 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 84 137 273 34 192 162 290), lower := (rows 37 74 84 137 273 34 192 128 256), losses := [] }

theorem u7205 : Upper (D 7) (R 7) [36,72,80,129,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7205 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7206 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 66, targets := 160 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,6),(1,0),(1,5),(1,7)], upper := (rows 37 74 84 137 273 160 66 162 290), lower := (rows 37 74 84 137 273 160 66 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 20 238 0 194 322), good := (rows 61 426 445 169 273 160 418 160 256) }] }

theorem u7206 : Upper (D 7) (R 7) [36,72,80,129,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7206 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7207 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,5),(2,0),(2,1)], upper := (rows 37 74 84 137 273 160 96 130 258), lower := (rows 37 74 84 137 273 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 170 235 138 266), good := (rows 100 490 84 490 340 224 96 224 256) },{ target := 1, region := (rows 1 0 20 8 16 168 235 128 256), good := (rows 101 104 84 233 341 224 96 224 256) },{ target := 5, region := (rows 1 6 6 25 25 0 64 135 263), good := (rows 415 478 478 409 409 128 64 128 256) }] }

theorem u7207 : Upper (D 7) (R 7) [36,72,80,129,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7207 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7208 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 3, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(2,0),(4,0)], upper := (rows 37 74 84 137 274 160 65 162 290), lower := (rows 37 74 84 137 274 160 65 128 256), losses := [] }

theorem u7208 : Upper (D 7) (R 7) [36,72,80,129,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7208 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7209 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 169, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 137 274 160 66 161 289), lower := (rows 37 74 84 137 274 160 66 128 256), losses := [] }

theorem u7209 : Upper (D 7) (R 7) [36,72,80,129,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7209 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7210 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 74 84 137 274 160 96 131 259), lower := (rows 37 74 84 137 274 160 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 168 235 128 256), good := (rows 100 106 84 234 342 224 96 224 256) },{ target := 1, region := (rows 1 0 20 8 16 168 235 128 256), good := (rows 101 104 84 233 340 224 96 224 256) },{ target := 7, region := (rows 1 10 14 8 26 32 97 0 264), good := (rows 101 350 84 351 278 96 96 0 256) }] }

theorem u7210 : Upper (D 7) (R 7) [36,72,80,129,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7210 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7211 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 137 304 34 65 130 386), lower := (rows 37 74 84 137 304 34 65 128 256), losses := [] }

theorem u7211 : Upper (D 7) (R 7) [36,72,80,129,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7211 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7212 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 137 304 34 66 129 385), lower := (rows 37 74 84 137 304 34 66 128 256), losses := [] }

theorem u7212 : Upper (D 7) (R 7) [36,72,80,129,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7212 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7213 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 0, region := 202, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(4,7)], upper := (rows 37 74 84 137 304 34 192 131 259), lower := (rows 37 74 84 137 304 34 192 128 256), losses := [] }

theorem u7213 : Upper (D 7) (R 7) [36,72,80,129,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7213 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7214 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 137 304 160 65 130 258), lower := (rows 37 74 84 137 304 160 65 128 256), losses := [] }

theorem u7214 : Upper (D 7) (R 7) [36,72,80,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7214 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7215 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 202, targets := 32 },{ cop := 3, region := 66, targets := 1 },{ cop := 3, region := 66, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,5)], upper := (rows 37 74 84 137 304 160 66 131 259), lower := (rows 37 74 84 137 304 160 66 128 256), losses := [] }

theorem u7215 : Upper (D 7) (R 7) [36,72,80,129,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7215 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7216 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 436, targets := 1 },{ cop := 1, region := 432, targets := 64 },{ cop := 3, region := 66, targets := 32 }], pairs := [(1,5),(2,0),(4,0),(4,6)], upper := (rows 37 74 84 137 400 34 65 162 290), lower := (rows 37 74 84 137 400 34 65 128 256), losses := [] }

theorem u7216 : Upper (D 7) (R 7) [36,72,80,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7216 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7217 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 137 400 34 66 161 289), lower := (rows 37 74 84 137 400 34 66 128 256), losses := [] }

theorem u7217 : Upper (D 7) (R 7) [36,72,80,129,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7217 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7218 : Route 9 := (fun mask => (mask,id))

def c7218 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7218 : Upper (D 7) (R 7) [36,72,80,129,384,2,32] 13 := by
  apply FastRouting.sound _ _ [36,72,80,129,384,2,32] 13 (by decide) (choices 1) [1,2] r7218 c7218
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u524
  · exact u525

def b7219 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 74 84 138 145 288 65 162 290), lower := (rows 37 74 84 138 145 288 65 128 256), losses := [] }

theorem u7219 : Upper (D 7) (R 7) [36,72,80,130,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7219 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7220 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 84 138 145 288 66 161 289), lower := (rows 37 74 84 138 145 288 66 128 256), losses := [] }

theorem u7220 : Upper (D 7) (R 7) [36,72,80,130,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7220 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7221 : PairBound 9 := { available := 3, camps := [], pairs := [(1,0),(2,0),(3,0)], upper := (rows 37 74 84 138 145 288 96 131 259), lower := (rows 37 74 84 138 145 288 96 128 256), losses := [{ target := 0, region := (rows 0 22 20 24 16 288 353 128 256), good := (rows 102 74 94 138 222 352 96 128 352) }] }

theorem u7221 : Upper (D 7) (R 7) [36,72,80,130,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7221 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7222 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 74 84 138 176 288 65 131 259), lower := (rows 37 74 84 138 176 288 65 128 256), losses := [] }

theorem u7222 : Upper (D 7) (R 7) [36,72,80,130,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7222 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7223 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 84 138 176 288 66 129 257), lower := (rows 37 74 84 138 176 288 66 128 256), losses := [] }

theorem u7223 : Upper (D 7) (R 7) [36,72,80,130,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7223 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7224 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 1, region := 168, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(3,0)], upper := (rows 37 74 84 138 273 160 65 162 290), lower := (rows 37 74 84 138 273 160 65 128 256), losses := [] }

theorem u7224 : Upper (D 7) (R 7) [36,72,80,130,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7224 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7225 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 84 138 273 160 66 161 289), lower := (rows 37 74 84 138 273 160 66 128 256), losses := [] }

theorem u7225 : Upper (D 7) (R 7) [36,72,80,130,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7225 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7226 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,0)], upper := (rows 37 74 84 138 273 160 96 131 259), lower := (rows 37 74 84 138 273 160 96 128 256), losses := [{ target := 0, region := (rows 0 235 20 168 16 168 235 128 256), good := (rows 110 106 86 234 342 234 106 234 256) },{ target := 1, region := (rows 1 0 20 8 16 168 235 128 256), good := (rows 101 104 84 232 341 224 96 224 256) }] }

theorem u7226 : Upper (D 7) (R 7) [36,72,80,130,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7226 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7227 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 2, region := 161, targets := 64 }], pairs := [(0,1),(0,6),(2,1),(3,6)], upper := (rows 37 74 84 138 274 160 65 161 289), lower := (rows 37 74 84 138 274 160 65 128 256), losses := [{ target := 6, region := (rows 5 2 4 10 18 239 0 197 325), good := (rows 421 442 437 186 314 160 417 160 256) }] }

theorem u7227 : Upper (D 7) (R 7) [36,72,80,130,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7227 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7228 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 229, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 74 84 138 274 160 96 129 257), lower := (rows 37 74 84 138 274 160 96 128 256), losses := [] }

theorem u7228 : Upper (D 7) (R 7) [36,72,80,130,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7228 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7229 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 138 304 160 65 131 259), lower := (rows 37 74 84 138 304 160 65 128 256), losses := [] }

theorem u7229 : Upper (D 7) (R 7) [36,72,80,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7229 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7230 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 433, targets := 66 }], pairs := [(0,1),(0,6),(4,1),(4,6)], upper := (rows 37 74 84 138 304 160 66 129 257), lower := (rows 37 74 84 138 304 160 66 128 256), losses := [] }

theorem u7230 : Upper (D 7) (R 7) [36,72,80,130,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7230 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7231 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 138 400 33 65 162 290), lower := (rows 37 74 84 138 400 33 65 128 256), losses := [] }

theorem u7231 : Upper (D 7) (R 7) [36,72,80,130,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7231 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7232 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 37 74 84 138 400 33 66 161 289), lower := (rows 37 74 84 138 400 33 66 128 256), losses := [] }

theorem u7232 : Upper (D 7) (R 7) [36,72,80,130,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7232 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7233 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 138 400 33 96 131 259), lower := (rows 37 74 84 138 400 33 96 128 256), losses := [] }

theorem u7233 : Upper (D 7) (R 7) [36,72,80,130,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7233 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7234 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 85, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 37 74 84 168 145 288 65 130 258), lower := (rows 37 74 84 168 145 288 65 128 256), losses := [] }

theorem u7234 : Upper (D 7) (R 7) [36,72,80,160,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7234 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7235 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 37 74 84 168 145 288 66 131 259), lower := (rows 37 74 84 168 145 288 66 128 256), losses := [] }

theorem u7235 : Upper (D 7) (R 7) [36,72,80,160,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7235 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7236 : Route 9 := (fun mask => (mask,id))

def c7236 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7236 : Upper (D 7) (R 7) [36,72,80,160,130,256,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,130,256,1] 13 (by decide) (choices 1) [1,2] r7236 c7236
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u526
  · exact u527

def b7237 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 86, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 37 74 84 168 146 288 66 129 257), lower := (rows 37 74 84 168 146 288 66 128 256), losses := [] }

theorem u7237 : Upper (D 7) (R 7) [36,72,80,160,130,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7237 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7238 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 68, targets := 162 },{ cop := 1, region := 168, targets := 1 }], pairs := [(2,1),(2,5),(2,7),(3,0)], upper := (rows 37 74 84 168 273 34 65 130 386), lower := (rows 37 74 84 168 273 34 65 128 256), losses := [] }

theorem u7238 : Upper (D 7) (R 7) [36,72,80,160,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7238 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7239 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 168 273 34 66 129 385), lower := (rows 37 74 84 168 273 34 66 128 256), losses := [] }

theorem u7239 : Upper (D 7) (R 7) [36,72,80,160,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7239 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7240 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 6, region := 42, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 37 74 84 168 273 34 192 131 259), lower := (rows 37 74 84 168 273 34 192 128 256), losses := [] }

theorem u7240 : Upper (D 7) (R 7) [36,72,80,160,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7240 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 84 168 274 33 65 130 386), lower := (rows 37 74 84 168 274 33 65 128 256), losses := [] }

theorem u7241 : Upper (D 7) (R 7) [36,72,80,160,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7241 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 169, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 168 274 33 66 129 385), lower := (rows 37 74 84 168 274 33 66 128 256), losses := [] }

theorem u7242 : Upper (D 7) (R 7) [36,72,80,160,258,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7242 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7243 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 2, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,7)], upper := (rows 37 74 84 168 274 33 192 131 259), lower := (rows 37 74 84 168 274 33 192 128 256), losses := [] }

theorem u7243 : Upper (D 7) (R 7) [36,72,80,160,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7243 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7244 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 404, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 37 74 84 168 400 33 65 130 258), lower := (rows 37 74 84 168 400 33 65 128 256), losses := [] }

theorem u7244 : Upper (D 7) (R 7) [36,72,80,160,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7244 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7245 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 74 84 168 400 33 66 131 259), lower := (rows 37 74 84 168 400 33 66 128 256), losses := [] }

theorem u7245 : Upper (D 7) (R 7) [36,72,80,160,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7245 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r7246 : Route 9 := (fun mask => (mask,id))

def c7246 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7246 : Upper (D 7) (R 7) [36,72,80,160,384,2,1] 13 := by
  apply FastRouting.sound _ _ [36,72,80,160,384,2,1] 13 (by decide) (choices 1) [1,2] r7246 c7246
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u528
  · exact u529

def b7247 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 168 400 34 66 129 257), lower := (rows 37 74 84 168 400 34 66 128 256), losses := [] }

theorem u7247 : Upper (D 7) (R 7) [36,72,80,160,384,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7247 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 265 50 160 65 130 386), lower := (rows 37 74 84 265 50 160 65 128 256), losses := [] }

theorem u7248 : Upper (D 7) (R 7) [36,72,80,257,34,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7248 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 265 50 160 66 129 385), lower := (rows 37 74 84 265 50 160 66 128 256), losses := [] }

theorem u7249 : Upper (D 7) (R 7) [36,72,80,257,34,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7249 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7250 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5),(2,0),(3,5),(4,0)], upper := (rows 37 74 84 265 50 160 192 131 259), lower := (rows 37 74 84 265 50 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 22 8 18 224 224 128 256), good := (rows 100 126 116 264 118 224 224 224 256) }] }

theorem u7250 : Upper (D 7) (R 7) [36,72,80,257,34,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7250 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7251 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 265 145 34 66 160 416), lower := (rows 37 74 84 265 145 34 66 128 256), losses := [] }

theorem u7251 : Upper (D 7) (R 7) [36,72,80,257,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7251 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7252 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(2,1)], upper := (rows 37 74 84 265 145 34 96 130 386), lower := (rows 37 74 84 265 145 34 96 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 42 107 170 298), good := (rows 484 490 84 490 212 482 480 128 256) },{ target := 1, region := (rows 1 0 20 8 16 32 97 128 256), good := (rows 101 72 84 329 213 96 96 128 256) }] }

theorem u7252 : Upper (D 7) (R 7) [36,72,80,257,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7252 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7253 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 37 74 84 265 145 34 192 162 290), lower := (rows 37 74 84 265 145 34 192 128 256), losses := [] }

theorem u7253 : Upper (D 7) (R 7) [36,72,80,257,129,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7253 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 69, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 74 84 265 176 34 65 130 386), lower := (rows 37 74 84 265 176 34 65 128 256), losses := [] }

theorem u7254 : Upper (D 7) (R 7) [36,72,80,257,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7254 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7255 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 37 74 84 265 176 34 66 129 385), lower := (rows 37 74 84 265 176 34 66 128 256), losses := [] }

theorem u7255 : Upper (D 7) (R 7) [36,72,80,257,160,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7255 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7256 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 0, region := 458, targets := 32 }], pairs := [(0,7),(1,5),(1,7),(3,7)], upper := (rows 37 74 84 265 176 34 192 131 259), lower := (rows 37 74 84 265 176 34 192 128 256), losses := [] }

theorem u7256 : Upper (D 7) (R 7) [36,72,80,257,160,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7256 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 37 74 84 296 19 160 65 130 386), lower := (rows 37 74 84 296 19 160 65 128 256), losses := [] }

theorem u7257 : Upper (D 7) (R 7) [36,72,80,288,3,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7257 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7258 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 425, targets := 66 }], pairs := [(0,1),(0,6),(3,1),(3,6)], upper := (rows 37 74 84 296 19 160 66 129 385), lower := (rows 37 74 84 296 19 160 66 128 256), losses := [] }

theorem u7258 : Upper (D 7) (R 7) [36,72,80,288,3,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7258 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7259 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 196, targets := 32 },{ cop := 4, region := 424, targets := 64 }], pairs := [(0,1),(1,0),(2,5),(3,6)], upper := (rows 37 74 84 296 19 160 192 131 259), lower := (rows 37 74 84 296 19 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 100 106 116 362 18 224 224 224 256) },{ target := 1, region := (rows 5 0 4 8 16 224 224 128 256), good := (rows 101 104 117 360 17 224 224 224 256) }] }

theorem u7259 : Upper (D 7) (R 7) [36,72,80,288,3,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7259 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u7259
end Delivery.IrregularNine14.P07
