import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0104

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21240 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 68 }], pairs := [(0,2),(0,6),(3,6)], upper := (rows 35 74 134 268 84 33 113 177 305), lower := (rows 35 74 134 268 84 33 64 128 256), losses := [{ target := 6, region := (rows 7 2 4 24 16 63 0 144 272), good := (rows 35 43 167 301 445 33 0 128 256) }] }

theorem u21240 : Upper (D 6) (R 6) [34,72,130,260,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21241 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 74 134 268 84 48 97 161 289), lower := (rows 35 74 134 268 84 48 64 128 256), losses := [] }

theorem u21241 : Upper (D 6) (R 6) [34,72,130,260,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21241 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21242 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 49, targets := 4 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,2),(0,6),(4,2)], upper := (rows 35 74 134 268 112 33 85 149 277), lower := (rows 35 74 134 268 112 33 64 128 256), losses := [] }

theorem u21242 : Upper (D 6) (R 6) [34,72,130,260,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21242 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21243 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 6 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 35 74 134 268 112 36 81 145 273), lower := (rows 35 74 134 268 112 36 64 128 256), losses := [] }

theorem u21243 : Upper (D 6) (R 6) [34,72,130,260,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21243 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21244 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 74 134 268 112 48 69 133 261), lower := (rows 35 74 134 268 112 48 64 128 256), losses := [] }

theorem u21244 : Upper (D 6) (R 6) [34,72,130,260,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21244 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21245 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 1 }], pairs := [(0,2),(0,6),(2,0)], upper := (rows 35 74 134 280 21 33 100 228 356), lower := (rows 35 74 134 280 21 33 64 128 256), losses := [] }

theorem u21245 : Upper (D 6) (R 6) [34,72,130,272,5,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21246 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 49, targets := 64 },{ cop := 4, region := 360, targets := 2 }], pairs := [(0,6),(3,1),(4,6)], upper := (rows 35 74 134 280 21 36 97 225 353), lower := (rows 35 74 134 280 21 36 64 128 256), losses := [] }

theorem u21246 : Upper (D 6) (R 6) [34,72,130,272,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21247 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 280 21 96 101 165 293), lower := (rows 35 74 134 280 21 96 64 128 256), losses := [] }

theorem u21247 : Upper (D 6) (R 6) [34,72,130,272,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21248 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 33, targets := 68 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(0,6),(2,5)], upper := (rows 35 74 134 280 52 33 69 197 325), lower := (rows 35 74 134 280 52 33 64 128 256), losses := [] }

theorem u21248 : Upper (D 6) (R 6) [34,72,130,272,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21248 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21249 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 331, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 35 74 134 280 52 36 65 193 321), lower := (rows 35 74 134 280 52 36 64 128 256), losses := [] }

theorem u21249 : Upper (D 6) (R 6) [34,72,130,272,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21250 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 134 280 52 96 69 133 261), lower := (rows 35 74 134 280 52 96 64 128 256), losses := [] }

theorem u21250 : Upper (D 6) (R 6) [34,72,130,272,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21250 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21251 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 296 81 33 84 148 276), lower := (rows 35 74 134 296 81 33 64 128 256), losses := [] }

theorem u21251 : Upper (D 6) (R 6) [34,72,130,288,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21251 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21252 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 134 296 81 36 85 149 277), lower := (rows 35 74 134 296 81 36 64 128 256), losses := [] }

theorem u21252 : Upper (D 6) (R 6) [34,72,130,288,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21253 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 296 81 48 69 133 261), lower := (rows 35 74 134 296 81 48 64 128 256), losses := [] }

theorem u21253 : Upper (D 6) (R 6) [34,72,130,288,65,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21253 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21254 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 134 296 84 33 85 149 277), lower := (rows 35 74 134 296 84 33 64 128 256), losses := [] }

theorem u21254 : Upper (D 6) (R 6) [34,72,130,288,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21254 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21255 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 2, region := 33, targets := 64 }], pairs := [(0,6),(2,5),(4,5)], upper := (rows 35 74 134 296 84 36 81 145 273), lower := (rows 35 74 134 296 84 36 64 128 256), losses := [] }

theorem u21255 : Upper (D 6) (R 6) [34,72,130,288,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21256 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 134 296 84 48 69 133 261), lower := (rows 35 74 134 296 84 48 64 128 256), losses := [] }

theorem u21256 : Upper (D 6) (R 6) [34,72,130,288,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21256 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21257 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 22 33 352 480 352), lower := (rows 35 74 148 13 22 33 64 128 256), losses := [] }

theorem u21257 : Upper (D 6) (R 6) [34,72,144,5,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21258 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 13 22 96 353 417 289), lower := (rows 35 74 148 13 22 96 64 128 256), losses := [] }

theorem u21258 : Upper (D 6) (R 6) [34,72,144,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21258 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21259 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 355, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 74 148 13 22 288 97 225 353), lower := (rows 35 74 148 13 22 288 64 128 256), losses := [] }

theorem u21259 : Upper (D 6) (R 6) [34,72,144,5,6,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21259 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21260 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 81 34 356 420 292), lower := (rows 35 74 148 13 81 34 64 128 256), losses := [] }

theorem u21260 : Upper (D 6) (R 6) [34,72,144,5,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21261 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 35 74 148 13 81 36 354 418 290), lower := (rows 35 74 148 13 81 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 60 75 139 267), good := (rows 482 490 180 494 500 36 64 128 256) }] }

theorem u21261 : Upper (D 6) (R 6) [34,72,144,5,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21262 : Route 9 := (fun mask => (mask,id))

def c21262 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21262 : Upper (D 6) (R 6) [34,72,144,5,65,256] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,65,256] 13 (by decide) (choices 1) [2,4,32] r21262 c21262
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6287
  · exact u6288
  · exact u6289

def b21263 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 112 33 326 390 262), lower := (rows 35 74 148 13 112 33 64 128 256), losses := [] }

theorem u21263 : Upper (D 6) (R 6) [34,72,144,5,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21264 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 112 34 325 389 261), lower := (rows 35 74 148 13 112 34 64 128 256), losses := [] }

theorem u21264 : Upper (D 6) (R 6) [34,72,144,5,96,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21264 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21265 : PairBound 9 := { available := 259, camps := [{ cop := 3, region := 322, targets := 36 },{ cop := 0, region := 336, targets := 4 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 148 13 112 36 323 387 259), lower := (rows 35 74 148 13 112 36 64 128 256), losses := [] }

theorem u21265 : Upper (D 6) (R 6) [34,72,144,5,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r21266 : Route 9 := (fun mask => (mask,id))

def c21266 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u21266 : Upper (D 6) (R 6) [34,72,144,5,96,256] 13 := by
  apply FastRouting.sound _ _ [34,72,144,5,96,256] 13 (by decide) (choices 1) [1,2,4] r21266 c21266
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6290
  · exact u6291
  · exact u6292

def b21267 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 273 34 100 228 356), lower := (rows 35 74 148 13 273 34 64 128 256), losses := [] }

theorem u21267 : Upper (D 6) (R 6) [34,72,144,5,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21268 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 336, targets := 4 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(2,0),(4,2)], upper := (rows 35 74 148 13 273 36 98 226 354), lower := (rows 35 74 148 13 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 60 75 139 267), good := (rows 482 490 180 494 500 36 64 128 256) }] }

theorem u21268 : Upper (D 6) (R 6) [34,72,144,5,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21268 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21269 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 13 273 96 102 166 294), lower := (rows 35 74 148 13 273 96 64 128 256), losses := [] }

theorem u21269 : Upper (D 6) (R 6) [34,72,144,5,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21270 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 274 33 100 228 356), lower := (rows 35 74 148 13 274 33 64 128 256), losses := [] }

theorem u21270 : Upper (D 6) (R 6) [34,72,144,5,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21270 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21271 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 74 148 13 274 36 97 225 353), lower := (rows 35 74 148 13 274 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 144 475 274 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 128 256), good := (rows 35 43 180 45 275 36 0 128 256) }] }

theorem u21271 : Upper (D 6) (R 6) [34,72,144,5,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21272 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 13 274 96 101 165 293), lower := (rows 35 74 148 13 274 96 64 128 256), losses := [] }

theorem u21272 : Upper (D 6) (R 6) [34,72,144,5,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21273 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 276 33 98 226 354), lower := (rows 35 74 148 13 276 33 64 128 256), losses := [] }

theorem u21273 : Upper (D 6) (R 6) [34,72,144,5,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21273 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21274 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 276 34 97 225 353), lower := (rows 35 74 148 13 276 34 64 128 256), losses := [] }

theorem u21274 : Upper (D 6) (R 6) [34,72,144,5,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21275 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 13 276 96 99 163 291), lower := (rows 35 74 148 13 276 96 64 128 256), losses := [] }

theorem u21275 : Upper (D 6) (R 6) [34,72,144,5,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21276 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 304 33 70 198 326), lower := (rows 35 74 148 13 304 33 64 128 256), losses := [] }

theorem u21276 : Upper (D 6) (R 6) [34,72,144,5,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21277 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 304 34 69 197 325), lower := (rows 35 74 148 13 304 34 64 128 256), losses := [] }

theorem u21277 : Upper (D 6) (R 6) [34,72,144,5,288,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21278 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 66, targets := 36 },{ cop := 0, region := 336, targets := 4 }], pairs := [(1,2),(1,5),(4,2)], upper := (rows 35 74 148 13 304 36 67 195 323), lower := (rows 35 74 148 13 304 36 64 128 256), losses := [] }

theorem u21278 : Upper (D 6) (R 6) [34,72,144,5,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21279 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 13 304 96 71 135 263), lower := (rows 35 74 148 13 304 96 64 128 256), losses := [] }

theorem u21279 : Upper (D 6) (R 6) [34,72,144,5,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21280 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 468, targets := 1 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,0),(4,0)], upper := (rows 35 74 148 13 336 33 102 166 294), lower := (rows 35 74 148 13 336 33 64 128 256), losses := [] }

theorem u21280 : Upper (D 6) (R 6) [34,72,144,5,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21281 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 13 336 34 101 165 293), lower := (rows 35 74 148 13 336 34 64 128 256), losses := [] }

theorem u21281 : Upper (D 6) (R 6) [34,72,144,5,320,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21282 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 336, targets := 4 }], pairs := [(0,6),(1,2),(4,2)], upper := (rows 35 74 148 13 336 36 99 163 291), lower := (rows 35 74 148 13 336 36 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 25 32 65 129 257), good := (rows 499 90 144 475 336 32 64 128 256) },{ target := 6, region := (rows 3 2 4 8 16 44 0 131 259), good := (rows 419 427 180 429 272 36 0 128 256) }] }

theorem u21282 : Upper (D 6) (R 6) [34,72,144,5,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21283 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 14 273 33 100 228 356), lower := (rows 35 74 148 14 273 33 64 128 256), losses := [] }

theorem u21283 : Upper (D 6) (R 6) [34,72,144,6,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21284 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 148 14 273 36 97 225 353), lower := (rows 35 74 148 14 273 36 64 128 256), losses := [] }

theorem u21284 : Upper (D 6) (R 6) [34,72,144,6,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21285 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 14 273 96 101 165 293), lower := (rows 35 74 148 14 273 96 64 128 256), losses := [] }

theorem u21285 : Upper (D 6) (R 6) [34,72,144,6,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21285 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21286 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,1),(4,1)], upper := (rows 35 74 148 14 304 33 69 197 325), lower := (rows 35 74 148 14 304 33 64 128 256), losses := [] }

theorem u21286 : Upper (D 6) (R 6) [34,72,144,6,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21286 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21287 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 2 },{ cop := 0, region := 336, targets := 4 }], pairs := [(2,1),(4,1),(4,2)], upper := (rows 35 74 148 14 304 36 65 193 321), lower := (rows 35 74 148 14 304 36 64 128 256), losses := [] }

theorem u21287 : Upper (D 6) (R 6) [34,72,144,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21288 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 14 304 96 69 133 261), lower := (rows 35 74 148 14 304 96 64 128 256), losses := [] }

theorem u21288 : Upper (D 6) (R 6) [34,72,144,6,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21289 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 81 33 326 390 262), lower := (rows 35 74 148 44 81 33 64 128 256), losses := [] }

theorem u21289 : Upper (D 6) (R 6) [34,72,144,36,65,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21290 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 44 81 34 325 389 261), lower := (rows 35 74 148 44 81 34 64 128 256), losses := [] }

theorem u21290 : Upper (D 6) (R 6) [34,72,144,36,65,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21290 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21291 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 148 44 81 36 323 387 259), lower := (rows 35 74 148 44 81 36 64 128 256), losses := [] }

theorem u21291 : Upper (D 6) (R 6) [34,72,144,36,65,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21292 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 212, targets := 32 }], pairs := [(2,5),(4,5)], upper := (rows 35 74 148 44 81 288 71 135 263), lower := (rows 35 74 148 44 81 288 64 128 256), losses := [] }

theorem u21292 : Upper (D 6) (R 6) [34,72,144,36,65,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21292 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21293 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 273 33 70 198 326), lower := (rows 35 74 148 44 273 33 64 128 256), losses := [] }

theorem u21293 : Upper (D 6) (R 6) [34,72,144,36,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21293 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21294 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 74 148 44 273 34 69 197 325), lower := (rows 35 74 148 44 273 34 64 128 256), losses := [] }

theorem u21294 : Upper (D 6) (R 6) [34,72,144,36,257,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21294 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21295 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 148 44 273 36 67 195 323), lower := (rows 35 74 148 44 273 36 64 128 256), losses := [] }

theorem u21295 : Upper (D 6) (R 6) [34,72,144,36,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21296 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 44 273 96 71 135 263), lower := (rows 35 74 148 44 273 96 64 128 256), losses := [] }

theorem u21296 : Upper (D 6) (R 6) [34,72,144,36,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21297 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 33, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 74 148 44 274 33 69 197 325), lower := (rows 35 74 148 44 274 33 64 128 256), losses := [] }

theorem u21297 : Upper (D 6) (R 6) [34,72,144,36,258,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21297 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21298 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 74 148 44 274 36 65 193 321), lower := (rows 35 74 148 44 274 36 64 128 256), losses := [] }

theorem u21298 : Upper (D 6) (R 6) [34,72,144,36,258,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21298 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b21299 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 74 148 44 274 96 69 133 261), lower := (rows 35 74 148 44 274 96 64 128 256), losses := [] }

theorem u21299 : Upper (D 6) (R 6) [34,72,144,36,258,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b21299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u21299
end Delivery.IrregularNine14.P06
