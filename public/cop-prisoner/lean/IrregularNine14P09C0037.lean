import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0002

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2220 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 56 273 160 66 448 320), lower := (rows 97 7 140 56 273 160 66 128 256), losses := [] }

theorem u2220 : Upper (D 9) (R 9) [96,5,136,48,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2220 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2221 : Route 9 := (fun mask => (mask,id))

def c2221 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2221 : Upper (D 9) (R 9) [96,5,136,48,257,128,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,257,128,256] 13 (by decide) (choices 1) [2,64] r2221 c2221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u124
  · exact u125

def b2222 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(4,5),(4,7)], upper := (rows 97 7 140 56 274 160 65 448 320), lower := (rows 97 7 140 56 274 160 65 128 256), losses := [] }

theorem u2222 : Upper (D 9) (R 9) [96,5,136,48,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2222 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2223 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 321, targets := 128 },{ cop := 6, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,5),(4,7)], upper := (rows 97 7 140 56 274 160 320 193 321), lower := (rows 97 7 140 56 274 160 320 128 256), losses := [{ target := 7, region := (rows 41 6 4 8 22 32 383 0 303), good := (rows 353 343 351 377 338 353 320 0 320) }] }

theorem u2223 : Upper (D 9) (R 9) [96,5,136,48,258,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2223 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2224 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 99, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 140 56 336 34 65 384 384), lower := (rows 97 7 140 56 336 34 65 128 256), losses := [] }

theorem u2224 : Upper (D 9) (R 9) [96,5,136,48,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2224 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2225 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 56 336 34 192 385 257), lower := (rows 97 7 140 56 336 34 192 128 256), losses := [] }

theorem u2225 : Upper (D 9) (R 9) [96,5,136,48,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2225 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2226 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 56 336 34 320 129 385), lower := (rows 97 7 140 56 336 34 320 128 256), losses := [] }

theorem u2226 : Upper (D 9) (R 9) [96,5,136,48,320,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2226 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2227 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(4,5),(4,7)], upper := (rows 97 7 140 56 336 160 65 386 258), lower := (rows 97 7 140 56 336 160 65 128 256), losses := [] }

theorem u2227 : Upper (D 9) (R 9) [96,5,136,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2227 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2228 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 56 336 160 66 385 257), lower := (rows 97 7 140 56 336 160 66 128 256), losses := [] }

theorem u2228 : Upper (D 9) (R 9) [96,5,136,48,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2228 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2229 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 97 7 140 56 336 160 320 131 259), lower := (rows 97 7 140 56 336 160 320 128 256), losses := [] }

theorem u2229 : Upper (D 9) (R 9) [96,5,136,48,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2229 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2230 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 140 56 400 34 65 448 320), lower := (rows 97 7 140 56 400 34 65 128 256), losses := [] }

theorem u2230 : Upper (D 9) (R 9) [96,5,136,48,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2230 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2231 : Route 9 := (fun mask => (mask,id))

def c2231 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2231 : Upper (D 9) (R 9) [96,5,136,48,384,2,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,48,384,2,256] 13 (by decide) (choices 1) [1,64] r2231 c2231
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u126
  · exact u127

def b2232 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 1, region := 496, targets := 1 }], pairs := [(1,5),(2,5),(3,5),(4,0)], upper := (rows 97 7 140 265 50 288 80 192 448), lower := (rows 97 7 140 265 50 288 80 128 256), losses := [] }

theorem u2232 : Upper (D 9) (R 9) [96,5,136,257,34,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2232 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2233 : Route 9 := (fun mask => (mask,id))

def c2233 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2233 : Upper (D 9) (R 9) [96,5,136,257,34,256,128] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257,34,256,128] 13 (by decide) (choices 1) [16,64] r2233 c2233
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u128
  · exact u129

def b2234 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 361, targets := 128 },{ cop := 1, region := 496, targets := 1 }], pairs := [(0,7),(2,0),(3,7),(4,0)], upper := (rows 97 7 140 265 146 48 320 224 352), lower := (rows 97 7 140 265 146 48 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 379 179 307), good := (rows 480 502 204 460 498 496 320 128 320) }] }

theorem u2234 : Upper (D 9) (R 9) [96,5,136,257,130,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2234 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2235 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 146 96 320 176 304), lower := (rows 97 7 140 265 146 96 320 128 256), losses := [] }

theorem u2235 : Upper (D 9) (R 9) [96,5,136,257,130,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2235 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2236 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 144, targets := 1 },{ cop := 0, region := 144, targets := 256 }], pairs := [(2,0),(4,0),(4,6),(4,8)], upper := (rows 97 7 140 265 176 288 66 208 336), lower := (rows 97 7 140 265 176 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 95 363 66 195 323), good := (rows 496 502 188 444 176 288 498 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 33 23 188 297 176 288 2 128 288) }] }

theorem u2236 : Upper (D 9) (R 9) [96,5,136,257,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2236 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2237 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 7 140 265 176 288 80 194 322), lower := (rows 97 7 140 265 176 288 80 128 256), losses := [] }

theorem u2237 : Upper (D 9) (R 9) [96,5,136,257,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2237 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2238 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 264, targets := 128 },{ cop := 1, region := 496, targets := 1 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,8),(2,0),(3,7),(4,0)], upper := (rows 97 7 140 265 274 48 192 224 352), lower := (rows 97 7 140 265 274 48 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 18 50 255 179 307), good := (rows 480 502 204 460 498 496 192 192 256) }] }

theorem u2238 : Upper (D 9) (R 9) [96,5,136,257,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2238 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2239 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 265 274 96 192 176 304), lower := (rows 97 7 140 265 274 96 192 128 256), losses := [] }

theorem u2239 : Upper (D 9) (R 9) [96,5,136,257,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2239 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2240 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 97 7 140 265 304 34 80 192 448), lower := (rows 97 7 140 265 304 34 80 128 256), losses := [] }

theorem u2240 : Upper (D 9) (R 9) [96,5,136,257,288,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2240 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2241 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 265 304 34 192 208 336), lower := (rows 97 7 140 265 304 34 192 128 256), losses := [] }

theorem u2241 : Upper (D 9) (R 9) [96,5,136,257,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2241 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2242 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 265 304 160 66 208 336), lower := (rows 97 7 140 265 304 160 66 128 256), losses := [] }

theorem u2242 : Upper (D 9) (R 9) [96,5,136,257,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2242 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2243 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 7 140 265 304 160 80 194 322), lower := (rows 97 7 140 265 304 160 80 128 256), losses := [] }

theorem u2243 : Upper (D 9) (R 9) [96,5,136,257,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2243 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2244 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 0, region := 264, targets := 128 }], pairs := [(2,0),(3,7),(4,0)], upper := (rows 97 7 140 265 400 34 80 224 352), lower := (rows 97 7 140 265 400 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 59 34 127 163 291), good := (rows 496 502 220 476 464 498 80 128 256) }] }

theorem u2244 : Upper (D 9) (R 9) [96,5,136,257,384,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2244 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2245 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 140 265 400 34 96 208 336), lower := (rows 97 7 140 265 400 34 96 128 256), losses := [] }

theorem u2245 : Upper (D 9) (R 9) [96,5,136,257,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2245 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2246 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 140 265 400 48 96 194 322), lower := (rows 97 7 140 265 400 48 96 128 256), losses := [] }

theorem u2246 : Upper (D 9) (R 9) [96,5,136,257,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2246 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2247 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 177, targets := 256 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(0,8),(2,0),(4,8)], upper := (rows 97 7 140 266 145 48 320 224 352), lower := (rows 97 7 140 266 145 48 320 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 48 379 177 305), good := (rows 480 462 204 334 496 496 320 128 320) }] }

theorem u2247 : Upper (D 9) (R 9) [96,5,136,258,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2247 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2248 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 5, region := 1, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 145 96 320 176 304), lower := (rows 97 7 140 266 145 96 320 128 256), losses := [] }

theorem u2248 : Upper (D 9) (R 9) [96,5,136,258,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2248 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2249 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 140 266 273 48 96 192 448), lower := (rows 97 7 140 266 273 48 96 128 256), losses := [] }

theorem u2249 : Upper (D 9) (R 9) [96,5,136,258,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2249 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2250 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 305, targets := 128 },{ cop := 4, region := 225, targets := 256 }], pairs := [(0,7),(0,8),(2,0),(4,7)], upper := (rows 97 7 140 266 273 48 192 224 352), lower := (rows 97 7 140 266 273 48 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 48 247 177 305), good := (rows 480 462 204 334 496 496 192 192 256) }] }

theorem u2250 : Upper (D 9) (R 9) [96,5,136,258,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2250 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2251 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 266 273 96 192 176 304), lower := (rows 97 7 140 266 273 96 192 128 256), losses := [] }

theorem u2251 : Upper (D 9) (R 9) [96,5,136,258,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2251 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2252 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 99, targets := 256 },{ cop := 5, region := 337, targets := 128 },{ cop := 0, region := 272, targets := 1 }], pairs := [(0,7),(0,8),(1,8),(4,0),(4,7)], upper := (rows 97 7 140 266 304 160 65 208 336), lower := (rows 97 7 140 266 304 160 65 128 256), losses := [] }

theorem u2252 : Upper (D 9) (R 9) [96,5,136,258,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2252 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2253 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 398, targets := 32 },{ cop := 5, region := 337, targets := 128 }], pairs := [(0,7),(1,5),(2,5),(3,5)], upper := (rows 97 7 140 266 304 160 80 193 321), lower := (rows 97 7 140 266 304 160 80 128 256), losses := [] }

theorem u2253 : Upper (D 9) (R 9) [96,5,136,258,288,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2253 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2254 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 400, targets := 1 },{ cop := 4, region := 97, targets := 128 },{ cop := 4, region := 97, targets := 256 }], pairs := [(0,7),(0,8),(2,0),(4,0)], upper := (rows 97 7 140 266 400 33 80 224 352), lower := (rows 97 7 140 266 400 33 80 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 51 32 123 161 289), good := (rows 496 478 204 350 464 496 80 128 256) }] }

theorem u2254 : Upper (D 9) (R 9) [96,5,136,258,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2254 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2255 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 414, targets := 32 }], pairs := [(1,5),(2,5),(3,5),(4,5)], upper := (rows 97 7 140 266 400 48 96 193 321), lower := (rows 97 7 140 266 400 48 96 128 256), losses := [] }

theorem u2255 : Upper (D 9) (R 9) [96,5,136,258,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2255 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2256 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,7),(1,7),(2,0),(4,8)], upper := (rows 97 7 140 280 145 34 320 224 352), lower := (rows 97 7 140 280 145 34 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 34 379 163 291), good := (rows 480 486 204 348 476 482 320 128 320) }] }

theorem u2256 : Upper (D 9) (R 9) [96,5,136,272,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2256 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2257 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 140 280 145 96 320 162 290), lower := (rows 97 7 140 280 145 96 320 128 256), losses := [] }

theorem u2257 : Upper (D 9) (R 9) [96,5,136,272,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2257 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2258 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 280 176 33 66 448 320), lower := (rows 97 7 140 280 176 33 66 128 256), losses := [] }

theorem u2258 : Upper (D 9) (R 9) [96,5,136,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2258 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2259 : Route 9 := (fun mask => (mask,id))

def c2259 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2259 : Upper (D 9) (R 9) [96,5,136,272,160,1,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272,160,1,256] 13 (by decide) (choices 1) [2,64] r2259 c2259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u130
  · exact u131

def b2260 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 280 176 34 65 448 320), lower := (rows 97 7 140 280 176 34 65 128 256), losses := [] }

theorem u2260 : Upper (D 9) (R 9) [96,5,136,272,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2260 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2261 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 144, targets := 256 },{ cop := 4, region := 329, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,8)], upper := (rows 97 7 140 280 176 34 320 193 321), lower := (rows 97 7 140 280 176 34 320 128 256), losses := [] }

theorem u2261 : Upper (D 9) (R 9) [96,5,136,272,160,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2261 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2262 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 4, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,0),(4,6)], upper := (rows 97 7 140 280 176 288 65 194 322), lower := (rows 97 7 140 280 176 288 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 64 128 256), good := (rows 96 22 188 312 176 288 64 128 288) },{ target := 6, region := (rows 1 2 4 8 20 296 0 128 256), good := (rows 33 23 188 312 176 288 1 128 288) }] }

theorem u2262 : Upper (D 9) (R 9) [96,5,136,272,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2262 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2263 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,7),(1,7),(4,0),(4,8)], upper := (rows 97 7 140 280 176 288 66 193 321), lower := (rows 97 7 140 280 176 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 296 66 128 256), good := (rows 96 86 188 312 176 288 66 128 288) }] }

theorem u2263 : Upper (D 9) (R 9) [96,5,136,272,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2263 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2264 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 428, targets := 65 },{ cop := 2, region := 97, targets := 256 }], pairs := [(0,8),(2,0),(2,6),(3,0),(3,6)], upper := (rows 97 7 140 296 82 160 65 400 272), lower := (rows 97 7 140 296 82 160 65 128 256), losses := [] }

theorem u2264 : Upper (D 9) (R 9) [96,5,136,288,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2264 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2265 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 115, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 82 160 80 385 257), lower := (rows 97 7 140 296 82 160 80 128 256), losses := [] }

theorem u2265 : Upper (D 9) (R 9) [96,5,136,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2265 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2266 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 336, targets := 32 },{ cop := 1, region := 336, targets := 128 },{ cop := 3, region := 65, targets := 128 },{ cop := 4, region := 161, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,5),(4,7)], upper := (rows 97 7 140 296 82 160 320 145 273), lower := (rows 97 7 140 296 82 160 320 128 256), losses := [{ target := 7, region := (rows 9 6 4 8 22 32 350 0 262), good := (rows 97 343 351 361 338 32 320 0 320) }] }

theorem u2266 : Upper (D 9) (R 9) [96,5,136,288,66,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2266 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2267 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 115, targets := 256 }], pairs := [(0,8),(1,8),(4,8)], upper := (rows 97 7 140 296 145 34 80 448 320), lower := (rows 97 7 140 296 145 34 80 128 256), losses := [] }

theorem u2267 : Upper (D 9) (R 9) [96,5,136,288,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2267 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2268 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(2,5),(4,5),(4,8)], upper := (rows 97 7 140 296 145 34 320 208 336), lower := (rows 97 7 140 296 145 34 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 19 0 379 179 307), good := (rows 465 471 204 460 465 466 320 128 320) }] }

theorem u2268 : Upper (D 9) (R 9) [96,5,136,288,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2268 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2269 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 115, targets := 256 }], pairs := [(0,8),(1,8),(4,8)], upper := (rows 97 7 140 296 145 48 66 448 320), lower := (rows 97 7 140 296 145 48 66 128 256), losses := [] }

theorem u2269 : Upper (D 9) (R 9) [96,5,136,288,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2269 [(5,4),(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r2270 : Route 9 := (fun mask => (mask,id))

def c2270 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2270 : Upper (D 9) (R 9) [96,5,136,288,129,16,256] 13 := by
  apply FastRouting.sound _ _ [96,5,136,288,129,16,256] 13 (by decide) (choices 1) [2,64] r2270 c2270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u132
  · exact u133

def b2271 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 296 208 33 66 400 272), lower := (rows 97 7 140 296 208 33 66 128 256), losses := [] }

theorem u2271 : Upper (D 9) (R 9) [96,5,136,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2271 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2272 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 2, region := 113, targets := 256 }], pairs := [(0,8),(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 208 33 80 386 258), lower := (rows 97 7 140 296 208 33 80 128 256), losses := [] }

theorem u2272 : Upper (D 9) (R 9) [96,5,136,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2272 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2273 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 464, targets := 33 },{ cop := 4, region := 33, targets := 384 },{ cop := 6, region := 41, targets := 128 }], pairs := [(0,7),(0,8),(3,7),(4,0),(4,5)], upper := (rows 97 7 140 296 208 33 320 146 274), lower := (rows 97 7 140 296 208 33 320 128 256), losses := [] }

theorem u2273 : Upper (D 9) (R 9) [96,5,136,288,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2273 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2274 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 412, targets := 1 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(2,0),(3,0),(4,0)], upper := (rows 97 7 140 296 208 34 65 400 272), lower := (rows 97 7 140 296 208 34 65 128 256), losses := [] }

theorem u2274 : Upper (D 9) (R 9) [96,5,136,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2274 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2275 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 7 140 296 208 34 80 385 257), lower := (rows 97 7 140 296 208 34 80 128 256), losses := [] }

theorem u2275 : Upper (D 9) (R 9) [96,5,136,288,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2275 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2276 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 256 },{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7),(4,0),(4,5),(4,8)], upper := (rows 97 7 140 296 208 34 320 145 273), lower := (rows 97 7 140 296 208 34 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 34 328 128 256), good := (rows 96 54 220 360 208 34 320 128 320) }] }

theorem u2276 : Upper (D 9) (R 9) [96,5,136,288,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2276 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2277 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 396, targets := 1 },{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7),(2,0),(3,0)], upper := (rows 97 7 140 296 273 34 80 192 448), lower := (rows 97 7 140 296 273 34 80 128 256), losses := [] }

theorem u2277 : Upper (D 9) (R 9) [96,5,136,288,257,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2277 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2278 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 296 273 34 192 208 336), lower := (rows 97 7 140 296 273 34 192 128 256), losses := [] }

theorem u2278 : Upper (D 9) (R 9) [96,5,136,288,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2278 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2279 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 280, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(3,7),(4,7)], upper := (rows 97 7 140 296 273 160 66 208 336), lower := (rows 97 7 140 296 273 160 66 128 256), losses := [] }

theorem u2279 : Upper (D 9) (R 9) [96,5,136,288,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2279 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2279
end Delivery.IrregularNine14.P09
