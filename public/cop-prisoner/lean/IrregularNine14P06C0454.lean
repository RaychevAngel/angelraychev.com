import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0143

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b27240 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 40, targets := 65 },{ cop := 3, region := 81, targets := 2 }], pairs := [(0,1),(3,0),(3,6)], upper := (rows 97 131 262 44 88 34 85 149 277), lower := (rows 97 131 262 44 88 34 64 128 256), losses := [] }

theorem u27240 : Upper (D 6) (R 6) [96,129,258,36,72,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27240 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27241 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 40, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 131 262 44 88 36 83 147 275), lower := (rows 97 131 262 44 88 36 64 128 256), losses := [] }

theorem u27241 : Upper (D 6) (R 6) [96,129,258,36,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27241 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27242 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 390, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 262 44 88 48 71 135 263), lower := (rows 97 131 262 44 88 48 64 128 256), losses := [] }

theorem u27242 : Upper (D 6) (R 6) [96,129,258,36,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27242 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27243 : Route 9 := (fun mask => (mask,id))

def c27243 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27243 : Upper (D 6) (R 6) [96,129,264,5,6,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5,6,2] 13 (by decide) (choices 1) [16,32] r27243 c27243
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8580
  · exact u8581

def b27244 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 131 268 13 22 48 98 226 354), lower := (rows 97 131 268 13 22 48 64 128 256), losses := [] }

theorem u27244 : Upper (D 6) (R 6) [96,129,264,5,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27244 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27245 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 13 22 96 114 178 306), lower := (rows 97 131 268 13 22 96 64 128 256), losses := [] }

theorem u27245 : Upper (D 6) (R 6) [96,129,264,5,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27245 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27246 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 131 268 13 50 34 84 212 340), lower := (rows 97 131 268 13 50 34 64 128 256), losses := [] }

theorem u27246 : Upper (D 6) (R 6) [96,129,264,5,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27246 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27247 : PairBound 9 := { available := 82, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 97 131 268 13 50 36 82 210 338), lower := (rows 97 131 268 13 50 36 64 128 256), losses := [] }

theorem u27247 : Upper (D 6) (R 6) [96,129,264,5,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27247 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27248 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 268 13 50 48 70 198 326), lower := (rows 97 131 268 13 50 48 64 128 256), losses := [] }

theorem u27248 : Upper (D 6) (R 6) [96,129,264,5,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27248 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27249 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 13 50 96 86 150 278), lower := (rows 97 131 268 13 50 96 64 128 256), losses := [] }

theorem u27249 : Upper (D 6) (R 6) [96,129,264,5,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27249 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27250 : Route 9 := (fun mask => (mask,id))

def c27250 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27250 : Upper (D 6) (R 6) [96,129,264,5,36,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5,36,2] 13 (by decide) (choices 1) [2,16] r27250 c27250
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8582
  · exact u8583

def b27251 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 268 13 52 48 66 194 322), lower := (rows 97 131 268 13 52 48 64 128 256), losses := [] }

theorem u27251 : Upper (D 6) (R 6) [96,129,264,5,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27251 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27252 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 13 52 96 82 146 274), lower := (rows 97 131 268 13 52 96 64 128 256), losses := [] }

theorem u27252 : Upper (D 6) (R 6) [96,129,264,5,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27252 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27253 : Route 9 := (fun mask => (mask,id))

def c27253 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27253 : Upper (D 6) (R 6) [96,129,264,6,5,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,6,5,2] 13 (by decide) (choices 1) [16,32] r27253 c27253
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8584
  · exact u8585

def b27254 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 227, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 97 131 268 14 21 48 98 226 354), lower := (rows 97 131 268 14 21 48 64 128 256), losses := [] }

theorem u27254 : Upper (D 6) (R 6) [96,129,264,6,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27254 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27255 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 14 21 96 114 178 306), lower := (rows 97 131 268 14 21 96 64 128 256), losses := [] }

theorem u27255 : Upper (D 6) (R 6) [96,129,264,6,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27255 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27256 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 131 268 14 50 33 84 212 340), lower := (rows 97 131 268 14 50 33 64 128 256), losses := [] }

theorem u27256 : Upper (D 6) (R 6) [96,129,264,6,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27256 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27257 : PairBound 9 := { available := 81, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 97 131 268 14 50 36 81 209 337), lower := (rows 97 131 268 14 50 36 64 128 256), losses := [] }

theorem u27257 : Upper (D 6) (R 6) [96,129,264,6,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27257 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27258 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 268 14 50 48 69 197 325), lower := (rows 97 131 268 14 50 48 64 128 256), losses := [] }

theorem u27258 : Upper (D 6) (R 6) [96,129,264,6,34,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27258 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27259 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 14 50 96 85 149 277), lower := (rows 97 131 268 14 50 96 64 128 256), losses := [] }

theorem u27259 : Upper (D 6) (R 6) [96,129,264,6,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27259 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27260 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 195, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 131 268 14 52 33 82 210 338), lower := (rows 97 131 268 14 52 33 64 128 256), losses := [] }

theorem u27260 : Upper (D 6) (R 6) [96,129,264,6,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27260 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27261 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 48, targets := 65 },{ cop := 4, region := 65, targets := 4 }], pairs := [(0,2),(4,0),(4,6)], upper := (rows 97 131 268 14 52 34 81 209 337), lower := (rows 97 131 268 14 52 34 64 128 256), losses := [] }

theorem u27261 : Upper (D 6) (R 6) [96,129,264,6,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27261 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27262 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 97 131 268 14 52 48 67 195 323), lower := (rows 97 131 268 14 52 48 64 128 256), losses := [] }

theorem u27262 : Upper (D 6) (R 6) [96,129,264,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27262 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27263 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 14 52 96 83 147 275), lower := (rows 97 131 268 14 52 96 64 128 256), losses := [] }

theorem u27263 : Upper (D 6) (R 6) [96,129,264,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27263 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27264 : Route 9 := (fun mask => (mask,id))

def c27264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27264 : Upper (D 6) (R 6) [96,129,264,17,6,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,6,2] 13 (by decide) (choices 1) [4,32] r27264 c27264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8586
  · exact u8587

def b27265 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 268 25 22 36 98 226 354), lower := (rows 97 131 268 25 22 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 60 80 144 272), good := (rows 96 130 300 508 502 36 64 128 256) }] }

theorem u27265 : Upper (D 6) (R 6) [96,129,264,17,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27265 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27266 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 25 22 96 102 166 294), lower := (rows 97 131 268 25 22 96 64 128 256), losses := [] }

theorem u27266 : Upper (D 6) (R 6) [96,129,264,17,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27266 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27267 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 56, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 97 131 268 25 50 34 68 196 324), lower := (rows 97 131 268 25 50 34 64 128 256), losses := [] }

theorem u27267 : Upper (D 6) (R 6) [96,129,264,17,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27267 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27268 : Route 9 := (fun mask => (mask,id))

def c27268 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27268 : Upper (D 6) (R 6) [96,129,264,17,34,4] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,34,4] 13 (by decide) (choices 1) [2,4] r27268 c27268
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8588
  · exact u8589

def b27269 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 25 50 96 70 134 262), lower := (rows 97 131 268 25 50 96 64 128 256), losses := [] }

theorem u27269 : Upper (D 6) (R 6) [96,129,264,17,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27269 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27270 : Route 9 := (fun mask => (mask,id))

def c27270 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27270 : Upper (D 6) (R 6) [96,129,264,17,36,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17,36,2] 13 (by decide) (choices 1) [2,4] r27270 c27270
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8590
  · exact u8591

def b27271 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 268 25 52 36 66 194 322), lower := (rows 97 131 268 25 52 36 64 128 256), losses := [] }

theorem u27271 : Upper (D 6) (R 6) [96,129,264,17,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27271 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27272 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 25 52 96 70 134 262), lower := (rows 97 131 268 25 52 96 64 128 256), losses := [] }

theorem u27272 : Upper (D 6) (R 6) [96,129,264,17,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27272 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27273 : Route 9 := (fun mask => (mask,id))

def c27273 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27273 : Upper (D 6) (R 6) [96,129,264,18,5,2] 13 := by
  apply FastRouting.sound _ _ [96,129,264,18,5,2] 13 (by decide) (choices 1) [4,32] r27273 c27273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8592
  · exact u8593

def b27274 : PairBound 9 := { available := 98, camps := [{ cop := 5, region := 195, targets := 4 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 97 131 268 26 21 36 98 226 354), lower := (rows 97 131 268 26 21 36 64 128 256), losses := [] }

theorem u27274 : Upper (D 6) (R 6) [96,129,264,18,5,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27274 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27275 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 26 21 96 102 166 294), lower := (rows 97 131 268 26 21 96 64 128 256), losses := [] }

theorem u27275 : Upper (D 6) (R 6) [96,129,264,18,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27275 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27276 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 324, targets := 33 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(2,0),(2,5)], upper := (rows 97 131 268 26 52 33 70 198 326), lower := (rows 97 131 268 26 52 33 64 128 256), losses := [] }

theorem u27276 : Upper (D 6) (R 6) [96,129,264,18,36,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27276 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27277 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 65, targets := 2 }], pairs := [(0,1),(2,1),(4,0)], upper := (rows 97 131 268 26 52 34 69 197 325), lower := (rows 97 131 268 26 52 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 42 64 128 256), good := (rows 96 162 316 58 52 34 64 128 256) },{ target := 1, region := (rows 17 0 12 8 16 32 88 152 280), good := (rows 97 129 460 477 501 32 64 128 256) }] }

theorem u27277 : Upper (D 6) (R 6) [96,129,264,18,36,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27277 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27278 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 97 131 268 26 52 36 67 195 323), lower := (rows 97 131 268 26 52 36 64 128 256), losses := [] }

theorem u27278 : Upper (D 6) (R 6) [96,129,264,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27278 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27279 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 26 52 96 71 135 263), lower := (rows 97 131 268 26 52 96 64 128 256), losses := [] }

theorem u27279 : Upper (D 6) (R 6) [96,129,264,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27279 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27280 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 332, targets := 33 }], pairs := [(2,0),(2,5),(3,0)], upper := (rows 97 131 268 28 50 33 70 198 326), lower := (rows 97 131 268 28 50 33 64 128 256), losses := [] }

theorem u27280 : Upper (D 6) (R 6) [96,129,264,20,34,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27280 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27281 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 48, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 97 131 268 28 50 34 69 197 325), lower := (rows 97 131 268 28 50 34 64 128 256), losses := [] }

theorem u27281 : Upper (D 6) (R 6) [96,129,264,20,34,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27281 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27282 : PairBound 9 := { available := 67, camps := [{ cop := 5, region := 211, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 97 131 268 28 50 36 67 195 323), lower := (rows 97 131 268 28 50 36 64 128 256), losses := [] }

theorem u27282 : Upper (D 6) (R 6) [96,129,264,20,34,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27282 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27283 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 28 50 96 71 135 263), lower := (rows 97 131 268 28 50 96 64 128 256), losses := [] }

theorem u27283 : Upper (D 6) (R 6) [96,129,264,20,34,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27283 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27284 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 268 42 21 34 84 212 340), lower := (rows 97 131 268 42 21 34 64 128 256), losses := [] }

theorem u27284 : Upper (D 6) (R 6) [96,129,264,34,5,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27284 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27285 : Route 9 := (fun mask => (mask,id))

def c27285 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27285 : Upper (D 6) (R 6) [96,129,264,34,5,4] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,5,4] 13 (by decide) (choices 1) [2,16] r27285 c27285
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8594
  · exact u8595

def b27286 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 324, targets := 33 }], pairs := [(2,0),(2,5)], upper := (rows 97 131 268 42 21 48 70 198 326), lower := (rows 97 131 268 42 21 48 64 128 256), losses := [] }

theorem u27286 : Upper (D 6) (R 6) [96,129,264,34,5,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27286 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27287 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 42 21 96 86 150 278), lower := (rows 97 131 268 42 21 96 64 128 256), losses := [] }

theorem u27287 : Upper (D 6) (R 6) [96,129,264,34,5,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27287 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27288 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 131 268 42 22 33 84 212 340), lower := (rows 97 131 268 42 22 33 64 128 256), losses := [] }

theorem u27288 : Upper (D 6) (R 6) [96,129,264,34,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27288 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27289 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 40, targets := 65 },{ cop := 4, region := 97, targets := 2 }], pairs := [(0,1),(3,0),(3,6)], upper := (rows 97 131 268 42 22 36 81 209 337), lower := (rows 97 131 268 42 22 36 64 128 256), losses := [] }

theorem u27289 : Upper (D 6) (R 6) [96,129,264,34,6,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27289 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27290 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 97 131 268 42 22 48 69 197 325), lower := (rows 97 131 268 42 22 48 64 128 256), losses := [] }

theorem u27290 : Upper (D 6) (R 6) [96,129,264,34,6,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27290 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27291 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6),(2,6),(3,6)], upper := (rows 97 131 268 42 22 96 85 149 277), lower := (rows 97 131 268 42 22 96 64 128 256), losses := [] }

theorem u27291 : Upper (D 6) (R 6) [96,129,264,34,6,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27291 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27292 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 131 268 42 82 33 84 148 276), lower := (rows 97 131 268 42 82 33 64 128 256), losses := [] }

theorem u27292 : Upper (D 6) (R 6) [96,129,264,34,66,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27292 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27293 : Route 9 := (fun mask => (mask,id))

def c27293 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27293 : Upper (D 6) (R 6) [96,129,264,34,66,4] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,66,4] 13 (by decide) (choices 1) [1,4,16] r27293 c27293
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8596
  · exact u8597
  · exact u8598

def b27294 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 42 82 48 69 133 261), lower := (rows 97 131 268 42 82 48 64 128 256), losses := [] }

theorem u27294 : Upper (D 6) (R 6) [96,129,264,34,66,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27294 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27295 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 340, targets := 33 }], pairs := [(2,0),(2,5),(4,0)], upper := (rows 97 131 268 42 84 33 86 150 278), lower := (rows 97 131 268 42 84 33 64 128 256), losses := [] }

theorem u27295 : Upper (D 6) (R 6) [96,129,264,34,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27295 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27296 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 69 }], pairs := [(3,0),(3,2),(3,6)], upper := (rows 97 131 268 42 84 34 85 149 277), lower := (rows 97 131 268 42 84 34 64 128 256), losses := [] }

theorem u27296 : Upper (D 6) (R 6) [96,129,264,34,68,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27296 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r27297 : Route 9 := (fun mask => (mask,id))

def c27297 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u27297 : Upper (D 6) (R 6) [96,129,264,34,68,4] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34,68,4] 13 (by decide) (choices 1) [1,2,16] r27297 c27297
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8599
  · exact u8600
  · exact u8601

def b27298 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 131 268 42 84 48 71 135 263), lower := (rows 97 131 268 42 84 48 64 128 256), losses := [] }

theorem u27298 : Upper (D 6) (R 6) [96,129,264,34,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27298 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b27299 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,2),(1,2)], upper := (rows 97 131 268 44 22 33 82 210 338), lower := (rows 97 131 268 44 22 33 64 128 256), losses := [] }

theorem u27299 : Upper (D 6) (R 6) [96,129,264,36,6,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b27299 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u27299
end Delivery.IrregularNine14.P06
