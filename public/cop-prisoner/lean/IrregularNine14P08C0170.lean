import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0047

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b10200 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 37 280 208 161 225 161 417), lower := (rows 67 14 37 280 208 32 64 128 256), losses := [] }

theorem u10200 : Upper (D 8) (R 8) [66,12,33,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10200 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10201 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 14 37 296 49 240 208 208 464), lower := (rows 67 14 37 296 49 32 64 128 256), losses := [] }

theorem u10201 : Upper (D 8) (R 8) [66,12,33,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10201 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10202 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 296 81 176 240 176 432), lower := (rows 67 14 37 296 81 32 64 128 256), losses := [] }

theorem u10202 : Upper (D 8) (R 8) [66,12,33,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10202 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10203 : Route 9 := (fun mask => (mask,id))

def c10203 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10203 : Upper (D 8) (R 8) [66,12,33,288,96] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288,96] 13 (by decide) (choices 1) [1,16,128] r10203 c10203
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2830
  · exact u2831
  · exact u2832

def b10204 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 296 145 240 240 240 496), lower := (rows 67 14 37 296 145 32 64 128 256), losses := [] }

theorem u10204 : Upper (D 8) (R 8) [66,12,33,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10204 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10205 : Route 9 := (fun mask => (mask,id))

def c10205 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u10205 : Upper (D 8) (R 8) [66,12,33,288,160] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288,160] 13 (by decide) (choices 1) [1,16,64,128] r10205 c10205
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2833
  · exact u2834
  · exact u2835
  · exact u2836

def r10206 : Route 9 := (fun mask => (mask,id))

def c10206 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10206 : Upper (D 8) (R 8) [66,12,33,288,192] 13 := by
  apply FastRouting.sound _ _ [66,12,33,288,192] 13 (by decide) (choices 1) [1,16,128] r10206 c10206
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2837
  · exact u2838
  · exact u2839

def b10207 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 67 14 37 392 49 240 240 240 496), lower := (rows 67 14 37 392 49 32 64 128 256), losses := [] }

theorem u10207 : Upper (D 8) (R 8) [66,12,33,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10207 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10208 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 37 392 81 176 240 176 432), lower := (rows 67 14 37 392 81 32 64 128 256), losses := [] }

theorem u10208 : Upper (D 8) (R 8) [66,12,33,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10208 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10209 : Route 9 := (fun mask => (mask,id))

def c10209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10209 : Upper (D 8) (R 8) [66,12,33,384,96] 13 := by
  apply FastRouting.sound _ _ [66,12,33,384,96] 13 (by decide) (choices 1) [1,16,128] r10209 c10209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2840
  · exact u2841
  · exact u2842

def b10210 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 360, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 37 392 145 112 112 240 368), lower := (rows 67 14 37 392 145 32 64 128 256), losses := [] }

theorem u10210 : Upper (D 8) (R 8) [66,12,33,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10210 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10211 : Route 9 := (fun mask => (mask,id))

def c10211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10211 : Upper (D 8) (R 8) [66,12,33,384,160] 13 := by
  apply FastRouting.sound _ _ [66,12,33,384,160] 13 (by decide) (choices 1) [1,16,64] r10211 c10211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2843
  · exact u2844
  · exact u2845

def r10212 : Route 9 := (fun mask => (mask,id))

def c10212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u10212 : Upper (D 8) (R 8) [66,12,33,384,192] 13 := by
  apply FastRouting.sound _ _ [66,12,33,384,192] 13 (by decide) (choices 1) [1,16] r10212 c10212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2846
  · exact u2847

def b10213 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 52 137 49 480 480 480 480), lower := (rows 67 14 52 137 49 32 64 128 256), losses := [] }

theorem u10213 : Upper (D 8) (R 8) [66,12,48,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10213 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10214 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 137 81 416 480 416 416), lower := (rows 67 14 52 137 81 32 64 128 256), losses := [] }

theorem u10214 : Upper (D 8) (R 8) [66,12,48,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10214 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10215 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 137 112 417 481 417 417), lower := (rows 67 14 52 137 112 32 64 128 256), losses := [] }

theorem u10215 : Upper (D 8) (R 8) [66,12,48,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10215 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10216 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 14 52 137 145 352 352 480 352), lower := (rows 67 14 52 137 145 32 64 128 256), losses := [] }

theorem u10216 : Upper (D 8) (R 8) [66,12,48,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10216 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10217 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 137 176 353 353 481 353), lower := (rows 67 14 52 137 176 32 64 128 256), losses := [] }

theorem u10217 : Upper (D 8) (R 8) [66,12,48,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10217 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10218 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 137 208 289 353 417 289), lower := (rows 67 14 52 137 208 32 64 128 256), losses := [] }

theorem u10218 : Upper (D 8) (R 8) [66,12,48,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10218 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10219 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 137 273 224 224 224 480), lower := (rows 67 14 52 137 273 32 64 128 256), losses := [] }

theorem u10219 : Upper (D 8) (R 8) [66,12,48,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10219 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10220 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 137 304 225 225 225 481), lower := (rows 67 14 52 137 304 32 64 128 256), losses := [] }

theorem u10220 : Upper (D 8) (R 8) [66,12,48,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10220 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10221 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 137 336 161 225 161 417), lower := (rows 67 14 52 137 336 32 64 128 256), losses := [] }

theorem u10221 : Upper (D 8) (R 8) [66,12,48,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10221 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10222 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 137 400 97 97 225 353), lower := (rows 67 14 52 137 400 32 64 128 256), losses := [] }

theorem u10222 : Upper (D 8) (R 8) [66,12,48,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10222 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10223 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 168 49 481 449 449 449), lower := (rows 67 14 52 168 49 32 64 128 256), losses := [] }

theorem u10223 : Upper (D 8) (R 8) [66,12,48,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10223 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10224 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 168 81 417 481 417 417), lower := (rows 67 14 52 168 81 32 64 128 256), losses := [] }

theorem u10224 : Upper (D 8) (R 8) [66,12,48,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10224 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10225 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 168 112 417 449 385 385), lower := (rows 67 14 52 168 112 32 64 128 256), losses := [] }

theorem u10225 : Upper (D 8) (R 8) [66,12,48,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10225 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10226 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 168 145 353 353 481 353), lower := (rows 67 14 52 168 145 32 64 128 256), losses := [] }

theorem u10226 : Upper (D 8) (R 8) [66,12,48,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10226 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10227 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 22, targets := 1 }], pairs := [(1,0)], upper := (rows 67 14 52 168 176 353 321 449 321), lower := (rows 67 14 52 168 176 32 64 128 256), losses := [] }

theorem u10227 : Upper (D 8) (R 8) [66,12,48,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10227 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10228 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 168 208 289 353 417 289), lower := (rows 67 14 52 168 208 32 64 128 256), losses := [] }

theorem u10228 : Upper (D 8) (R 8) [66,12,48,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10228 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10229 : Route 9 := (fun mask => (mask,id))

def c10229 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10229 : Upper (D 8) (R 8) [66,12,48,160,257] 13 := by
  apply FastRouting.sound _ _ [66,12,48,160,257] 13 (by decide) (choices 1) [1,64,128] r10229 c10229
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2848
  · exact u2849
  · exact u2850

def b10230 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 168 304 225 193 193 449), lower := (rows 67 14 52 168 304 32 64 128 256), losses := [] }

theorem u10230 : Upper (D 8) (R 8) [66,12,48,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10230 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10231 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 168 336 161 225 161 417), lower := (rows 67 14 52 168 336 32 64 128 256), losses := [] }

theorem u10231 : Upper (D 8) (R 8) [66,12,48,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10231 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10232 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 168 400 97 97 225 353), lower := (rows 67 14 52 168 400 32 64 128 256), losses := [] }

theorem u10232 : Upper (D 8) (R 8) [66,12,48,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10232 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10233 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 52 265 49 224 224 224 480), lower := (rows 67 14 52 265 49 32 64 128 256), losses := [] }

theorem u10233 : Upper (D 8) (R 8) [66,12,48,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10233 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10234 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 265 81 160 224 160 416), lower := (rows 67 14 52 265 81 32 64 128 256), losses := [] }

theorem u10234 : Upper (D 8) (R 8) [66,12,48,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10234 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10235 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 265 112 161 225 161 417), lower := (rows 67 14 52 265 112 32 64 128 256), losses := [] }

theorem u10235 : Upper (D 8) (R 8) [66,12,48,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10235 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10236 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 265 145 224 224 224 480), lower := (rows 67 14 52 265 145 32 64 128 256), losses := [] }

theorem u10236 : Upper (D 8) (R 8) [66,12,48,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10236 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10237 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 265 176 225 225 225 481), lower := (rows 67 14 52 265 176 32 64 128 256), losses := [] }

theorem u10237 : Upper (D 8) (R 8) [66,12,48,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10237 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10238 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 265 208 161 225 161 417), lower := (rows 67 14 52 265 208 32 64 128 256), losses := [] }

theorem u10238 : Upper (D 8) (R 8) [66,12,48,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10238 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10239 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 296 49 225 193 193 449), lower := (rows 67 14 52 296 49 32 64 128 256), losses := [] }

theorem u10239 : Upper (D 8) (R 8) [66,12,48,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10239 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10240 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 296 81 161 225 161 417), lower := (rows 67 14 52 296 81 32 64 128 256), losses := [] }

theorem u10240 : Upper (D 8) (R 8) [66,12,48,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10240 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10241 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 296 112 161 193 129 385), lower := (rows 67 14 52 296 112 32 64 128 256), losses := [] }

theorem u10241 : Upper (D 8) (R 8) [66,12,48,288,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10241 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10242 : Route 9 := (fun mask => (mask,id))

def c10242 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u10242 : Upper (D 8) (R 8) [66,12,48,288,129] 13 := by
  apply FastRouting.sound _ _ [66,12,48,288,129] 13 (by decide) (choices 1) [1,64,128] r10242 c10242
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2851
  · exact u2852
  · exact u2853

def b10243 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 296 176 225 193 193 449), lower := (rows 67 14 52 296 176 32 64 128 256), losses := [] }

theorem u10243 : Upper (D 8) (R 8) [66,12,48,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10243 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10244 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 296 208 161 225 161 417), lower := (rows 67 14 52 296 208 32 64 128 256), losses := [] }

theorem u10244 : Upper (D 8) (R 8) [66,12,48,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10244 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10245 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 392 49 225 225 225 481), lower := (rows 67 14 52 392 49 32 64 128 256), losses := [] }

theorem u10245 : Upper (D 8) (R 8) [66,12,48,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10245 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10246 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 52 392 81 161 225 161 417), lower := (rows 67 14 52 392 81 32 64 128 256), losses := [] }

theorem u10246 : Upper (D 8) (R 8) [66,12,48,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10246 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10247 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 392 112 161 225 161 417), lower := (rows 67 14 52 392 112 32 64 128 256), losses := [] }

theorem u10247 : Upper (D 8) (R 8) [66,12,48,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10247 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10248 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 52 392 145 97 97 225 353), lower := (rows 67 14 52 392 145 32 64 128 256), losses := [] }

theorem u10248 : Upper (D 8) (R 8) [66,12,48,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10248 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10249 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 67 14 52 392 176 97 97 225 353), lower := (rows 67 14 52 392 176 32 64 128 256), losses := [] }

theorem u10249 : Upper (D 8) (R 8) [66,12,48,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10249 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10250 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 67 14 52 392 208 33 97 161 289), lower := (rows 67 14 52 392 208 32 64 128 256), losses := [] }

theorem u10250 : Upper (D 8) (R 8) [66,12,48,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10250 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10251 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 280 49 224 224 224 480), lower := (rows 67 14 133 280 49 32 64 128 256), losses := [] }

theorem u10251 : Upper (D 8) (R 8) [66,12,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10251 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10252 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 133 280 81 160 224 160 416), lower := (rows 67 14 133 280 81 32 64 128 256), losses := [] }

theorem u10252 : Upper (D 8) (R 8) [66,12,129,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10252 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10253 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 133 280 112 161 225 161 417), lower := (rows 67 14 133 280 112 32 64 128 256), losses := [] }

theorem u10253 : Upper (D 8) (R 8) [66,12,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10253 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10254 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 67 14 133 280 145 96 96 224 352), lower := (rows 67 14 133 280 145 32 64 128 256), losses := [] }

theorem u10254 : Upper (D 8) (R 8) [66,12,129,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10254 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10255 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 67 14 133 280 176 97 97 225 353), lower := (rows 67 14 133 280 176 32 64 128 256), losses := [] }

theorem u10255 : Upper (D 8) (R 8) [66,12,129,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10255 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10256 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 67 14 133 280 208 33 97 161 289), lower := (rows 67 14 133 280 208 32 64 128 256), losses := [] }

theorem u10256 : Upper (D 8) (R 8) [66,12,129,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10256 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10257 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 456, targets := 1 }], pairs := [(3,0)], upper := (rows 67 14 133 296 49 240 240 240 496), lower := (rows 67 14 133 296 49 32 64 128 256), losses := [] }

theorem u10257 : Upper (D 8) (R 8) [66,12,129,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10257 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10258 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6)], upper := (rows 67 14 133 296 81 176 240 176 432), lower := (rows 67 14 133 296 81 32 64 128 256), losses := [] }

theorem u10258 : Upper (D 8) (R 8) [66,12,129,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10258 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r10259 : Route 9 := (fun mask => (mask,id))

def c10259 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u10259 : Upper (D 8) (R 8) [66,12,129,288,96] 13 := by
  apply FastRouting.sound _ _ [66,12,129,288,96] 13 (by decide) (choices 1) [1,16,128] r10259 c10259
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2854
  · exact u2855
  · exact u2856

#print axioms u10259
end Delivery.IrregularNine14.P08
