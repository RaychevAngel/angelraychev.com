import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0003
import IrregularNine14P09C0004

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r3000 : Route 9 := (fun mask => (mask,id))

def c3000 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3000 : Upper (D 9) (R 9) [6,9,48,96,129,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,129,256] 13 (by decide) (choices 1) [128,256] r3000 c3000
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u206
  · exact u207

def b3001 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 52 104 208 33 448 384 384), lower := (rows 7 11 52 104 208 33 64 128 256), losses := [] }

theorem u3001 : Upper (D 9) (R 9) [6,9,48,96,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3001 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 2, region := 331, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 52 104 208 160 321 385 257), lower := (rows 7 11 52 104 208 160 64 128 256), losses := [] }

theorem u3002 : Upper (D 9) (R 9) [6,9,48,96,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3002 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3003 : Route 9 := (fun mask => (mask,id))

def c3003 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3003 : Upper (D 9) (R 9) [6,9,48,96,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,192,256] 13 (by decide) (choices 1) [1,128,256] r3003 c3003
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u208
  · exact u209
  · exact u210

def r3004 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3004 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3004 : Upper (D 9) (R 9) [6,9,48,96,384,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96,384,1] 13 (by decide) (choices 1) [128] r3004 c3004
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u211

def b3005 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,6),(1,6),(2,6),(3,0),(4,6)], upper := (rows 7 11 52 104 400 96 449 385 385), lower := (rows 7 11 52 104 400 96 64 128 256), losses := [] }

theorem u3005 : Upper (D 9) (R 9) [6,9,48,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3005 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3006 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 331, targets := 128 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,7),(1,7),(2,0),(2,6),(3,7)], upper := (rows 7 11 52 104 400 160 321 449 321), lower := (rows 7 11 52 104 400 160 64 128 256), losses := [] }

theorem u3006 : Upper (D 9) (R 9) [6,9,48,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3006 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3007 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 55, targets := 256 },{ cop := 4, region := 420, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(4,8)], upper := (rows 7 11 52 200 81 160 352 416 288), lower := (rows 7 11 52 200 81 160 64 128 256), losses := [] }

theorem u3007 : Upper (D 9) (R 9) [6,9,48,192,65,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3007 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3008 : Route 9 := (fun mask => (mask,id))

def c3008 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3008 : Upper (D 9) (R 9) [6,9,48,192,65,256] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,65,256] 13 (by decide) (choices 1) [32,128,256] r3008 c3008
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u212
  · exact u213
  · exact u214

def r3009 : Route 9 := (fun mask => (mask,id))

def c3009 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3009 : Upper (D 9) (R 9) [6,9,48,192,257,64] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,257,64] 13 (by decide) (choices 1) [32,128,256] r3009 c3009
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u215
  · exact u216
  · exact u217

def b3010 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,0),(3,8)], upper := (rows 7 11 52 200 273 288 224 224 480), lower := (rows 7 11 52 200 273 288 64 128 256), losses := [] }

theorem u3010 : Upper (D 9) (R 9) [6,9,48,192,257,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3010 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3011 : Route 9 := (fun mask => (mask,id))

def c3011 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u3011 : Upper (D 9) (R 9) [6,9,48,192,320,1] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,1] 13 (by decide) (choices 1) [32,128,256] r3011 c3011
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u218
  · exact u219
  · exact u220

def r3012 : Route 9 := (fun mask => (mask,id))

def c3012 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3012 : Upper (D 9) (R 9) [6,9,48,192,320,128] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192,320,128] 13 (by decide) (choices 1) [1,32,256] r3012 c3012
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u221
  · exact u222
  · exact u223

def b3013 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 203, targets := 256 },{ cop := 4, region := 36, targets := 65 }], pairs := [(0,8),(1,8),(2,0),(2,6),(3,8)], upper := (rows 7 11 52 200 336 288 225 161 417), lower := (rows 7 11 52 200 336 288 64 128 256), losses := [] }

theorem u3013 : Upper (D 9) (R 9) [6,9,48,192,320,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3013 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 4, region := 356, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 56 145 96 448 384 384), lower := (rows 7 11 100 56 145 96 64 128 256), losses := [] }

theorem u3014 : Upper (D 9) (R 9) [6,9,96,48,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3014 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 42, targets := 320 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(1,6),(1,8),(3,6),(3,8)], upper := (rows 7 11 100 56 145 160 320 448 320), lower := (rows 7 11 100 56 145 160 64 128 256), losses := [] }

theorem u3015 : Upper (D 9) (R 9) [6,9,96,48,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3015 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3016 : Route 9 := (fun mask => (mask,id))

def c3016 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3016 : Upper (D 9) (R 9) [6,9,96,48,129,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,129,256] 13 (by decide) (choices 1) [128,256] r3016 c3016
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u224
  · exact u225

def b3017 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 47, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 11 100 56 208 33 448 384 384), lower := (rows 7 11 100 56 208 33 64 128 256), losses := [] }

theorem u3017 : Upper (D 9) (R 9) [6,9,96,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3017 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3018 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 100 56 208 160 321 385 257), lower := (rows 7 11 100 56 208 160 64 128 256), losses := [] }

theorem u3018 : Upper (D 9) (R 9) [6,9,96,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3018 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3019 : Route 9 := (fun mask => (mask,id))

def c3019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3019 : Upper (D 9) (R 9) [6,9,96,48,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,192,256] 13 (by decide) (choices 1) [1,128,256] r3019 c3019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u226
  · exact u227
  · exact u228

def r3020 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3020 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3020 : Upper (D 9) (R 9) [6,9,96,48,384,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,48,384,1] 13 (by decide) (choices 1) [128] r3020 c3020
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u229

def b3021 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 56 400 96 449 385 385), lower := (rows 7 11 100 56 400 96 64 128 256), losses := [] }

theorem u3021 : Upper (D 9) (R 9) [6,9,96,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3021 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3022 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 7 11 100 56 400 160 321 449 321), lower := (rows 7 11 100 56 400 160 64 128 256), losses := [] }

theorem u3022 : Upper (D 9) (R 9) [6,9,96,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3022 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 4, region := 452, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 152 49 96 448 384 384), lower := (rows 7 11 100 152 49 96 64 128 256), losses := [] }

theorem u3023 : Upper (D 9) (R 9) [6,9,96,144,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3023 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 460, targets := 1 },{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 324, targets := 128 }], pairs := [(1,5),(2,0),(2,7),(3,0),(3,5)], upper := (rows 7 11 100 152 49 160 320 448 320), lower := (rows 7 11 100 152 49 160 64 128 256), losses := [] }

theorem u3024 : Upper (D 9) (R 9) [6,9,96,144,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3024 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3025 : Route 9 := (fun mask => (mask,id))

def c3025 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3025 : Upper (D 9) (R 9) [6,9,96,144,33,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,33,256] 13 (by decide) (choices 1) [128,256] r3025 c3025
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u230
  · exact u231

def b3026 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 4, region := 228, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 152 273 96 480 416 416), lower := (rows 7 11 100 152 273 96 64 128 256), losses := [] }

theorem u3026 : Upper (D 9) (R 9) [6,9,96,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3026 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3027_32 : Upper (D 9) (R 9) [6,9,96,144,257,128,32] 13 :=
  permutation_upper _ _ _ [6,9,96,144,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u232

def r3027 : Route 9 := (fun mask => (mask,id))

def c3027 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3027 : Upper (D 9) (R 9) [6,9,96,144,257,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257,128] 13 (by decide) (choices 1) [32,256] r3027 c3027
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3027_32
  · exact u234

theorem m3028_32 : Upper (D 9) (R 9) [6,9,96,144,257,256,32] 13 :=
  permutation_upper _ _ _ [6,9,96,144,257,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u233

theorem m3028_128 : Upper (D 9) (R 9) [6,9,96,144,257,256,128] 13 :=
  permutation_upper _ _ _ [6,9,96,144,257,128,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u234

def r3028 : Route 9 := (fun mask => (mask,id))

def c3028 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3028 : Upper (D 9) (R 9) [6,9,96,144,257,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257,256] 13 (by decide) (choices 1) [32,128] r3028 c3028
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3028_32
  · exact m3028_128

def r3029 : Route 9 := (fun mask => (mask,id))

def c3029 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3029 : Upper (D 9) (R 9) [6,9,96,144,288,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,1] 13 (by decide) (choices 1) [128,256] r3029 c3029
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u235
  · exact u236

def b3030 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 152 304 96 449 385 385), lower := (rows 7 11 100 152 304 96 64 128 256), losses := [] }

theorem u3030 : Upper (D 9) (R 9) [6,9,96,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3030 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3031 : Route 9 := (fun mask => (mask,id))

def c3031 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3031 : Upper (D 9) (R 9) [6,9,96,144,288,128] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288,128] 13 (by decide) (choices 1) [1,256] r3031 c3031
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u237
  · exact u238

def b3032 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 207, targets := 256 },{ cop := 5, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 11 100 152 304 288 193 193 449), lower := (rows 7 11 100 152 304 288 64 128 256), losses := [] }

theorem u3032 : Upper (D 9) (R 9) [6,9,96,144,288,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3032 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 42, targets := 320 }], pairs := [(1,6),(1,8),(3,6),(3,8)], upper := (rows 7 11 100 168 145 48 320 448 320), lower := (rows 7 11 100 168 145 48 64 128 256), losses := [] }

theorem u3033 : Upper (D 9) (R 9) [6,9,96,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3033 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 168 145 96 336 400 272), lower := (rows 7 11 100 168 145 96 64 128 256), losses := [] }

theorem u3034 : Upper (D 9) (R 9) [6,9,96,160,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3034 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3035 : Route 9 := (fun mask => (mask,id))

def c3035 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3035 : Upper (D 9) (R 9) [6,9,96,160,129,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,129,256] 13 (by decide) (choices 1) [16,256] r3035 c3035
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u239
  · exact u240

def b3036 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 47, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 100 168 208 33 336 400 272), lower := (rows 7 11 100 168 208 33 64 128 256), losses := [] }

theorem u3036 : Upper (D 9) (R 9) [6,9,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3036 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 47, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 11 100 168 208 48 321 385 257), lower := (rows 7 11 100 168 208 48 64 128 256), losses := [] }

theorem u3037 : Upper (D 9) (R 9) [6,9,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3037 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3038 : Route 9 := (fun mask => (mask,id))

def c3038 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3038 : Upper (D 9) (R 9) [6,9,96,160,192,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,192,256] 13 (by decide) (choices 1) [1,16,256] r3038 c3038
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u241
  · exact u242
  · exact u243

def r3039 : Route 9 := (fun mask => (mask,id))

def c3039 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | _ => 0)

theorem u3039 : Upper (D 9) (R 9) [6,9,96,160,257,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257,16] 13 (by decide) (choices 1) [128,256] r3039 c3039
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u244
  · exact u245

def b3040 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 168 273 96 464 400 400), lower := (rows 7 11 100 168 273 96 64 128 256), losses := [] }

theorem u3040 : Upper (D 9) (R 9) [6,9,96,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3040 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 11 100 168 273 160 336 464 336), lower := (rows 7 11 100 168 273 160 64 128 256), losses := [] }

theorem u3041 : Upper (D 9) (R 9) [6,9,96,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3041 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3042 : Route 9 := (fun mask => (mask,id))

def c3042 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3042 : Upper (D 9) (R 9) [6,9,96,160,257,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257,256] 13 (by decide) (choices 1) [16,128] r3042 c3042
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u246
  · exact u247

def r3043 : Route 9 := (fun mask => (mask,id))

def c3043 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | _ => 0)

theorem u3043 : Upper (D 9) (R 9) [6,9,96,160,320,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320,1] 13 (by decide) (choices 1) [16,128,256] r3043 c3043
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u248
  · exact u249
  · exact u250

def b3044 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 395, targets := 64 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6)], upper := (rows 7 11 100 168 336 48 449 385 385), lower := (rows 7 11 100 168 336 48 64 128 256), losses := [] }

theorem u3044 : Upper (D 9) (R 9) [6,9,96,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3044 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 },{ cop := 5, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 11 100 168 336 160 337 401 273), lower := (rows 7 11 100 168 336 160 64 128 256), losses := [] }

theorem u3045 : Upper (D 9) (R 9) [6,9,96,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3045 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3046 : Route 9 := (fun mask => (mask,id))

def c3046 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3046 : Upper (D 9) (R 9) [6,9,96,160,320,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320,256] 13 (by decide) (choices 1) [1,16,128] r3046 c3046
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u251
  · exact u252
  · exact u253

def r3047 : Route 9 := (fun mask => (mask,id))

def c3047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | _ => 0)

theorem u3047 : Upper (D 9) (R 9) [6,9,96,160,384,1] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,384,1] 13 (by decide) (choices 1) [16,256] r3047 c3047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u254
  · exact u255

def b3048 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 4, region := 40, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 7 11 100 168 400 48 321 449 321), lower := (rows 7 11 100 168 400 48 64 128 256), losses := [] }

theorem u3048 : Upper (D 9) (R 9) [6,9,96,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3048 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3049 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 168 400 96 337 401 273), lower := (rows 7 11 100 168 400 96 64 128 256), losses := [] }

theorem u3049 : Upper (D 9) (R 9) [6,9,96,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3049 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3050 : Route 9 := (fun mask => (mask,id))

def c3050 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3050 : Upper (D 9) (R 9) [6,9,96,160,384,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,384,256] 13 (by decide) (choices 1) [1,16] r3050 c3050
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u256
  · exact u257

def b3051 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 48, targets := 448 },{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(4,6),(4,7),(4,8)], upper := (rows 7 11 100 392 49 48 448 448 448), lower := (rows 7 11 100 392 49 48 64 128 256), losses := [] }

theorem u3051 : Upper (D 9) (R 9) [6,9,96,384,33,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3051 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 392 49 96 464 400 400), lower := (rows 7 11 100 392 49 96 64 128 256), losses := [] }

theorem u3052 : Upper (D 9) (R 9) [6,9,96,384,33,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3052 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 336, camps := [{ cop := 4, region := 460, targets := 1 },{ cop := 4, region := 458, targets := 32 },{ cop := 4, region := 324, targets := 128 }], pairs := [(1,5),(2,0),(2,7),(3,0),(3,5)], upper := (rows 7 11 100 392 49 160 336 464 336), lower := (rows 7 11 100 392 49 160 64 128 256), losses := [] }

theorem u3053 : Upper (D 9) (R 9) [6,9,96,384,33,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3053 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r3054 : Route 9 := (fun mask => (mask,id))

def c3054 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u3054 : Upper (D 9) (R 9) [6,9,96,384,129,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129,16] 13 (by decide) (choices 1) [32,256] r3054 c3054
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u258
  · exact u259

def b3055 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 392 145 96 368 432 304), lower := (rows 7 11 100 392 145 96 64 128 256), losses := [] }

theorem u3055 : Upper (D 9) (R 9) [6,9,96,384,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3055 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m3056_16 : Upper (D 9) (R 9) [6,9,96,384,129,256,16] 13 :=
  permutation_upper _ _ _ [6,9,96,384,129,16,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u259

theorem m3056_32 : Upper (D 9) (R 9) [6,9,96,384,129,256,32] 13 :=
  permutation_upper _ _ _ [6,9,96,384,129,64,256] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u260

def r3056 : Route 9 := (fun mask => (mask,id))

def c3056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3056 : Upper (D 9) (R 9) [6,9,96,384,129,256] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129,256] 13 (by decide) (choices 1) [16,32] r3056 c3056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3056_16
  · exact m3056_32

def b3057 : PairBound 9 := { available := 336, camps := [{ cop := 5, region := 476, targets := 1 },{ cop := 4, region := 328, targets := 32 },{ cop := 4, region := 324, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(3,5),(4,0)], upper := (rows 7 11 100 392 176 33 336 464 336), lower := (rows 7 11 100 392 176 33 64 128 256), losses := [] }

theorem u3057 : Upper (D 9) (R 9) [6,9,96,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3057 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3058 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 395, targets := 32 },{ cop := 3, region := 48, targets := 1 }], pairs := [(0,5),(1,5),(3,5),(4,0)], upper := (rows 7 11 100 392 176 48 321 449 321), lower := (rows 7 11 100 392 176 48 64 128 256), losses := [] }

theorem u3058 : Upper (D 9) (R 9) [6,9,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3058 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3059 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 411, targets := 64 },{ cop := 5, region := 4, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(3,6),(4,6)], upper := (rows 7 11 100 392 176 96 337 401 273), lower := (rows 7 11 100 392 176 96 64 128 256), losses := [] }

theorem u3059 : Upper (D 9) (R 9) [6,9,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3059 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P09
