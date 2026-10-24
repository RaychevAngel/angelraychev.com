import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0054
import IrregularNine14P09C0055
import IrregularNine14P09C0056

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6840 : Route 9 := (fun mask => (mask,id))

def c6840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6840 : Upper (D 9) (R 9) [6,33,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384] 13 (by decide) (choices 1) [1,8,256] r6840 c6840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3262
  · exact u3263
  · exact u3264

def r6841 : Route 9 := (fun mask => (mask,id))

def c6841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u6841 : Upper (D 9) (R 9) [6,33,192,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,257] 13 (by decide) (choices 1) [8,16,128,256] r6841 c6841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3265
  · exact u3266
  · exact u3267
  · exact u3268

def r6842 : Route 9 := (fun mask => (mask,id))

def c6842 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6842 : Upper (D 9) (R 9) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [1,16,128,256] r6842 c6842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3269
  · exact u3270
  · exact u3271
  · exact u3272

def r6843 : Route 9 := (fun mask => (mask,id))

def c6843 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6843 : Upper (D 9) (R 9) [6,33,192,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384] 13 (by decide) (choices 1) [1,8,16,256] r6843 c6843
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3273
  · exact u3274
  · exact u3275
  · exact u3276

def b6844 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 7 35 196 200 273 312 376 440 312), lower := (rows 7 35 196 200 273 32 64 128 256), losses := [] }

theorem u6844 : Upper (D 9) (R 9) [6,33,192,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6844 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6845 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 7 35 196 200 280 305 369 433 305), lower := (rows 7 35 196 200 280 32 64 128 256), losses := [] }

theorem u6845 : Upper (D 9) (R 9) [6,33,192,192,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6845 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6846 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 8, targets := 289 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,8)], upper := (rows 7 35 196 200 304 313 345 409 281), lower := (rows 7 35 196 200 304 32 64 128 256), losses := [] }

theorem u6846 : Upper (D 9) (R 9) [6,33,192,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6847 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 231, targets := 256 }], pairs := [(0,8),(1,8),(4,5),(4,6),(4,7)], upper := (rows 7 35 196 265 280 240 240 240 496), lower := (rows 7 35 196 265 280 32 64 128 256), losses := [] }

theorem u6847 : Upper (D 9) (R 9) [6,33,192,257,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6847 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6848 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u6848 : Upper (D 9) (R 9) [6,33,192,257,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,288] 13 (by decide) (choices 1) [8,16,64] r6848 c6848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3277
  · exact u3278
  · exact u3279

def r6849 : Route 9 := (fun mask => (mask,id))

def c6849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6849 : Upper (D 9) (R 9) [6,33,192,257,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257,320] 13 (by decide) (choices 1) [8,16,128] r6849 c6849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3280
  · exact u3281
  · exact u3282

def b6850 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 24, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7),(4,0)], upper := (rows 7 35 196 280 280 225 225 225 481), lower := (rows 7 35 196 280 280 32 64 128 256), losses := [] }

theorem u6850 : Upper (D 9) (R 9) [6,33,192,272,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6850 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6851 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 7 35 196 280 304 233 201 201 457), lower := (rows 7 35 196 280 304 32 64 128 256), losses := [] }

theorem u6851 : Upper (D 9) (R 9) [6,33,192,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6851 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6852 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 7 35 196 280 336 169 233 169 425), lower := (rows 7 35 196 280 336 32 64 128 256), losses := [] }

theorem u6852 : Upper (D 9) (R 9) [6,33,192,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6852 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6853 : Route 9 := (fun mask => (mask,id))

def c6853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6853 : Upper (D 9) (R 9) [6,33,192,288,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,288,320] 13 (by decide) (choices 1) [1,8,16,128] r6853 c6853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3283
  · exact u3284
  · exact u3285
  · exact u3286

theorem m6854_16 : Upper (D 9) (R 9) [6,33,192,320,384,16] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3288

def r6854 : Route 9 := (fun mask => (mask,id))

def c6854 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6854 : Upper (D 9) (R 9) [6,33,192,320,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,320,384] 13 (by decide) (choices 1) [1,8,16] r6854 c6854
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3287
  · exact u3288
  · exact m6854_16

def b6855 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 384 },{ cop := 4, region := 8, targets := 128 }], pairs := [(3,5),(3,7),(4,5),(4,7),(4,8)], upper := (rows 7 42 52 73 81 416 448 384 384), lower := (rows 7 42 52 73 81 32 64 128 256), losses := [] }

theorem u6855 : Upper (D 9) (R 9) [6,40,48,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6855 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6856_128 : Upper (D 9) (R 9) [6,40,48,65,129,128] 13 :=
  permutation_upper _ _ _ [6,40,48,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3289

def r6856 : Route 9 := (fun mask => (mask,id))

def c6856 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6856 : Upper (D 9) (R 9) [6,40,48,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,129] 13 (by decide) (choices 1) [64,128,256] r6856 c6856
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3289
  · exact m6856_128
  · exact u3290

def r6857 : Route 9 := (fun mask => (mask,id))

def c6857 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6857 : Upper (D 9) (R 9) [6,40,48,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,192] 13 (by decide) (choices 1) [1,128,256] r6857 c6857
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3291
  · exact u3292
  · exact u3293

def r6858 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6858 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6858 : Upper (D 9) (R 9) [6,40,48,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,48,65,384] 13 (by decide) (choices 1) [1,64,128] r6858 c6858
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3294
  · exact u3295
  · exact u3296

def b6859 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 16, targets := 289 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,8)], upper := (rows 7 42 52 200 208 289 321 385 257), lower := (rows 7 42 52 200 208 32 64 128 256), losses := [] }

theorem u6859 : Upper (D 9) (R 9) [6,40,48,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6859 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6860_256 : Upper (D 9) (R 9) [6,40,48,192,320,256] 13 :=
  permutation_upper _ _ _ [6,40,48,192,320,128] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3298

def r6860 : Route 9 := (fun mask => (mask,id))

def c6860 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6860 : Upper (D 9) (R 9) [6,40,48,192,320] 13 := by
  apply FastRouting.sound _ _ [6,40,48,192,320] 13 (by decide) (choices 1) [1,128,256] r6860 c6860
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3297
  · exact u3298
  · exact m6860_256

def b6861 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 469, targets := 32 },{ cop := 3, region := 2, targets := 192 }], pairs := [(0,5),(1,6),(1,7),(2,5),(4,5)], upper := (rows 7 42 84 41 145 480 448 448 448), lower := (rows 7 42 84 41 145 32 64 128 256), losses := [] }

theorem u6861 : Upper (D 9) (R 9) [6,40,80,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6862 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 41 400 481 449 449 449), lower := (rows 7 42 84 41 400 32 64 128 256), losses := [] }

theorem u6862 : Upper (D 9) (R 9) [6,40,80,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6863 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 460, targets := 32 },{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0),(1,6),(2,5),(3,5),(4,6)], upper := (rows 7 42 84 73 49 416 448 384 384), lower := (rows 7 42 84 73 49 32 64 128 256), losses := [] }

theorem u6863 : Upper (D 9) (R 9) [6,40,80,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6863 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6864 : Route 9 := (fun mask => (mask,id))

def c6864 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6864 : Upper (D 9) (R 9) [6,40,80,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,129] 13 (by decide) (choices 1) [128,256] r6864 c6864
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3299
  · exact u3300

def r6865 : Route 9 := (fun mask => (mask,id))

def c6865 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6865 : Upper (D 9) (R 9) [6,40,80,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,160] 13 (by decide) (choices 1) [1,128,256] r6865 c6865
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3301
  · exact u3302
  · exact u3303

def r6866 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6866 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6866 : Upper (D 9) (R 9) [6,40,80,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,65,384] 13 (by decide) (choices 1) [1,128] r6866 c6866
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3304
  · exact u3305

def b6867 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 104 145 417 449 385 385), lower := (rows 7 42 84 104 145 32 64 128 256), losses := [] }

theorem u6867 : Upper (D 9) (R 9) [6,40,80,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6867 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6868 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 104 400 417 449 385 385), lower := (rows 7 42 84 104 400 32 64 128 256), losses := [] }

theorem u6868 : Upper (D 9) (R 9) [6,40,80,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6868 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6869 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 16, targets := 352 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 7 42 84 137 145 352 352 480 352), lower := (rows 7 42 84 137 145 32 64 128 256), losses := [] }

theorem u6869 : Upper (D 9) (R 9) [6,40,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6869 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6870 : Route 9 := (fun mask => (mask,id))

def c6870 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6870 : Upper (D 9) (R 9) [6,40,80,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160] 13 (by decide) (choices 1) [1,64,256] r6870 c6870
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3306
  · exact u3307
  · exact u3308

def b6871 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 7 42 84 137 208 289 353 417 289), lower := (rows 7 42 84 137 208 32 64 128 256), losses := [] }

theorem u6871 : Upper (D 9) (R 9) [6,40,80,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6871 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6872 : Route 9 := (fun mask => (mask,id))

def c6872 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6872 : Upper (D 9) (R 9) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [64,128,256] r6872 c6872
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3309
  · exact u3310
  · exact u3311

def r6873 : Route 9 := (fun mask => (mask,id))

def c6873 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6873 : Upper (D 9) (R 9) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [1,64,128,256] r6873 c6873
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3312
  · exact u3313
  · exact u3314
  · exact u3315

def b6874 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 4, targets := 417 },{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(2,0),(2,5),(2,7),(2,8)], upper := (rows 7 42 84 137 336 417 481 417 417), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u6874 : Upper (D 9) (R 9) [6,40,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6874 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6875 : Route 9 := (fun mask => (mask,id))

def c6875 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6875 : Upper (D 9) (R 9) [6,40,80,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,384] 13 (by decide) (choices 1) [1,64,256] r6875 c6875
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3316
  · exact u3317
  · exact u3318

def b6876 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 2, targets := 449 },{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(1,0),(1,6),(1,7),(1,8)], upper := (rows 7 42 84 168 400 353 321 449 321), lower := (rows 7 42 84 168 400 32 64 128 256), losses := [] }

theorem u6876 : Upper (D 9) (R 9) [6,40,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6877 : Route 9 := (fun mask => (mask,id))

def c6877 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6877 : Upper (D 9) (R 9) [6,40,80,192,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,160] 13 (by decide) (choices 1) [1,256] r6877 c6877
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3319
  · exact u3320

def r6878 : Route 9 := (fun mask => (mask,id))

def c6878 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6878 : Upper (D 9) (R 9) [6,40,80,192,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,288] 13 (by decide) (choices 1) [1,128,256] r6878 c6878
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3321
  · exact u3322
  · exact u3323

def r6879 : Route 9 := (fun mask => (mask,id))

def c6879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6879 : Upper (D 9) (R 9) [6,40,80,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384] 13 (by decide) (choices 1) [1,256] r6879 c6879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3324
  · exact u3325

def b6880 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 7 42 84 392 400 97 97 225 353), lower := (rows 7 42 84 392 400 32 64 128 256), losses := [] }

theorem u6880 : Upper (D 9) (R 9) [6,40,80,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6881 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 42 100 25 81 416 448 384 384), lower := (rows 7 42 100 25 81 32 64 128 256), losses := [] }

theorem u6881 : Upper (D 9) (R 9) [6,40,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6881 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6882 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 8, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 7 42 100 25 145 480 448 448 448), lower := (rows 7 42 100 25 145 32 64 128 256), losses := [] }

theorem u6882 : Upper (D 9) (R 9) [6,40,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6882 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6883 : Route 9 := (fun mask => (mask,id))

def c6883 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6883 : Upper (D 9) (R 9) [6,40,96,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,192] 13 (by decide) (choices 1) [1,128,256] r6883 c6883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3326
  · exact u3327
  · exact u3328

def r6884 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6884 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6884 : Upper (D 9) (R 9) [6,40,96,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,384] 13 (by decide) (choices 1) [1,64,128] r6884 c6884
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3329
  · exact u3330
  · exact u3331

def r6885 : Route 9 := (fun mask => (mask,id))

def c6885 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6885 : Upper (D 9) (R 9) [6,40,96,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,129] 13 (by decide) (choices 1) [1,128,256] r6885 c6885
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3332
  · exact u3333
  · exact u3334

def r6886 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6886 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6886 : Upper (D 9) (R 9) [6,40,96,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,80,384] 13 (by decide) (choices 1) [1,128] r6886 c6886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3335
  · exact u3336

def b6887 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 426, targets := 64 },{ cop := 4, region := 420, targets := 1 }], pairs := [(1,6),(2,0),(3,5),(3,6),(4,5)], upper := (rows 7 42 100 137 81 432 464 400 400), lower := (rows 7 42 100 137 81 32 64 128 256), losses := [] }

theorem u6887 : Upper (D 9) (R 9) [6,40,96,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6887 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6888 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 16, targets := 320 },{ cop := 4, region := 8, targets := 64 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 7 42 100 137 145 368 336 464 336), lower := (rows 7 42 100 137 145 32 64 128 256), losses := [] }

theorem u6888 : Upper (D 9) (R 9) [6,40,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6888 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6889 : Route 9 := (fun mask => (mask,id))

def c6889 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6889 : Upper (D 9) (R 9) [6,40,96,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192] 13 (by decide) (choices 1) [1,16,256] r6889 c6889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3337
  · exact u3338
  · exact u3339

def r6890 : Route 9 := (fun mask => (mask,id))

def c6890 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6890 : Upper (D 9) (R 9) [6,40,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,257] 13 (by decide) (choices 1) [16,64,128,256] r6890 c6890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3340
  · exact u3341
  · exact u3342
  · exact u3343

def r6891 : Route 9 := (fun mask => (mask,id))

def c6891 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6891 : Upper (D 9) (R 9) [6,40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320] 13 (by decide) (choices 1) [1,16,128,256] r6891 c6891
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3344
  · exact u3345
  · exact u3346
  · exact u3347

def r6892 : Route 9 := (fun mask => (mask,id))

def c6892 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6892 : Upper (D 9) (R 9) [6,40,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384] 13 (by decide) (choices 1) [1,16,64,256] r6892 c6892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3348
  · exact u3349
  · exact u3350
  · exact u3351

def r6893 : Route 9 := (fun mask => (mask,id))

def c6893 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6893 : Upper (D 9) (R 9) [6,40,96,144,65] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,65] 13 (by decide) (choices 1) [1,128,256] r6893 c6893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3352
  · exact u3353
  · exact u3354

def b6894 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 65 }], pairs := [(0,7),(1,7),(2,7),(3,0),(3,6)], upper := (rows 7 42 100 152 145 353 321 449 321), lower := (rows 7 42 100 152 145 32 64 128 256), losses := [] }

theorem u6894 : Upper (D 9) (R 9) [6,40,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6894 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6895 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 42 100 152 208 289 321 385 257), lower := (rows 7 42 100 152 208 32 64 128 256), losses := [] }

theorem u6895 : Upper (D 9) (R 9) [6,40,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6895 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6896 : Route 9 := (fun mask => (mask,id))

def c6896 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6896 : Upper (D 9) (R 9) [6,40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,257] 13 (by decide) (choices 1) [1,64,128,256] r6896 c6896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3355
  · exact u3356
  · exact u3357
  · exact u3358

def r6897 : Route 9 := (fun mask => (mask,id))

def c6897 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6897 : Upper (D 9) (R 9) [6,40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320] 13 (by decide) (choices 1) [1,128,256] r6897 c6897
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3359
  · exact u3360
  · exact u3361

def b6898 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 42 100 152 400 353 321 449 321), lower := (rows 7 42 100 152 400 32 64 128 256), losses := [] }

theorem u6898 : Upper (D 9) (R 9) [6,40,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6898 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6899 : Route 9 := (fun mask => (mask,id))

def c6899 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6899 : Upper (D 9) (R 9) [6,40,96,192,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,129] 13 (by decide) (choices 1) [1,16,256] r6899 c6899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3362
  · exact u3363
  · exact u3364

#print axioms u6899
end Delivery.IrregularNine14.P09
