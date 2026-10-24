import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0056
import IrregularNine14P09C0057
import IrregularNine14P09C0058

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6900 : Route 9 := (fun mask => (mask,id))

def c6900 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6900 : Upper (D 9) (R 9) [6,40,96,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,257] 13 (by decide) (choices 1) [1,16,128,256] r6900 c6900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3365
  · exact u3366
  · exact u3367
  · exact u3368

def r6901 : Route 9 := (fun mask => (mask,id))

def c6901 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6901 : Upper (D 9) (R 9) [6,40,96,192,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,192,384] 13 (by decide) (choices 1) [1,16,256] r6901 c6901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3369
  · exact u3370
  · exact u3371

def r6902 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6902 : Upper (D 9) (R 9) [6,40,96,384,65] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,65] 13 (by decide) (choices 1) [1,16,128] r6902 c6902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3372
  · exact u3373
  · exact u3374

def r6903 : Route 9 := (fun mask => (mask,id))

def c6903 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6903 : Upper (D 9) (R 9) [6,40,96,384,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,129] 13 (by decide) (choices 1) [1,16,64,256] r6903 c6903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3375
  · exact u3376
  · exact u3377
  · exact u3378

def r6904 : Route 9 := (fun mask => (mask,id))

def c6904 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6904 : Upper (D 9) (R 9) [6,40,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192] 13 (by decide) (choices 1) [1,16,256] r6904 c6904
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3379
  · exact u3380
  · exact u3381

def b6905 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 7 42 100 392 400 113 81 209 337), lower := (rows 7 42 100 392 400 32 64 128 256), losses := [] }

theorem u6905 : Upper (D 9) (R 9) [6,40,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6905 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6906 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 10, targets := 448 }], pairs := [(1,6),(1,7),(1,8),(3,6),(3,7)], upper := (rows 7 42 196 25 49 480 448 448 448), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u6906 : Upper (D 9) (R 9) [6,40,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6906 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6907 : PairBound 9 := { available := 416, camps := [{ cop := 4, region := 8, targets := 416 },{ cop := 3, region := 486, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 7 42 196 25 81 416 480 416 416), lower := (rows 7 42 196 25 81 32 64 128 256), losses := [] }

theorem u6907 : Upper (D 9) (R 9) [6,40,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6907 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6908 : Route 9 := (fun mask => (mask,id))

def c6908 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6908 : Upper (D 9) (R 9) [6,40,192,17,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,96] 13 (by decide) (choices 1) [1,128,256] r6908 c6908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3382
  · exact u3383
  · exact u3384

def b6909 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 7 42 196 25 208 289 353 417 289), lower := (rows 7 42 196 25 208 32 64 128 256), losses := [] }

theorem u6909 : Upper (D 9) (R 9) [6,40,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6909 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6910 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 480 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(3,7),(3,8)], upper := (rows 7 42 196 25 273 480 480 480 480), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u6910 : Upper (D 9) (R 9) [6,40,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6910 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6911 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6911 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6911 : Upper (D 9) (R 9) [6,40,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288] 13 (by decide) (choices 1) [1,64,256] r6911 c6911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3385
  · exact u3386
  · exact u3387

def r6912 : Route 9 := (fun mask => (mask,id))

def c6912 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6912 : Upper (D 9) (R 9) [6,40,192,17,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320] 13 (by decide) (choices 1) [1,128,256] r6912 c6912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3388
  · exact u3389
  · exact u3390

def b6913 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 460, targets := 32 },{ cop := 4, region := 452, targets := 1 }], pairs := [(1,6),(2,0),(2,5),(3,5),(4,6)], upper := (rows 7 42 196 73 49 432 464 400 400), lower := (rows 7 42 196 73 49 32 64 128 256), losses := [] }

theorem u6913 : Upper (D 9) (R 9) [6,40,192,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6913 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6914 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 362, targets := 128 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,6),(1,7),(2,0),(3,7),(4,6)], upper := (rows 7 42 196 73 145 304 368 432 304), lower := (rows 7 42 196 73 145 32 64 128 256), losses := [] }

theorem u6914 : Upper (D 9) (R 9) [6,40,192,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6915 : Route 9 := (fun mask => (mask,id))

def c6915 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6915 : Upper (D 9) (R 9) [6,40,192,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,160] 13 (by decide) (choices 1) [1,16,256] r6915 c6915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3391
  · exact u3392
  · exact u3393

def r6916 : Route 9 := (fun mask => (mask,id))

def c6916 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6916 : Upper (D 9) (R 9) [6,40,192,65,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,257] 13 (by decide) (choices 1) [16,128,256] r6916 c6916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3394
  · exact u3395
  · exact u3396

def r6917 : Route 9 := (fun mask => (mask,id))

def c6917 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6917 : Upper (D 9) (R 9) [6,40,192,65,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,288] 13 (by decide) (choices 1) [1,16,128,256] r6917 c6917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3397
  · exact u3398
  · exact u3399
  · exact u3400

def r6918 : Route 9 := (fun mask => (mask,id))

def c6918 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6918 : Upper (D 9) (R 9) [6,40,192,65,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,65,384] 13 (by decide) (choices 1) [1,16,256] r6918 c6918
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3401
  · exact u3402
  · exact u3403

def b6919 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 456, targets := 32 }], pairs := [(0,5),(1,6),(2,5),(3,5),(4,6)], upper := (rows 7 42 196 88 49 417 449 385 385), lower := (rows 7 42 196 88 49 32 64 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 17 49 0 145 273), good := (rows 439 42 132 442 433 32 0 128 256) }] }

theorem u6919 : Upper (D 9) (R 9) [6,40,192,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6919 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6920 : Route 9 := (fun mask => (mask,id))

def c6920 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6920 : Upper (D 9) (R 9) [6,40,192,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,129] 13 (by decide) (choices 1) [1,256] r6920 c6920
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3404
  · exact u3405

def r6921 : Route 9 := (fun mask => (mask,id))

def c6921 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6921 : Upper (D 9) (R 9) [6,40,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,160] 13 (by decide) (choices 1) [1,256] r6921 c6921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3406
  · exact u3407

def r6922 : Route 9 := (fun mask => (mask,id))

def c6922 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6922 : Upper (D 9) (R 9) [6,40,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,257] 13 (by decide) (choices 1) [1,128,256] r6922 c6922
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3408
  · exact u3409
  · exact u3410

def r6923 : Route 9 := (fun mask => (mask,id))

def c6923 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6923 : Upper (D 9) (R 9) [6,40,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288] 13 (by decide) (choices 1) [1,128,256] r6923 c6923
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3411
  · exact u3412
  · exact u3413

def r6924 : Route 9 := (fun mask => (mask,id))

def c6924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6924 : Upper (D 9) (R 9) [6,40,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,384] 13 (by decide) (choices 1) [1,256] r6924 c6924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3414
  · exact u3415

def r6925 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6925 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6925 : Upper (D 9) (R 9) [6,40,192,257,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,33] 13 (by decide) (choices 1) [16,64,256] r6925 c6925
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3416
  · exact u3417
  · exact u3418

def r6926 : Route 9 := (fun mask => (mask,id))

def c6926 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6926 : Upper (D 9) (R 9) [6,40,192,257,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,65] 13 (by decide) (choices 1) [16,128,256] r6926 c6926
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3419
  · exact u3420
  · exact u3421

def r6927 : Route 9 := (fun mask => (mask,id))

def c6927 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6927 : Upper (D 9) (R 9) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [1,16,128,256] r6927 c6927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3422
  · exact u3423
  · exact u3424
  · exact u3425

def b6928 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 7 42 196 265 208 305 369 433 305), lower := (rows 7 42 196 265 208 32 64 128 256), losses := [] }

theorem u6928 : Upper (D 9) (R 9) [6,40,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6928 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6929 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 265 273 240 240 240 496), lower := (rows 7 42 196 265 273 32 64 128 256), losses := [] }

theorem u6929 : Upper (D 9) (R 9) [6,40,192,257,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6929 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6930 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6930 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6930 : Upper (D 9) (R 9) [6,40,192,257,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,288] 13 (by decide) (choices 1) [1,16,64] r6930 c6930
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3426
  · exact u3427
  · exact u3428

def r6931 : Route 9 := (fun mask => (mask,id))

def c6931 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6931 : Upper (D 9) (R 9) [6,40,192,257,320] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,320] 13 (by decide) (choices 1) [1,16,128] r6931 c6931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3429
  · exact u3430
  · exact u3431

def r6932 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6932 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6932 : Upper (D 9) (R 9) [6,40,192,272,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,33] 13 (by decide) (choices 1) [1,64,256] r6932 c6932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3432
  · exact u3433
  · exact u3434

def r6933 : Route 9 := (fun mask => (mask,id))

def c6933 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6933 : Upper (D 9) (R 9) [6,40,192,272,65] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,65] 13 (by decide) (choices 1) [1,128,256] r6933 c6933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3435
  · exact u3436
  · exact u3437

def r6934 : Route 9 := (fun mask => (mask,id))

def c6934 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6934 : Upper (D 9) (R 9) [6,40,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96] 13 (by decide) (choices 1) [1,128,256] r6934 c6934
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3438
  · exact u3439
  · exact u3440

def b6935 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 289 },{ cop := 4, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5),(4,8)], upper := (rows 7 42 196 280 208 289 353 417 289), lower := (rows 7 42 196 280 208 32 64 128 256), losses := [] }

theorem u6935 : Upper (D 9) (R 9) [6,40,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6935 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6936 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 7 42 196 280 273 225 225 225 481), lower := (rows 7 42 196 280 273 32 64 128 256), losses := [] }

theorem u6936 : Upper (D 9) (R 9) [6,40,192,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6936 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6937 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0),(3,6)], upper := (rows 7 42 196 280 304 225 193 193 449), lower := (rows 7 42 196 280 304 32 64 128 256), losses := [] }

theorem u6937 : Upper (D 9) (R 9) [6,40,192,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6937 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6938 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 7 42 196 280 336 161 225 161 417), lower := (rows 7 42 196 280 336 32 64 128 256), losses := [] }

theorem u6938 : Upper (D 9) (R 9) [6,40,192,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6938 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6939 : Route 9 := (fun mask => (mask,id))

def c6939 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6939 : Upper (D 9) (R 9) [6,40,192,320,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,33] 13 (by decide) (choices 1) [1,16,128,256] r6939 c6939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3441
  · exact u3442
  · exact u3443
  · exact u3444

def r6940 : Route 9 := (fun mask => (mask,id))

def c6940 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6940 : Upper (D 9) (R 9) [6,40,192,320,129] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,129] 13 (by decide) (choices 1) [1,16,256] r6940 c6940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3445
  · exact u3446
  · exact u3447

def r6941 : Route 9 := (fun mask => (mask,id))

def c6941 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6941 : Upper (D 9) (R 9) [6,40,192,320,160] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,160] 13 (by decide) (choices 1) [1,16,256] r6941 c6941
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3448
  · exact u3449
  · exact u3450

def r6942 : Route 9 := (fun mask => (mask,id))

def c6942 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6942 : Upper (D 9) (R 9) [6,40,192,320,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,257] 13 (by decide) (choices 1) [1,16,128] r6942 c6942
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3451
  · exact u3452
  · exact u3453

def r6943 : Route 9 := (fun mask => (mask,id))

def c6943 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6943 : Upper (D 9) (R 9) [6,40,192,320,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,288] 13 (by decide) (choices 1) [1,16,128] r6943 c6943
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3454
  · exact u3455
  · exact u3456

def r6944 : Route 9 := (fun mask => (mask,id))

def c6944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6944 : Upper (D 9) (R 9) [6,40,192,320,384] 13 := by
  apply FastRouting.sound _ _ [6,40,192,320,384] 13 (by decide) (choices 1) [1,16] r6944 c6944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3457
  · exact u3458

def b6945 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 448 }], pairs := [(3,6),(3,7),(3,8),(4,6),(4,7)], upper := (rows 7 98 164 25 25 480 448 448 448), lower := (rows 7 98 164 25 25 32 64 128 256), losses := [] }

theorem u6945 : Upper (D 9) (R 9) [6,96,160,17,9] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6945 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6946 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 486, targets := 1 },{ cop := 4, region := 428, targets := 64 }], pairs := [(1,0),(2,0),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 25 81 424 456 392 392), lower := (rows 7 98 164 25 81 32 64 128 256), losses := [] }

theorem u6946 : Upper (D 9) (R 9) [6,96,160,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6946 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6947 : Route 9 := (fun mask => (mask,id))

def c6947 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6947 : Upper (D 9) (R 9) [6,96,160,17,72] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,72] 13 (by decide) (choices 1) [1,128,256] r6947 c6947
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3459
  · exact u3460
  · exact u3461

def r6948 : Route 9 := (fun mask => (mask,id))

def c6948 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6948 : Upper (D 9) (R 9) [6,96,160,17,192] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,192] 13 (by decide) (choices 1) [1,8,256] r6948 c6948
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3462
  · exact u3463
  · exact u3464

def b6949 : PairBound 9 := { available := 456, camps := [{ cop := 4, region := 8, targets := 448 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(3,6),(3,7),(3,8),(4,5)], upper := (rows 7 98 164 25 273 488 456 456 456), lower := (rows 7 98 164 25 273 32 64 128 256), losses := [] }

theorem u6949 : Upper (D 9) (R 9) [6,96,160,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6949 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6950_128 : Upper (D 9) (R 9) [6,96,160,17,264,128] 13 :=
  permutation_upper _ _ _ [6,96,160,17,264,64] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3466

def r6950 : Route 9 := (fun mask => (mask,id))

def c6950 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6950 : Upper (D 9) (R 9) [6,96,160,17,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,264] 13 (by decide) (choices 1) [1,64,128,256] r6950 c6950
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3465
  · exact u3466
  · exact m6950_128
  · exact u3467

def r6951 : Route 9 := (fun mask => (mask,id))

def c6951 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6951 : Upper (D 9) (R 9) [6,96,160,17,320] 13 := by
  apply FastRouting.sound _ _ [6,96,160,17,320] 13 (by decide) (choices 1) [1,8,128,256] r6951 c6951
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3468
  · exact u3469
  · exact u3470
  · exact u3471

def b6952 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(2,6),(3,5),(4,5),(4,6)], upper := (rows 7 98 164 73 145 312 344 408 280), lower := (rows 7 98 164 73 145 32 64 128 256), losses := [] }

theorem u6952 : Upper (D 9) (R 9) [6,96,160,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6952 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6953 : Route 9 := (fun mask => (mask,id))

def c6953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6953 : Upper (D 9) (R 9) [6,96,160,65,136] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,136] 13 (by decide) (choices 1) [1,16,256] r6953 c6953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3472
  · exact u3473
  · exact u3474

def r6954 : Route 9 := (fun mask => (mask,id))

def c6954 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u6954 : Upper (D 9) (R 9) [6,96,160,65,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,257] 13 (by decide) (choices 1) [8,16,128,256] r6954 c6954
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3475
  · exact u3476
  · exact u3477
  · exact u3478

def r6955 : Route 9 := (fun mask => (mask,id))

def c6955 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6955 : Upper (D 9) (R 9) [6,96,160,65,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,264] 13 (by decide) (choices 1) [1,16,128,256] r6955 c6955
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3479
  · exact u3480
  · exact u3481
  · exact u3482

def r6956 : Route 9 := (fun mask => (mask,id))

def c6956 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6956 : Upper (D 9) (R 9) [6,96,160,65,384] 13 := by
  apply FastRouting.sound _ _ [6,96,160,65,384] 13 (by decide) (choices 1) [1,8,16,256] r6956 c6956
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3483
  · exact u3484
  · exact u3485
  · exact u3486

def b6957 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 389, targets := 64 },{ cop := 2, region := 323, targets := 128 }], pairs := [(0,6),(0,7),(2,6),(3,5),(4,5)], upper := (rows 7 98 164 88 152 289 321 385 257), lower := (rows 7 98 164 88 152 32 64 128 256), losses := [] }

theorem u6957 : Upper (D 9) (R 9) [6,96,160,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6957 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6958 : Route 9 := (fun mask => (mask,id))

def c6958 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6958 : Upper (D 9) (R 9) [6,96,160,80,257] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,257] 13 (by decide) (choices 1) [1,8,128,256] r6958 c6958
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3487
  · exact u3488
  · exact u3489
  · exact u3490

def r6959 : Route 9 := (fun mask => (mask,id))

def c6959 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6959 : Upper (D 9) (R 9) [6,96,160,80,264] 13 := by
  apply FastRouting.sound _ _ [6,96,160,80,264] 13 (by decide) (choices 1) [1,128,256] r6959 c6959
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3491
  · exact u3492
  · exact u3493

#print axioms u6959
end Delivery.IrregularNine14.P09
