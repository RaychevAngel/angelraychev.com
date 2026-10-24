import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0272
import IrregularNine14P07C0273
import IrregularNine14P07C0274

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r32880 : Route 9 := (fun mask => (mask,id))

def c32880 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32880 : Upper (D 7) (R 7) [12,48,66,384,3] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,3] 13 (by decide) (choices 1) [1,64,128] r32880 c32880
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16373
  · exact u16374
  · exact u16375

def b32881 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 392 49 227 195 195 451), lower := (rows 13 50 70 392 49 32 64 128 256), losses := [] }

theorem u32881 : Upper (D 7) (R 7) [12,48,66,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32882 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 70 392 50 225 193 193 449), lower := (rows 13 50 70 392 50 32 64 128 256), losses := [] }

theorem u32882 : Upper (D 7) (R 7) [12,48,66,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32883 : Route 9 := (fun mask => (mask,id))

def c32883 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32883 : Upper (D 7) (R 7) [12,48,66,384,65] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,65] 13 (by decide) (choices 1) [1,2,128] r32883 c32883
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16376
  · exact u16377
  · exact u16378

def b32884 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 16, targets := 161 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,5),(4,7)], upper := (rows 13 50 70 392 82 161 225 161 417), lower := (rows 13 50 70 392 82 32 64 128 256), losses := [] }

theorem u32884 : Upper (D 7) (R 7) [12,48,66,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32885 : PairBound 9 := { available := 131, camps := [{ cop := 4, region := 6, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(2,7)], upper := (rows 13 50 70 392 112 163 195 131 387), lower := (rows 13 50 70 392 112 32 64 128 256), losses := [] }

theorem u32885 : Upper (D 7) (R 7) [12,48,66,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32885 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32886 : Route 9 := (fun mask => (mask,id))

def c32886 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32886 : Upper (D 7) (R 7) [12,48,66,384,129] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,129] 13 (by decide) (choices 1) [1,2,64] r32886 c32886
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16379
  · exact u16380
  · exact u16381

def r32887 : Route 9 := (fun mask => (mask,id))

def c32887 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32887 : Upper (D 7) (R 7) [12,48,66,384,130] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,130] 13 (by decide) (choices 1) [1,64] r32887 c32887
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16382
  · exact u16383

def b32888 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 70 392 176 99 67 195 323), lower := (rows 13 50 70 392 176 32 64 128 256), losses := [] }

theorem u32888 : Upper (D 7) (R 7) [12,48,66,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32889 : Route 9 := (fun mask => (mask,id))

def c32889 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32889 : Upper (D 7) (R 7) [12,48,66,384,192] 13 := by
  apply FastRouting.sound _ _ [12,48,66,384,192] 13 (by decide) (choices 1) [1,2] r32889 c32889
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16384
  · exact u16385

def r32890 : Route 9 := (fun mask => (mask,id))

def c32890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u32890 : Upper (D 7) (R 7) [12,48,96,192,3] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,3] 13 (by decide) (choices 1) [1,2,128,256] r32890 c32890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16386
  · exact u16387
  · exact u16388
  · exact u16389

def b32891 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 434, targets := 64 },{ cop := 4, region := 358, targets := 128 }], pairs := [(1,6),(1,7),(2,7),(4,6)], upper := (rows 13 50 100 200 145 291 323 387 259), lower := (rows 13 50 100 200 145 32 64 128 256), losses := [] }

theorem u32891 : Upper (D 7) (R 7) [12,48,96,192,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32891 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32892 : Route 9 := (fun mask => (mask,id))

def c32892 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u32892 : Upper (D 7) (R 7) [12,48,96,192,130] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,130] 13 (by decide) (choices 1) [1,2,256] r32892 c32892
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16390
  · exact u16391
  · exact u16392

def r32893 : Route 9 := (fun mask => (mask,id))

def c32893 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32893 : Upper (D 7) (R 7) [12,48,96,192,257] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,257] 13 (by decide) (choices 1) [1,2,128] r32893 c32893
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16393
  · exact u16394
  · exact u16395

def r32894 : Route 9 := (fun mask => (mask,id))

def c32894 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32894 : Upper (D 7) (R 7) [12,48,96,192,258] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,258] 13 (by decide) (choices 1) [1,2,128] r32894 c32894
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16396
  · exact u16397
  · exact u16398

def r32895 : Route 9 := (fun mask => (mask,id))

def c32895 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32895 : Upper (D 7) (R 7) [12,48,96,192,384] 13 := by
  apply FastRouting.sound _ _ [12,48,96,192,384] 13 (by decide) (choices 1) [1,2] r32895 c32895
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16399
  · exact u16400

def r32896 : Route 9 := (fun mask => (mask,id))

def c32896 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32896 : Upper (D 7) (R 7) [12,48,96,257,3] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257,3] 13 (by decide) (choices 1) [2,64,128] r32896 c32896
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16401
  · exact u16402
  · exact u16403

def b32897 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(3,6)], upper := (rows 13 50 100 265 81 162 194 130 386), lower := (rows 13 50 100 265 81 32 64 128 256), losses := [] }

theorem u32897 : Upper (D 7) (R 7) [12,48,96,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32898 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 100 265 82 163 195 131 387), lower := (rows 13 50 100 265 82 32 64 128 256), losses := [] }

theorem u32898 : Upper (D 7) (R 7) [12,48,96,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32899 : Route 9 := (fun mask => (mask,id))

def c32899 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32899 : Upper (D 7) (R 7) [12,48,96,257,129] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257,129] 13 (by decide) (choices 1) [2,64,128] r32899 c32899
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16404
  · exact u16405
  · exact u16406

def r32900 : Route 9 := (fun mask => (mask,id))

def c32900 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32900 : Upper (D 7) (R 7) [12,48,96,257,130] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257,130] 13 (by decide) (choices 1) [1,2,64,128] r32900 c32900
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16407
  · exact u16408
  · exact u16409
  · exact u16410

def r32901 : Route 9 := (fun mask => (mask,id))

def c32901 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32901 : Upper (D 7) (R 7) [12,48,96,257,192] 13 := by
  apply FastRouting.sound _ _ [12,48,96,257,192] 13 (by decide) (choices 1) [1,2,128] r32901 c32901
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16411
  · exact u16412
  · exact u16413

def r32902 : Route 9 := (fun mask => (mask,id))

def c32902 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32902 : Upper (D 7) (R 7) [12,48,96,258,3] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,3] 13 (by decide) (choices 1) [1,64,128] r32902 c32902
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16414
  · exact u16415
  · exact u16416

def r32903 : Route 9 := (fun mask => (mask,id))

def c32903 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32903 : Upper (D 7) (R 7) [12,48,96,258,65] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,65] 13 (by decide) (choices 1) [1,2,128] r32903 c32903
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16417
  · exact u16418
  · exact u16419

def b32904 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 100 266 82 161 193 129 385), lower := (rows 13 50 100 266 82 32 64 128 256), losses := [] }

theorem u32904 : Upper (D 7) (R 7) [12,48,96,258,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32904 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32905 : Route 9 := (fun mask => (mask,id))

def c32905 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32905 : Upper (D 7) (R 7) [12,48,96,258,129] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,129] 13 (by decide) (choices 1) [1,2,64,128] r32905 c32905
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16420
  · exact u16421
  · exact u16422
  · exact u16423

def r32906 : Route 9 := (fun mask => (mask,id))

def c32906 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32906 : Upper (D 7) (R 7) [12,48,96,258,130] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,130] 13 (by decide) (choices 1) [1,64,128] r32906 c32906
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16424
  · exact u16425
  · exact u16426

def r32907 : Route 9 := (fun mask => (mask,id))

def c32907 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32907 : Upper (D 7) (R 7) [12,48,96,258,192] 13 := by
  apply FastRouting.sound _ _ [12,48,96,258,192] 13 (by decide) (choices 1) [1,2,128] r32907 c32907
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16427
  · exact u16428
  · exact u16429

def r32908 : Route 9 := (fun mask => (mask,id))

def c32908 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32908 : Upper (D 7) (R 7) [12,48,96,320,3] 13 := by
  apply FastRouting.sound _ _ [12,48,96,320,3] 13 (by decide) (choices 1) [1,2,128] r32908 c32908
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16430
  · exact u16431
  · exact u16432

def r32909 : Route 9 := (fun mask => (mask,id))

def c32909 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32909 : Upper (D 7) (R 7) [12,48,96,320,129] 13 := by
  apply FastRouting.sound _ _ [12,48,96,320,129] 13 (by decide) (choices 1) [1,2,128] r32909 c32909
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16433
  · exact u16434
  · exact u16435

def r32910 : Route 9 := (fun mask => (mask,id))

def c32910 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32910 : Upper (D 7) (R 7) [12,48,96,320,130] 13 := by
  apply FastRouting.sound _ _ [12,48,96,320,130] 13 (by decide) (choices 1) [1,2,128] r32910 c32910
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16436
  · exact u16437
  · exact u16438

def r32911 : Route 9 := (fun mask => (mask,id))

def c32911 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32911 : Upper (D 7) (R 7) [12,48,96,384,3] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,3] 13 (by decide) (choices 1) [1,2,64,128] r32911 c32911
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16439
  · exact u16440
  · exact u16441
  · exact u16442

def r32912 : Route 9 := (fun mask => (mask,id))

def c32912 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32912 : Upper (D 7) (R 7) [12,48,96,384,65] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,65] 13 (by decide) (choices 1) [1,2,128] r32912 c32912
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16443
  · exact u16444
  · exact u16445

def b32913 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 18, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,7)], upper := (rows 13 50 100 392 82 163 195 131 387), lower := (rows 13 50 100 392 82 32 64 128 256), losses := [] }

theorem u32913 : Upper (D 7) (R 7) [12,48,96,384,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32913 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32914 : Route 9 := (fun mask => (mask,id))

def c32914 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32914 : Upper (D 7) (R 7) [12,48,96,384,129] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,129] 13 (by decide) (choices 1) [1,2,64] r32914 c32914
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16446
  · exact u16447
  · exact u16448

def r32915 : Route 9 := (fun mask => (mask,id))

def c32915 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32915 : Upper (D 7) (R 7) [12,48,96,384,130] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,130] 13 (by decide) (choices 1) [1,2,64] r32915 c32915
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16449
  · exact u16450
  · exact u16451

def r32916 : Route 9 := (fun mask => (mask,id))

def c32916 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32916 : Upper (D 7) (R 7) [12,48,96,384,192] 13 := by
  apply FastRouting.sound _ _ [12,48,96,384,192] 13 (by decide) (choices 1) [1,2] r32916 c32916
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16452
  · exact u16453

def r32917 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32917 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32917 : Upper (D 7) (R 7) [12,48,192,257,3] 13 := by
  apply FastRouting.sound _ _ [12,48,192,257,3] 13 (by decide) (choices 1) [2,64] r32917 c32917
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16454
  · exact u16455

def b32918 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 265 49 226 194 194 450), lower := (rows 13 50 196 265 49 32 64 128 256), losses := [] }

theorem u32918 : Upper (D 7) (R 7) [12,48,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32918 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32919 : PairBound 9 := { available := 195, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 196 265 50 227 195 195 451), lower := (rows 13 50 196 265 50 32 64 128 256), losses := [] }

theorem u32919 : Upper (D 7) (R 7) [12,48,192,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32919 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32920 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 166, targets := 1 },{ cop := 4, region := 426, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(3,6)], upper := (rows 13 50 196 265 81 162 226 162 418), lower := (rows 13 50 196 265 81 32 64 128 256), losses := [] }

theorem u32920 : Upper (D 7) (R 7) [12,48,192,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32920 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32921 : Route 9 := (fun mask => (mask,id))

def c32921 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32921 : Upper (D 7) (R 7) [12,48,192,257,66] 13 := by
  apply FastRouting.sound _ _ [12,48,192,257,66] 13 (by decide) (choices 1) [1,2,128] r32921 c32921
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16456
  · exact u16457
  · exact u16458

def b32922 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 265 112 163 195 131 387), lower := (rows 13 50 196 265 112 32 64 128 256), losses := [] }

theorem u32922 : Upper (D 7) (R 7) [12,48,192,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32922 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32923 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 196 265 208 35 99 163 291), lower := (rows 13 50 196 265 208 32 64 128 256), losses := [] }

theorem u32923 : Upper (D 7) (R 7) [12,48,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32923 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32924 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32924 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32924 : Upper (D 7) (R 7) [12,48,192,258,3] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258,3] 13 (by decide) (choices 1) [1,64] r32924 c32924
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16459
  · exact u16460

def b32925 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 266 49 227 195 195 451), lower := (rows 13 50 196 266 49 32 64 128 256), losses := [] }

theorem u32925 : Upper (D 7) (R 7) [12,48,192,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32925 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32926 : PairBound 9 := { available := 193, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 196 266 50 225 193 193 449), lower := (rows 13 50 196 266 50 32 64 128 256), losses := [] }

theorem u32926 : Upper (D 7) (R 7) [12,48,192,258,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32926 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32927 : Route 9 := (fun mask => (mask,id))

def c32927 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32927 : Upper (D 7) (R 7) [12,48,192,258,65] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258,65] 13 (by decide) (choices 1) [1,2,128] r32927 c32927
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16461
  · exact u16462
  · exact u16463

def r32928 : Route 9 := (fun mask => (mask,id))

def c32928 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32928 : Upper (D 7) (R 7) [12,48,192,258,66] 13 := by
  apply FastRouting.sound _ _ [12,48,192,258,66] 13 (by decide) (choices 1) [1,128] r32928 c32928
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16464
  · exact u16465

def b32929 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 4, region := 2, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 13 50 196 266 112 163 195 131 387), lower := (rows 13 50 196 266 112 32 64 128 256), losses := [] }

theorem u32929 : Upper (D 7) (R 7) [12,48,192,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32929 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32930 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 196 266 208 35 99 163 291), lower := (rows 13 50 196 266 208 32 64 128 256), losses := [] }

theorem u32930 : Upper (D 7) (R 7) [12,48,192,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32930 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32931 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c32931 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u32931 : Upper (D 7) (R 7) [12,48,192,288,3] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,3] 13 (by decide) (choices 1) [1,2,64] r32931 c32931
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16466
  · exact u16467
  · exact u16468

def r32932 : Route 9 := (fun mask => (mask,id))

def c32932 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32932 : Upper (D 7) (R 7) [12,48,192,288,65] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,65] 13 (by decide) (choices 1) [1,2,128] r32932 c32932
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16469
  · exact u16470
  · exact u16471

def r32933 : Route 9 := (fun mask => (mask,id))

def c32933 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32933 : Upper (D 7) (R 7) [12,48,192,288,66] 13 := by
  apply FastRouting.sound _ _ [12,48,192,288,66] 13 (by decide) (choices 1) [1,2,128] r32933 c32933
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16472
  · exact u16473
  · exact u16474

def b32934 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 16, targets := 35 },{ cop := 4, region := 4, targets := 1 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 13 50 196 296 208 35 67 131 259), lower := (rows 13 50 196 296 208 32 64 128 256), losses := [] }

theorem u32934 : Upper (D 7) (R 7) [12,48,192,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32934 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32935 : Route 9 := (fun mask => (mask,id))

def c32935 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u32935 : Upper (D 7) (R 7) [12,48,192,320,3] 13 := by
  apply FastRouting.sound _ _ [12,48,192,320,3] 13 (by decide) (choices 1) [1,2,128] r32935 c32935
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16475
  · exact u16476
  · exact u16477

def b32936 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 461, targets := 32 },{ cop := 0, region := 178, targets := 64 }], pairs := [(0,5),(1,6),(2,5),(3,5)], upper := (rows 13 50 196 328 49 163 195 131 387), lower := (rows 13 50 196 328 49 32 64 128 256), losses := [] }

theorem u32936 : Upper (D 7) (R 7) [12,48,192,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32936 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32937 : PairBound 9 := { available := 131, camps := [{ cop := 5, region := 18, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(4,0)], upper := (rows 13 50 196 328 50 163 195 131 387), lower := (rows 13 50 196 328 50 32 64 128 256), losses := [] }

theorem u32937 : Upper (D 7) (R 7) [12,48,192,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32937 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32938 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 178, targets := 64 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 13 50 196 328 145 35 99 163 291), lower := (rows 13 50 196 328 145 32 64 128 256), losses := [] }

theorem u32938 : Upper (D 7) (R 7) [12,48,192,320,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32938 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r32939 : Route 9 := (fun mask => (mask,id))

def c32939 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u32939 : Upper (D 7) (R 7) [12,48,192,320,130] 13 := by
  apply FastRouting.sound _ _ [12,48,192,320,130] 13 (by decide) (choices 1) [1,2] r32939 c32939
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16478
  · exact u16479

#print axioms u32939
end Delivery.IrregularNine14.P07
