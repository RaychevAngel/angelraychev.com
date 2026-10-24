import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0100
import IrregularNine14P09C0101
import IrregularNine14P09C0102

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8400 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 14 38 152 208 289 321 385 257), lower := (rows 97 14 38 152 208 32 64 128 256), losses := [] }

theorem u8400 : Upper (D 9) (R 9) [96,12,34,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8400 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8401 : Route 9 := (fun mask => (mask,id))

def c8401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8401 : Upper (D 9) (R 9) [96,12,34,144,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144,257] 13 (by decide) (choices 1) [1,64,128,256] r8401 c8401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6028
  · exact u6029
  · exact u6030
  · exact u6031

def r8402 : Route 9 := (fun mask => (mask,id))

def c8402 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8402 : Upper (D 9) (R 9) [96,12,34,144,320] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144,320] 13 (by decide) (choices 1) [1,128,256] r8402 c8402
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6032
  · exact u6033
  · exact u6034

def b8403 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 97 14 38 152 400 353 321 449 321), lower := (rows 97 14 38 152 400 32 64 128 256), losses := [] }

theorem u8403 : Upper (D 9) (R 9) [96,12,34,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8403 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8404 : Route 9 := (fun mask => (mask,id))

def c8404 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8404 : Upper (D 9) (R 9) [96,12,34,192,129] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,129] 13 (by decide) (choices 1) [1,16,256] r8404 c8404
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6035
  · exact u6036
  · exact u6037

def r8405 : Route 9 := (fun mask => (mask,id))

def c8405 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8405 : Upper (D 9) (R 9) [96,12,34,192,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,257] 13 (by decide) (choices 1) [1,16,128,256] r8405 c8405
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6038
  · exact u6039
  · exact u6040
  · exact u6041

def r8406 : Route 9 := (fun mask => (mask,id))

def c8406 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8406 : Upper (D 9) (R 9) [96,12,34,192,384] 13 := by
  apply FastRouting.sound _ _ [96,12,34,192,384] 13 (by decide) (choices 1) [1,16,256] r8406 c8406
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6042
  · exact u6043
  · exact u6044

def b8407 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 408, targets := 32 }], pairs := [(1,6),(2,6),(3,5),(3,6),(4,5)], upper := (rows 97 14 38 392 81 433 465 401 401), lower := (rows 97 14 38 392 81 32 64 128 256), losses := [] }

theorem u8407 : Upper (D 9) (R 9) [96,12,34,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8407 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8408 : Route 9 := (fun mask => (mask,id))

def c8408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8408 : Upper (D 9) (R 9) [96,12,34,384,129] 13 := by
  apply FastRouting.sound _ _ [96,12,34,384,129] 13 (by decide) (choices 1) [1,16,64,256] r8408 c8408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6045
  · exact u6046
  · exact u6047
  · exact u6048

def r8409 : Route 9 := (fun mask => (mask,id))

def c8409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8409 : Upper (D 9) (R 9) [96,12,34,384,192] 13 := by
  apply FastRouting.sound _ _ [96,12,34,384,192] 13 (by decide) (choices 1) [1,16,256] r8409 c8409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6049
  · exact u6050
  · exact u6051

def b8410 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 97 14 38 392 400 113 81 209 337), lower := (rows 97 14 38 392 400 32 64 128 256), losses := [] }

theorem u8410 : Upper (D 9) (R 9) [96,12,34,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8410 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8411 : PairBound 9 := { available := 386, camps := [{ cop := 0, region := 20, targets := 384 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,7),(2,8),(4,7),(4,8)], upper := (rows 97 14 52 137 81 418 450 386 386), lower := (rows 97 14 52 137 81 32 64 128 256), losses := [] }

theorem u8411 : Upper (D 9) (R 9) [96,12,48,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8411 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8412 : Route 9 := (fun mask => (mask,id))

def c8412 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8412 : Upper (D 9) (R 9) [96,12,48,129,66] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,66] 13 (by decide) (choices 1) [1,128,256] r8412 c8412
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6052
  · exact u6053
  · exact u6054

def b8413 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 16, targets := 352 },{ cop := 4, region := 8, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6),(4,8)], upper := (rows 97 14 52 137 145 354 322 450 322), lower := (rows 97 14 52 137 145 32 64 128 256), losses := [] }

theorem u8413 : Upper (D 9) (R 9) [96,12,48,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8413 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8414 : Route 9 := (fun mask => (mask,id))

def c8414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8414 : Upper (D 9) (R 9) [96,12,48,129,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,130] 13 (by decide) (choices 1) [1,64,256] r8414 c8414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6055
  · exact u6056
  · exact u6057

def r8415 : Route 9 := (fun mask => (mask,id))

def c8415 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8415 : Upper (D 9) (R 9) [96,12,48,129,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,192] 13 (by decide) (choices 1) [1,2,256] r8415 c8415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6058
  · exact u6059
  · exact u6060

def r8416 : Route 9 := (fun mask => (mask,id))

def c8416 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8416 : Upper (D 9) (R 9) [96,12,48,129,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,257] 13 (by decide) (choices 1) [2,64,128,256] r8416 c8416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6061
  · exact u6062
  · exact u6063
  · exact u6064

def r8417 : Route 9 := (fun mask => (mask,id))

def c8417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8417 : Upper (D 9) (R 9) [96,12,48,129,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,258] 13 (by decide) (choices 1) [1,64,128,256] r8417 c8417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6065
  · exact u6066
  · exact u6067
  · exact u6068

def r8418 : Route 9 := (fun mask => (mask,id))

def c8418 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8418 : Upper (D 9) (R 9) [96,12,48,129,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,320] 13 (by decide) (choices 1) [1,2,128,256] r8418 c8418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6069
  · exact u6070
  · exact u6071
  · exact u6072

def r8419 : Route 9 := (fun mask => (mask,id))

def c8419 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8419 : Upper (D 9) (R 9) [96,12,48,129,384] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129,384] 13 (by decide) (choices 1) [1,2,64,256] r8419 c8419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6073
  · exact u6074
  · exact u6075
  · exact u6076

def b8420 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 20, targets := 384 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,7),(2,8),(4,7),(4,8)], upper := (rows 97 14 52 138 81 417 449 385 385), lower := (rows 97 14 52 138 81 32 64 128 256), losses := [] }

theorem u8420 : Upper (D 9) (R 9) [96,12,48,130,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8420 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8421 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 357, targets := 128 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(1,5),(2,7),(3,5),(4,5)], upper := (rows 97 14 52 138 145 353 321 449 321), lower := (rows 97 14 52 138 145 32 64 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 17 0 81 145 273), good := (rows 465 14 478 138 465 0 64 128 256) }] }

theorem u8421 : Upper (D 9) (R 9) [96,12,48,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8421 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8422 : Route 9 := (fun mask => (mask,id))

def c8422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8422 : Upper (D 9) (R 9) [96,12,48,130,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,192] 13 (by decide) (choices 1) [1,256] r8422 c8422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6077
  · exact u6078

def r8423 : Route 9 := (fun mask => (mask,id))

def c8423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8423 : Upper (D 9) (R 9) [96,12,48,130,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,257] 13 (by decide) (choices 1) [1,64,128,256] r8423 c8423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6079
  · exact u6080
  · exact u6081
  · exact u6082

def r8424 : Route 9 := (fun mask => (mask,id))

def c8424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8424 : Upper (D 9) (R 9) [96,12,48,130,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,320] 13 (by decide) (choices 1) [1,128,256] r8424 c8424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6083
  · exact u6084
  · exact u6085

def r8425 : Route 9 := (fun mask => (mask,id))

def c8425 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8425 : Upper (D 9) (R 9) [96,12,48,130,384] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130,384] 13 (by decide) (choices 1) [1,64,256] r8425 c8425
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6086
  · exact u6087
  · exact u6088

def r8426 : Route 9 := (fun mask => (mask,id))

def c8426 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8426 : Upper (D 9) (R 9) [96,12,48,192,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,129] 13 (by decide) (choices 1) [1,2,256] r8426 c8426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6089
  · exact u6090
  · exact u6091

def r8427 : Route 9 := (fun mask => (mask,id))

def c8427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8427 : Upper (D 9) (R 9) [96,12,48,192,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,130] 13 (by decide) (choices 1) [1,256] r8427 c8427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6092
  · exact u6093

def r8428 : Route 9 := (fun mask => (mask,id))

def c8428 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8428 : Upper (D 9) (R 9) [96,12,48,192,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,257] 13 (by decide) (choices 1) [1,2,128,256] r8428 c8428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6094
  · exact u6095
  · exact u6096
  · exact u6097

def r8429 : Route 9 := (fun mask => (mask,id))

def c8429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8429 : Upper (D 9) (R 9) [96,12,48,192,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,258] 13 (by decide) (choices 1) [1,128,256] r8429 c8429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6098
  · exact u6099
  · exact u6100

def r8430 : Route 9 := (fun mask => (mask,id))

def c8430 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8430 : Upper (D 9) (R 9) [96,12,48,192,384] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192,384] 13 (by decide) (choices 1) [1,2,256] r8430 c8430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6101
  · exact u6102
  · exact u6103

def b8431 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 20, targets := 384 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,7),(2,8),(4,7),(4,8)], upper := (rows 97 14 52 392 81 419 451 387 387), lower := (rows 97 14 52 392 81 32 64 128 256), losses := [] }

theorem u8431 : Upper (D 9) (R 9) [96,12,48,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8431 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8432 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c8432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u8432 : Upper (D 9) (R 9) [96,12,48,384,66] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,66] 13 (by decide) (choices 1) [1,128] r8432 c8432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u6104
  · exact u6105

def r8433 : Route 9 := (fun mask => (mask,id))

def c8433 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8433 : Upper (D 9) (R 9) [96,12,48,384,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,129] 13 (by decide) (choices 1) [1,2,64,256] r8433 c8433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6106
  · exact u6107
  · exact u6108
  · exact u6109

def r8434 : Route 9 := (fun mask => (mask,id))

def c8434 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8434 : Upper (D 9) (R 9) [96,12,48,384,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,130] 13 (by decide) (choices 1) [1,64,256] r8434 c8434
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6110
  · exact u6111
  · exact u6112

def r8435 : Route 9 := (fun mask => (mask,id))

def c8435 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8435 : Upper (D 9) (R 9) [96,12,48,384,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384,192] 13 (by decide) (choices 1) [1,2,256] r8435 c8435
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6113
  · exact u6114
  · exact u6115

def b8436 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 97 14 52 392 400 99 67 195 323), lower := (rows 97 14 52 392 400 32 64 128 256), losses := [] }

theorem u8436 : Upper (D 9) (R 9) [96,12,48,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8436 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8437 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 137 146 305 337 401 273), lower := (rows 97 14 100 137 146 32 64 128 256), losses := [] }

theorem u8437 : Upper (D 9) (R 9) [96,12,96,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8437 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8438 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 137 273 434 466 402 402), lower := (rows 97 14 100 137 273 32 64 128 256), losses := [] }

theorem u8438 : Upper (D 9) (R 9) [96,12,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8438 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8439 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 137 274 433 465 401 401), lower := (rows 97 14 100 137 274 32 64 128 256), losses := [] }

theorem u8439 : Upper (D 9) (R 9) [96,12,96,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8439 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8440 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 137 400 307 339 403 275), lower := (rows 97 14 100 137 400 32 64 128 256), losses := [] }

theorem u8440 : Upper (D 9) (R 9) [96,12,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8440 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8441 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 138 145 305 337 401 273), lower := (rows 97 14 100 138 145 32 64 128 256), losses := [] }

theorem u8441 : Upper (D 9) (R 9) [96,12,96,130,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8441 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8442 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 138 273 433 465 401 401), lower := (rows 97 14 100 138 273 32 64 128 256), losses := [] }

theorem u8442 : Upper (D 9) (R 9) [96,12,96,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8442 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 138 400 305 337 401 273), lower := (rows 97 14 100 138 400 32 64 128 256), losses := [] }

theorem u8443 : Upper (D 9) (R 9) [96,12,96,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8443 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8444 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 152 273 419 451 387 387), lower := (rows 97 14 100 152 273 32 64 128 256), losses := [] }

theorem u8444 : Upper (D 9) (R 9) [96,12,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8444 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8445 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 152 274 417 449 385 385), lower := (rows 97 14 100 152 274 32 64 128 256), losses := [] }

theorem u8445 : Upper (D 9) (R 9) [96,12,96,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8445 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8446 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 392 145 307 339 403 275), lower := (rows 97 14 100 392 145 32 64 128 256), losses := [] }

theorem u8446 : Upper (D 9) (R 9) [96,12,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8446 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8447 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 4, targets := 384 },{ cop := 2, region := 1, targets := 384 },{ cop := 0, region := 4, targets := 1 }], pairs := [(0,7),(0,8),(2,0),(2,7),(2,8)], upper := (rows 97 14 100 392 146 305 337 401 273), lower := (rows 97 14 100 392 146 32 64 128 256), losses := [] }

theorem u8447 : Upper (D 9) (R 9) [96,12,96,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8447 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8448 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 14 133 137 50 368 336 464 336), lower := (rows 97 14 133 137 50 32 64 128 256), losses := [] }

theorem u8448 : Upper (D 9) (R 9) [96,12,129,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8449 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 14 133 137 274 368 368 496 368), lower := (rows 97 14 133 137 274 32 64 128 256), losses := [] }

theorem u8449 : Upper (D 9) (R 9) [96,12,129,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8449 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8450 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 97 14 133 137 304 370 338 466 338), lower := (rows 97 14 133 137 304 32 64 128 256), losses := [] }

theorem u8450 : Upper (D 9) (R 9) [96,12,129,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8451 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 10, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(3,0)], upper := (rows 97 14 133 138 273 368 368 496 368), lower := (rows 97 14 133 138 273 32 64 128 256), losses := [] }

theorem u8451 : Upper (D 9) (R 9) [96,12,129,130,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8451 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8452 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 10, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(3,0)], upper := (rows 97 14 133 138 304 369 337 465 337), lower := (rows 97 14 133 138 304 32 64 128 256), losses := [] }

theorem u8452 : Upper (D 9) (R 9) [96,12,129,130,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8453 : PairBound 9 := { available := 322, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 133 152 49 354 322 450 322), lower := (rows 97 14 133 152 49 32 64 128 256), losses := [] }

theorem u8453 : Upper (D 9) (R 9) [96,12,129,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8454 : Route 9 := (fun mask => (mask,id))

def c8454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8454 : Upper (D 9) (R 9) [96,12,129,144,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,34] 13 (by decide) (choices 1) [1,64,256] r8454 c8454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6116
  · exact u6117
  · exact u6118

def b8455 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 133 152 112 291 323 387 259), lower := (rows 97 14 133 152 112 32 64 128 256), losses := [] }

theorem u8455 : Upper (D 9) (R 9) [96,12,129,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8456 : Route 9 := (fun mask => (mask,id))

def c8456 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8456 : Upper (D 9) (R 9) [96,12,129,144,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,257] 13 (by decide) (choices 1) [2,64,256] r8456 c8456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6119
  · exact u6120
  · exact u6121

def r8457 : Route 9 := (fun mask => (mask,id))

def c8457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8457 : Upper (D 9) (R 9) [96,12,129,144,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,258] 13 (by decide) (choices 1) [1,64,256] r8457 c8457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6122
  · exact u6123
  · exact u6124

def r8458 : Route 9 := (fun mask => (mask,id))

def c8458 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8458 : Upper (D 9) (R 9) [96,12,129,144,288] 13 := by
  apply FastRouting.sound _ _ [96,12,129,144,288] 13 (by decide) (choices 1) [1,2,64,256] r8458 c8458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6125
  · exact u6126
  · exact u6127
  · exact u6128

def b8459 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 14 133 168 81 306 338 402 274), lower := (rows 97 14 133 168 81 32 64 128 256), losses := [] }

theorem u8459 : Upper (D 9) (R 9) [96,12,129,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P09
