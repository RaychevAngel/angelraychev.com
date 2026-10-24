import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0071
import IrregularNine14P01C0072

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7620 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 140 283 299 331 395 267), lower := (rows 113 146 100 140 16 32 64 128 256), losses := [] }

theorem u7620 : Upper (D 1) (R 1) [112,144,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7621 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 265 158 174 206 142 398), lower := (rows 113 146 100 265 16 32 64 128 256), losses := [] }

theorem u7621 : Upper (D 1) (R 1) [112,144,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7622 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 266 159 175 207 143 399), lower := (rows 113 146 100 266 16 32 64 128 256), losses := [] }

theorem u7622 : Upper (D 1) (R 1) [112,144,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7623 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 268 155 171 203 139 395), lower := (rows 113 146 100 268 16 32 64 128 256), losses := [] }

theorem u7623 : Upper (D 1) (R 1) [112,144,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7623
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7624 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 146 100 392 31 47 79 143 271), lower := (rows 113 146 100 392 16 32 64 128 256), losses := [] }

theorem u7624 : Upper (D 1) (R 1) [112,144,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7624
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7625 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7625 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7625 : Upper (D 1) (R 1) [112,144,129,258] 13 := by
  apply FastRouting.sound _ _ [112,144,129,258] 13 (by decide) (choices 1) [2,4,8,32] r7625 c7625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4268
  · exact u4269
  · exact u4270
  · exact u4271

def r7626 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7626 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7626 : Upper (D 1) (R 1) [112,144,129,260] 13 := by
  apply FastRouting.sound _ _ [112,144,129,260] 13 (by decide) (choices 1) [2,8,32] r7626 c7626
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4272
  · exact u4273
  · exact u4274

def r7627 : Route 9 := (fun mask => (mask,id))

def c7627 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7627 : Upper (D 1) (R 1) [112,144,129,288] 13 := by
  apply FastRouting.sound _ _ [112,144,129,288] 13 (by decide) (choices 1) [2,4,8,64] r7627 c7627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4275
  · exact u4276
  · exact u4277
  · exact u4278

def b7628 : PairBound 9 := { available := 110, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 134 265 126 110 110 238 366), lower := (rows 113 146 134 265 16 32 64 128 256), losses := [] }

theorem u7628 : Upper (D 1) (R 1) [112,144,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7628
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7629 : PairBound 9 := { available := 109, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 134 266 125 109 109 237 365), lower := (rows 113 146 134 266 16 32 64 128 256), losses := [] }

theorem u7629 : Upper (D 1) (R 1) [112,144,130,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7630 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 134 268 123 107 107 235 363), lower := (rows 113 146 134 268 16 32 64 128 256), losses := [] }

theorem u7630 : Upper (D 1) (R 1) [112,144,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7631 : PairBound 9 := { available := 79, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 146 134 296 95 111 79 207 335), lower := (rows 113 146 134 296 16 32 64 128 256), losses := [] }

theorem u7631 : Upper (D 1) (R 1) [112,144,130,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7632 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7632 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7632 : Upper (D 1) (R 1) [112,144,136,257] 13 := by
  apply FastRouting.sound _ _ [112,144,136,257] 13 (by decide) (choices 1) [2,4,32] r7632 c7632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4279
  · exact u4280
  · exact u4281

def r7633 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7633 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7633 : Upper (D 1) (R 1) [112,144,136,258] 13 := by
  apply FastRouting.sound _ _ [112,144,136,258] 13 (by decide) (choices 1) [1,2,4,32] r7633 c7633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4282
  · exact u4283
  · exact u4284
  · exact u4285

def b7634 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 146 140 268 115 99 99 227 355), lower := (rows 113 146 140 268 16 32 64 128 256), losses := [] }

theorem u7634 : Upper (D 1) (R 1) [112,144,136,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7635 : Route 9 := (fun mask => (mask,id))

def c7635 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7635 : Upper (D 1) (R 1) [112,144,136,288] 13 := by
  apply FastRouting.sound _ _ [112,144,136,288] 13 (by decide) (choices 1) [1,2,4,64] r7635 c7635
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4286
  · exact u4287
  · exact u4288
  · exact u4289

def r7636 : Route 9 := (fun mask => (mask,id))

def c7636 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7636 : Upper (D 1) (R 1) [112,144,160,257] 13 := by
  apply FastRouting.sound _ _ [112,144,160,257] 13 (by decide) (choices 1) [2,4,8,64] r7636 c7636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4290
  · exact u4291
  · exact u4292
  · exact u4293

def r7637 : Route 9 := (fun mask => (mask,id))

def c7637 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7637 : Upper (D 1) (R 1) [112,144,160,258] 13 := by
  apply FastRouting.sound _ _ [112,144,160,258] 13 (by decide) (choices 1) [1,2,4,8,64] r7637 c7637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u4294
  · exact u4295
  · exact u4296
  · exact u4297
  · exact u4298

def r7638 : Route 9 := (fun mask => (mask,id))

def c7638 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7638 : Upper (D 1) (R 1) [112,144,160,260] 13 := by
  apply FastRouting.sound _ _ [112,144,160,260] 13 (by decide) (choices 1) [1,2,8,64] r7638 c7638
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4299
  · exact u4300
  · exact u4301
  · exact u4302

def r7639 : Route 9 := (fun mask => (mask,id))

def c7639 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7639 : Upper (D 1) (R 1) [112,144,160,320] 13 := by
  apply FastRouting.sound _ _ [112,144,160,320] 13 (by decide) (choices 1) [1,2,4,8] r7639 c7639
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4303
  · exact u4304
  · exact u4305
  · exact u4306

def b7640 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 113 259 14 14 240 240 240 240 496), lower := (rows 113 259 14 14 16 32 64 128 256), losses := [] }

theorem u7640 : Upper (D 1) (R 1) [112,257,10,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7640
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7641 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 113 259 14 26 244 228 228 228 484), lower := (rows 113 259 14 26 16 32 64 128 256), losses := [] }

theorem u7641 : Upper (D 1) (R 1) [112,257,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7642 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 259 14 28 242 226 226 226 482), lower := (rows 113 259 14 28 16 32 64 128 256), losses := [] }

theorem u7642 : Upper (D 1) (R 1) [112,257,10,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7643 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 259 14 56 214 230 198 198 454), lower := (rows 113 259 14 56 16 32 64 128 256), losses := [] }

theorem u7643 : Upper (D 1) (R 1) [112,257,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7644 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 259 14 138 244 244 244 244 500), lower := (rows 113 259 14 138 16 32 64 128 256), losses := [] }

theorem u7644 : Upper (D 1) (R 1) [112,257,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7644
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7645 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7645 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7645 : Upper (D 1) (R 1) [112,257,10,132] 13 := by
  apply FastRouting.sound _ _ [112,257,10,132] 13 (by decide) (choices 1) [2,32,128] r7645 c7645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4307
  · exact u4308
  · exact u4309

def r7646 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7646 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7646 : Upper (D 1) (R 1) [112,257,10,144] 13 := by
  apply FastRouting.sound _ _ [112,257,10,144] 13 (by decide) (choices 1) [2,4,32,128] r7646 c7646
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4310
  · exact u4311
  · exact u4312
  · exact u4313

def b7647 : PairBound 9 := { available := 202, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 259 22 44 218 234 202 202 458), lower := (rows 113 259 22 44 16 32 64 128 256), losses := [] }

theorem u7647 : Upper (D 1) (R 1) [112,257,18,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7648 : PairBound 9 := { available := 236, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 259 22 138 252 236 236 236 492), lower := (rows 113 259 22 138 16 32 64 128 256), losses := [] }

theorem u7648 : Upper (D 1) (R 1) [112,257,18,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7649 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 259 22 140 250 234 234 234 490), lower := (rows 113 259 22 140 16 32 64 128 256), losses := [] }

theorem u7649 : Upper (D 1) (R 1) [112,257,18,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7650 : PairBound 9 := { available := 206, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 113 259 22 168 222 238 206 206 462), lower := (rows 113 259 22 168 16 32 64 128 256), losses := [] }

theorem u7650 : Upper (D 1) (R 1) [112,257,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7651 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 28 44 210 226 194 194 450), lower := (rows 113 259 28 44 16 32 64 128 256), losses := [] }

theorem u7651 : Upper (D 1) (R 1) [112,257,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7652 : PairBound 9 := { available := 134, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 28 104 150 166 198 134 390), lower := (rows 113 259 28 104 16 32 64 128 256), losses := [] }

theorem u7652 : Upper (D 1) (R 1) [112,257,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7652
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7653 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7653 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 256 => 8 | _ => 0)

theorem u7653 : Upper (D 1) (R 1) [112,257,24,130] 13 := by
  apply FastRouting.sound _ _ [112,257,24,130] 13 (by decide) (choices 1) [2,4,32,128] r7653 c7653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4314
  · exact u4315
  · exact u4316
  · exact u4317

def b7654 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 386, targets := 16 }], pairs := [(1,4)], upper := (rows 113 259 28 140 242 226 226 226 482), lower := (rows 113 259 28 140 16 32 64 128 256), losses := [] }

theorem u7654 : Upper (D 1) (R 1) [112,257,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7655 : Route 9 := (fun mask => (mask,id))

def c7655 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u7655 : Upper (D 1) (R 1) [112,257,24,160] 13 := by
  apply FastRouting.sound _ _ [112,257,24,160] 13 (by decide) (choices 1) [2,4,64,128] r7655 c7655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4318
  · exact u4319
  · exact u4320
  · exact u4321

def b7656 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 52 138 222 238 206 206 462), lower := (rows 113 259 52 138 16 32 64 128 256), losses := [] }

theorem u7656 : Upper (D 1) (R 1) [112,257,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7657 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 52 140 218 234 202 202 458), lower := (rows 113 259 52 140 16 32 64 128 256), losses := [] }

theorem u7657 : Upper (D 1) (R 1) [112,257,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7658 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 52 200 158 174 206 142 398), lower := (rows 113 259 52 200 16 32 64 128 256), losses := [] }

theorem u7658 : Upper (D 1) (R 1) [112,257,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7659 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 113 259 134 138 124 124 124 252 380), lower := (rows 113 259 134 138 16 32 64 128 256), losses := [] }

theorem u7659 : Upper (D 1) (R 1) [112,257,130,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7659
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7660 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 259 134 140 122 122 122 250 378), lower := (rows 113 259 134 140 16 32 64 128 256), losses := [] }

theorem u7660 : Upper (D 1) (R 1) [112,257,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7661 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7661 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u7661 : Upper (D 1) (R 1) [112,257,130,144] 13 := by
  apply FastRouting.sound _ _ [112,257,130,144] 13 (by decide) (choices 1) [2,4,8,32] r7661 c7661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4322
  · exact u4323
  · exact u4324
  · exact u4325

def b7662 : PairBound 9 := { available := 114, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 140 140 114 114 114 242 370), lower := (rows 113 259 140 140 16 32 64 128 256), losses := [] }

theorem u7662 : Upper (D 1) (R 1) [112,257,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7663 : PairBound 9 := { available := 102, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 259 140 152 118 102 102 230 358), lower := (rows 113 259 140 152 16 32 64 128 256), losses := [] }

theorem u7663 : Upper (D 1) (R 1) [112,257,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7664 : Route 9 := (fun mask => (mask,id))

def c7664 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7664 : Upper (D 1) (R 1) [112,257,144,160] 13 := by
  apply FastRouting.sound _ _ [112,257,144,160] 13 (by decide) (choices 1) [2,4,8,64] r7664 c7664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4326
  · exact u4327
  · exact u4328
  · exact u4329

def b7665 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 225, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 7 26 248 232 232 232 488), lower := (rows 113 262 7 26 16 32 64 128 256), losses := [] }

theorem u7665 : Upper (D 1) (R 1) [112,260,3,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7666 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 7 56 218 234 202 202 458), lower := (rows 113 262 7 56 16 32 64 128 256), losses := [] }

theorem u7666 : Upper (D 1) (R 1) [112,260,3,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7667 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 113, targets := 2 }], pairs := [(0,1)], upper := (rows 113 262 7 138 248 248 248 248 504), lower := (rows 113 262 7 138 16 32 64 128 256), losses := [] }

theorem u7667 : Upper (D 1) (R 1) [112,260,3,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7667
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7668 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 256 => 8 | _ => 0)

theorem u7668 : Upper (D 1) (R 1) [112,260,3,144] 13 := by
  apply FastRouting.sound _ _ [112,260,3,144] 13 (by decide) (choices 1) [2,8,32,128] r7668 c7668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4330
  · exact u4331
  · exact u4332
  · exact u4333

def b7669 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 262 13 26 242 226 226 226 482), lower := (rows 113 262 13 26 16 32 64 128 256), losses := [] }

theorem u7669 : Upper (D 1) (R 1) [112,260,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7670 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 113 262 13 56 210 226 194 194 450), lower := (rows 113 262 13 56 16 32 64 128 256), losses := [] }

theorem u7670 : Upper (D 1) (R 1) [112,260,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7670
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7671 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7671 : Upper (D 1) (R 1) [112,260,9,130] 13 := by
  apply FastRouting.sound _ _ [112,260,9,130] 13 (by decide) (choices 1) [2,32,128] r7671 c7671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4334
  · exact u4335
  · exact u4336

def b7672 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 482, targets := 16 }], pairs := [(1,4)], upper := (rows 113 262 13 152 242 226 226 226 482), lower := (rows 113 262 13 152 16 32 64 128 256), losses := [] }

theorem u7672 : Upper (D 1) (R 1) [112,260,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7673 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 262 14 11 240 240 240 240 496), lower := (rows 113 262 14 11 16 32 64 128 256), losses := [] }

theorem u7673 : Upper (D 1) (R 1) [112,260,10,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7673
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7674 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 14 25 242 226 226 226 482), lower := (rows 113 262 14 25 16 32 64 128 256), losses := [] }

theorem u7674 : Upper (D 1) (R 1) [112,260,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7674
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7675 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 262 14 26 241 225 225 225 481), lower := (rows 113 262 14 26 16 32 64 128 256), losses := [] }

theorem u7675 : Upper (D 1) (R 1) [112,260,10,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b7676 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 113 262 14 56 211 227 195 195 451), lower := (rows 113 262 14 56 16 32 64 128 256), losses := [] }

theorem u7676 : Upper (D 1) (R 1) [112,260,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7677 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7677 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7677 : Upper (D 1) (R 1) [112,260,10,129] 13 := by
  apply FastRouting.sound _ _ [112,260,10,129] 13 (by decide) (choices 1) [2,32,128] r7677 c7677
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u4337
  · exact u4338
  · exact u4339

def b7678 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 262 14 138 241 241 241 241 497), lower := (rows 113 262 14 138 16 32 64 128 256), losses := [] }

theorem u7678 : Upper (D 1) (R 1) [112,260,10,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b7678
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r7679 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7679 : Upper (D 1) (R 1) [112,260,10,144] 13 := by
  apply FastRouting.sound _ _ [112,260,10,144] 13 (by decide) (choices 1) [1,2,32,128] r7679 c7679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4340
  · exact u4341
  · exact u4342
  · exact u4343

#print axioms u7679
end Delivery.IrregularNine14.P01
