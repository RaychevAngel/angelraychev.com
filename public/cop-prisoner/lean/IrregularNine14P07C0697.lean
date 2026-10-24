import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0554
import IrregularNine14P07C0555
import IrregularNine14P07C0556
import IrregularNine14P07C0557
import IrregularNine14P07C0558

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r41820 : Route 9 := (fun mask => (mask,id))

def c41820 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41820 : Upper (D 7) (R 7) [12,96,130,160] 13 := by
  apply FastRouting.sound _ _ [12,96,130,160] 13 (by decide) (choices 2) [3,65,66,257,258,320] r41820 c41820
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33270
  · exact u33271
  · exact u33272
  · exact u33273
  · exact u33274
  · exact u33275

def r41821 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41821 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41821 : Upper (D 7) (R 7) [12,96,130,257] 13 := by
  apply FastRouting.sound _ _ [12,96,130,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41821 c41821
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33276
  · exact u33277
  · exact u33278
  · exact u33279
  · exact u33280
  · exact u33281
  · exact u33282

def r41822 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41822 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41822 : Upper (D 7) (R 7) [12,96,130,258] 13 := by
  apply FastRouting.sound _ _ [12,96,130,258] 13 (by decide) (choices 2) [33,96,129,160] r41822 c41822
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33283
  · exact u33284
  · exact u33285
  · exact u33286

def r41823 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41823 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41823 : Upper (D 7) (R 7) [12,96,130,272] 13 := by
  apply FastRouting.sound _ _ [12,96,130,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41823 c41823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33287
  · exact u33288
  · exact u33289
  · exact u33290
  · exact u33291
  · exact u33292
  · exact u33293

def r41824 : Route 9 := (fun mask => (mask,id))

def c41824 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41824 : Upper (D 7) (R 7) [12,96,130,288] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41824 c41824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33294
  · exact u33295
  · exact u33296
  · exact u33297
  · exact u33298
  · exact u33299

def r41825 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41825 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41825 : Upper (D 7) (R 7) [12,96,130,384] 13 := by
  apply FastRouting.sound _ _ [12,96,130,384] 13 (by decide) (choices 2) [3,33,34,96] r41825 c41825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33300
  · exact u33301
  · exact u33302
  · exact u33303

def r41826 : Route 9 := (fun mask => (mask,id))

def c41826 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u41826 : Upper (D 7) (R 7) [12,96,144,160] 13 := by
  apply FastRouting.sound _ _ [12,96,144,160] 13 (by decide) (choices 2) [3,65,66,257,258,320] r41826 c41826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33304
  · exact u33305
  · exact u33306
  · exact u33307
  · exact u33308
  · exact u33309

def r41827 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41827 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41827 : Upper (D 7) (R 7) [12,96,144,257] 13 := by
  apply FastRouting.sound _ _ [12,96,144,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41827 c41827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33310
  · exact u33311
  · exact u33312
  · exact u33313
  · exact u33314
  · exact u33315
  · exact u33316

def r41828 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41828 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41828 : Upper (D 7) (R 7) [12,96,144,258] 13 := by
  apply FastRouting.sound _ _ [12,96,144,258] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41828 c41828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33317
  · exact u33318
  · exact u33319
  · exact u33320
  · exact u33321
  · exact u33322
  · exact u33323

def r41829 : Route 9 := (fun mask => (mask,id))

def c41829 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41829 : Upper (D 7) (R 7) [12,96,144,288] 13 := by
  apply FastRouting.sound _ _ [12,96,144,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41829 c41829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33324
  · exact u33325
  · exact u33326
  · exact u33327
  · exact u33328
  · exact u33329

def r41830 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41830 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41830 : Upper (D 7) (R 7) [12,96,144,384] 13 := by
  apply FastRouting.sound _ _ [12,96,144,384] 13 (by decide) (choices 2) [3,33,34,96] r41830 c41830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33330
  · exact u33331
  · exact u33332
  · exact u33333

def r41831 : Route 9 := (fun mask => (mask,id))

def c41831 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u41831 : Upper (D 7) (R 7) [12,96,160,192] 13 := by
  apply FastRouting.sound _ _ [12,96,160,192] 13 (by decide) (choices 2) [3,257,258] r41831 c41831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33334
  · exact u33335
  · exact u33336

def r41832 : Route 9 := (fun mask => (mask,id))

def c41832 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41832 : Upper (D 7) (R 7) [12,96,160,257] 13 := by
  apply FastRouting.sound _ _ [12,96,160,257] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41832 c41832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33337
  · exact u33338
  · exact u33339
  · exact u33340
  · exact u33341
  · exact u33342

def r41833 : Route 9 := (fun mask => (mask,id))

def c41833 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41833 : Upper (D 7) (R 7) [12,96,160,258] 13 := by
  apply FastRouting.sound _ _ [12,96,160,258] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41833 c41833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33343
  · exact u33344
  · exact u33345
  · exact u33346
  · exact u33347
  · exact u33348

def r41834 : Route 9 := (fun mask => (mask,id))

def c41834 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41834 : Upper (D 7) (R 7) [12,96,160,272] 13 := by
  apply FastRouting.sound _ _ [12,96,160,272] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41834 c41834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33349
  · exact u33350
  · exact u33351
  · exact u33352
  · exact u33353
  · exact u33354

def r41835 : Route 9 := (fun mask => (mask,id))

def c41835 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u41835 : Upper (D 7) (R 7) [12,96,160,320] 13 := by
  apply FastRouting.sound _ _ [12,96,160,320] 13 (by decide) (choices 2) [3,129,130] r41835 c41835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33355
  · exact u33356
  · exact u33357

def r41836 : Route 9 := (fun mask => (mask,id))

def c41836 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u41836 : Upper (D 7) (R 7) [12,96,160,384] 13 := by
  apply FastRouting.sound _ _ [12,96,160,384] 13 (by decide) (choices 2) [3,65,66] r41836 c41836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u33358
  · exact u33359
  · exact u33360

def b41837 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 259 7 26 240 224 224 224 480), lower := (rows 13 259 7 26 16 32 64 128 256), losses := [] }

theorem u41837 : Upper (D 7) (R 7) [12,257,3,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41838 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 259 7 42 240 240 240 240 496), lower := (rows 13 259 7 42 16 32 64 128 256), losses := [] }

theorem u41838 : Upper (D 7) (R 7) [12,257,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41839 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 259 7 56 242 226 226 226 482), lower := (rows 13 259 7 56 16 32 64 128 256), losses := [] }

theorem u41839 : Upper (D 7) (R 7) [12,257,3,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41839 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41840 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 4, targets := 224 },{ cop := 1, region := 248, targets := 1 }], pairs := [(2,5),(2,6),(2,7),(3,0)], upper := (rows 13 259 7 104 242 242 242 242 498), lower := (rows 13 259 7 104 16 32 64 128 256), losses := [] }

theorem u41840 : Upper (D 7) (R 7) [12,257,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41841 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41841 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41841 : Upper (D 7) (R 7) [12,257,17,34] 13 := by
  apply FastRouting.sound _ _ [12,257,17,34] 13 (by decide) (choices 2) [34,66,96,192] r41841 c41841
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33361
  · exact u33362
  · exact u33363
  · exact u33364

def r41842 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41842 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41842 : Upper (D 7) (R 7) [12,257,17,96] 13 := by
  apply FastRouting.sound _ _ [12,257,17,96] 13 (by decide) (choices 2) [34,96,130,160] r41842 c41842
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33365
  · exact u33366
  · exact u33367
  · exact u33368

def r41843 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41843 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41843 : Upper (D 7) (R 7) [12,257,18,33] 13 := by
  apply FastRouting.sound _ _ [12,257,18,33] 13 (by decide) (choices 2) [34,66,96,192] r41843 c41843
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33369
  · exact u33370
  · exact u33371
  · exact u33372

def r41844 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41844 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41844 : Upper (D 7) (R 7) [12,257,18,34] 13 := by
  apply FastRouting.sound _ _ [12,257,18,34] 13 (by decide) (choices 2) [33,65,96,192] r41844 c41844
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33373
  · exact u33374
  · exact u33375
  · exact u33376

def r41845 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41845 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41845 : Upper (D 7) (R 7) [12,257,18,96] 13 := by
  apply FastRouting.sound _ _ [12,257,18,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41845 c41845
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33377
  · exact u33378
  · exact u33379
  · exact u33380
  · exact u33381
  · exact u33382
  · exact u33383

def b41846 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 259 37 42 210 242 210 210 466), lower := (rows 13 259 37 42 16 32 64 128 256), losses := [] }

theorem u41846 : Upper (D 7) (R 7) [12,257,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41847 : PairBound 9 := { available := 194, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 259 37 56 210 226 194 194 450), lower := (rows 13 259 37 56 16 32 64 128 256), losses := [] }

theorem u41847 : Upper (D 7) (R 7) [12,257,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41848 : Route 9 := (fun mask => (mask,id))

def c41848 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41848 : Upper (D 7) (R 7) [12,257,33,66] 13 := by
  apply FastRouting.sound _ _ [12,257,33,66] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41848 c41848
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33384
  · exact u33385
  · exact u33386
  · exact u33387
  · exact u33388
  · exact u33389

def r41849 : Route 9 := (fun mask => (mask,id))

def c41849 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41849 : Upper (D 7) (R 7) [12,257,33,80] 13 := by
  apply FastRouting.sound _ _ [12,257,33,80] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41849 c41849
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33390
  · exact u33391
  · exact u33392
  · exact u33393
  · exact u33394
  · exact u33395

def b41850 : PairBound 9 := { available := 210, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 259 37 104 210 242 210 210 466), lower := (rows 13 259 37 104 16 32 64 128 256), losses := [] }

theorem u41850 : Upper (D 7) (R 7) [12,257,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41850 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41851 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41851 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41851 : Upper (D 7) (R 7) [12,257,33,192] 13 := by
  apply FastRouting.sound _ _ [12,257,33,192] 13 (by decide) (choices 2) [34,66,96,192] r41851 c41851
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33396
  · exact u33397
  · exact u33398
  · exact u33399

def b41852 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 9, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 259 38 42 209 241 209 209 465), lower := (rows 13 259 38 42 16 32 64 128 256), losses := [] }

theorem u41852 : Upper (D 7) (R 7) [12,257,34,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41852 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41853 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41853 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41853 : Upper (D 7) (R 7) [12,257,34,48] 13 := by
  apply FastRouting.sound _ _ [12,257,34,48] 13 (by decide) (choices 2) [3,65,66,192] r41853 c41853
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33400
  · exact u33401
  · exact u33402
  · exact u33403

theorem m41854_65 : Upper (D 7) (R 7) [12,257,34,66,65] 13 :=
  permutation_upper _ _ _ [12,257,34,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33404

theorem m41854_192 : Upper (D 7) (R 7) [12,257,34,66,192] 13 :=
  permutation_upper _ _ _ [12,257,34,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33407

def r41854 : Route 9 := (fun mask => (mask,id))

def c41854 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41854 : Upper (D 7) (R 7) [12,257,34,66] 13 := by
  apply FastRouting.sound _ _ [12,257,34,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41854 c41854
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33404
  · exact m41854_65
  · exact u33405
  · exact u33406
  · exact u33407
  · exact m41854_192

def r41855 : Route 9 := (fun mask => (mask,id))

def c41855 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41855 : Upper (D 7) (R 7) [12,257,34,80] 13 := by
  apply FastRouting.sound _ _ [12,257,34,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41855 c41855
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33408
  · exact u33409
  · exact u33410
  · exact u33411
  · exact u33412
  · exact u33413
  · exact u33414
  · exact u33415
  · exact u33416
  · exact u33417

def r41856 : Route 9 := (fun mask => (mask,id))

def c41856 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41856 : Upper (D 7) (R 7) [12,257,34,96] 13 := by
  apply FastRouting.sound _ _ [12,257,34,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41856 c41856
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33418
  · exact u33419
  · exact u33420
  · exact u33421
  · exact u33422
  · exact u33423

def r41857 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41857 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41857 : Upper (D 7) (R 7) [12,257,34,192] 13 := by
  apply FastRouting.sound _ _ [12,257,34,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41857 c41857
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33424
  · exact u33425
  · exact u33426
  · exact u33427
  · exact u33428
  · exact u33429
  · exact u33430

def r41858 : Route 9 := (fun mask => (mask,id))

def c41858 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41858 : Upper (D 7) (R 7) [12,257,48,96] 13 := by
  apply FastRouting.sound _ _ [12,257,48,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41858 c41858
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33431
  · exact u33432
  · exact u33433
  · exact u33434
  · exact u33435
  · exact u33436

def r41859 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41859 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41859 : Upper (D 7) (R 7) [12,257,48,192] 13 := by
  apply FastRouting.sound _ _ [12,257,48,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41859 c41859
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33437
  · exact u33438
  · exact u33439
  · exact u33440
  · exact u33441
  · exact u33442
  · exact u33443

def b41860 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 9, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 259 100 104 147 179 211 147 403), lower := (rows 13 259 100 104 16 32 64 128 256), losses := [] }

theorem u41860 : Upper (D 7) (R 7) [12,257,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41860 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41861_129 : Upper (D 7) (R 7) [12,257,96,160,129] 13 :=
  permutation_upper _ _ _ [12,257,96,160,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33445

theorem m41861_130 : Upper (D 7) (R 7) [12,257,96,160,130] 13 :=
  permutation_upper _ _ _ [12,257,96,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33446

def r41861 : Route 9 := (fun mask => (mask,id))

def c41861 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41861 : Upper (D 7) (R 7) [12,257,96,160] 13 := by
  apply FastRouting.sound _ _ [12,257,96,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41861 c41861
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33444
  · exact u33445
  · exact u33446
  · exact m41861_129
  · exact m41861_130
  · exact u33447

def b41862 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 274 7 11 240 224 224 224 480), lower := (rows 13 274 7 11 16 32 64 128 256), losses := [] }

theorem u41862 : Upper (D 7) (R 7) [12,272,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41863 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41863 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41863 : Upper (D 7) (R 7) [12,272,3,33] 13 := by
  apply FastRouting.sound _ _ [12,272,3,33] 13 (by decide) (choices 2) [34,66,96,192] r41863 c41863
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33448
  · exact u33449
  · exact u33450
  · exact u33451

def b41864 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 5, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 274 7 42 241 225 225 225 481), lower := (rows 13 274 7 42 16 32 64 128 256), losses := [] }

theorem u41864 : Upper (D 7) (R 7) [12,272,3,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41865 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c41865 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41865 : Upper (D 7) (R 7) [12,272,3,96] 13 := by
  apply FastRouting.sound _ _ [12,272,3,96] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r41865 c41865
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33452
  · exact u33453
  · exact u33454
  · exact u33455
  · exact u33456
  · exact u33457
  · exact u33458

def b41866 : PairBound 9 := { available := 194, camps := [{ cop := 5, region := 13, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 41 210 226 194 194 450), lower := (rows 13 274 37 41 16 32 64 128 256), losses := [] }

theorem u41866 : Upper (D 7) (R 7) [12,272,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41867 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 42 211 227 195 195 451), lower := (rows 13 274 37 42 16 32 64 128 256), losses := [] }

theorem u41867 : Upper (D 7) (R 7) [12,272,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41868_66 : Upper (D 7) (R 7) [12,272,33,65,66] 13 :=
  permutation_upper _ _ _ [12,272,33,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33459

theorem m41868_192 : Upper (D 7) (R 7) [12,272,33,65,192] 13 :=
  permutation_upper _ _ _ [12,272,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33462

def r41868 : Route 9 := (fun mask => (mask,id))

def c41868 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41868 : Upper (D 7) (R 7) [12,272,33,65] 13 := by
  apply FastRouting.sound _ _ [12,272,33,65] 13 (by decide) (choices 2) [34,66,96,130,160,192] r41868 c41868
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33459
  · exact m41868_66
  · exact u33460
  · exact u33461
  · exact u33462
  · exact m41868_192

def r41869 : Route 9 := (fun mask => (mask,id))

def c41869 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41869 : Upper (D 7) (R 7) [12,272,33,66] 13 := by
  apply FastRouting.sound _ _ [12,272,33,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r41869 c41869
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33463
  · exact u33464
  · exact u33465
  · exact u33466
  · exact u33467
  · exact u33468
  · exact u33469
  · exact u33470
  · exact u33471
  · exact u33472

def b41870 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 5, targets := 194 }], pairs := [(0,1),(0,6),(0,7),(2,1)], upper := (rows 13 274 37 104 211 227 195 195 451), lower := (rows 13 274 37 104 16 32 64 128 256), losses := [] }

theorem u41870 : Upper (D 7) (R 7) [12,272,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41870 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41871 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41871 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41871 : Upper (D 7) (R 7) [12,272,33,192] 13 := by
  apply FastRouting.sound _ _ [12,272,33,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41871 c41871
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33473
  · exact u33474
  · exact u33475
  · exact u33476
  · exact u33477
  · exact u33478
  · exact u33479

def b41872 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 9, targets := 192 }], pairs := [(0,6),(0,7),(3,6),(3,7)], upper := (rows 13 274 38 42 209 225 193 193 449), lower := (rows 13 274 38 42 16 32 64 128 256), losses := [] }

theorem u41872 : Upper (D 7) (R 7) [12,272,34,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41873_65 : Upper (D 7) (R 7) [12,272,34,66,65] 13 :=
  permutation_upper _ _ _ [12,272,34,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33480

theorem m41873_192 : Upper (D 7) (R 7) [12,272,34,66,192] 13 :=
  permutation_upper _ _ _ [12,272,34,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33483

def r41873 : Route 9 := (fun mask => (mask,id))

def c41873 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41873 : Upper (D 7) (R 7) [12,272,34,66] 13 := by
  apply FastRouting.sound _ _ [12,272,34,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r41873 c41873
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33480
  · exact m41873_65
  · exact u33481
  · exact u33482
  · exact u33483
  · exact m41873_192

def r41874 : Route 9 := (fun mask => (mask,id))

def c41874 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41874 : Upper (D 7) (R 7) [12,272,34,96] 13 := by
  apply FastRouting.sound _ _ [12,272,34,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41874 c41874
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33484
  · exact u33485
  · exact u33486
  · exact u33487
  · exact u33488
  · exact u33489

def r41875 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41875 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41875 : Upper (D 7) (R 7) [12,272,34,192] 13 := by
  apply FastRouting.sound _ _ [12,272,34,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r41875 c41875
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33490
  · exact u33491
  · exact u33492
  · exact u33493
  · exact u33494
  · exact u33495
  · exact u33496

def b41876 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 9, targets := 130 }], pairs := [(0,1),(0,7),(3,1),(3,7)], upper := (rows 13 274 100 104 147 163 195 131 387), lower := (rows 13 274 100 104 16 32 64 128 256), losses := [] }

theorem u41876 : Upper (D 7) (R 7) [12,272,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41876 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

theorem m41877_129 : Upper (D 7) (R 7) [12,272,96,160,129] 13 :=
  permutation_upper _ _ _ [12,272,96,160,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33498

theorem m41877_130 : Upper (D 7) (R 7) [12,272,96,160,130] 13 :=
  permutation_upper _ _ _ [12,272,96,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u33499

def r41877 : Route 9 := (fun mask => (mask,id))

def c41877 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41877 : Upper (D 7) (R 7) [12,272,96,160] 13 := by
  apply FastRouting.sound _ _ [12,272,96,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r41877 c41877
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u33497
  · exact u33498
  · exact u33499
  · exact m41877_129
  · exact m41877_130
  · exact u33500

def b41878 : PairBound 9 := { available := 240, camps := [{ cop := 1, region := 13, targets := 224 }], pairs := [(0,5),(0,6),(0,7),(2,5)], upper := (rows 13 290 7 11 240 240 240 240 496), lower := (rows 13 290 7 11 16 32 64 128 256), losses := [] }

theorem u41878 : Upper (D 7) (R 7) [12,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41878 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r41879 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c41879 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u41879 : Upper (D 7) (R 7) [12,288,3,17] 13 := by
  apply FastRouting.sound _ _ [12,288,3,17] 13 (by decide) (choices 2) [34,66,96,192] r41879 c41879
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u33501
  · exact u33502
  · exact u33503
  · exact u33504

#print axioms u41879
end Delivery.IrregularNine14.P07
