import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0130
import IrregularNine14P05C0131
import IrregularNine14P05C0132
import IrregularNine14P05C0133

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9360 : Route 9 := (fun mask => (mask,id))

def c9360 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9360 : Upper (D 5) (R 5) [18,96,40,384] 13 := by
  apply FastRouting.sound _ _ [18,96,40,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9360 c9360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7854
  · exact u7855
  · exact u7856
  · exact u7857
  · exact u7858
  · exact u7859

theorem m9361_10 : Upper (D 5) (R 5) [18,96,129,257,10] 13 :=
  permutation_upper _ _ _ [18,96,129,257,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7860

theorem m9361_40 : Upper (D 5) (R 5) [18,96,129,257,40] 13 :=
  permutation_upper _ _ _ [18,96,129,257,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7863

def r9361 : Route 9 := (fun mask => (mask,id))

def c9361 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9361 : Upper (D 5) (R 5) [18,96,129,257] 13 := by
  apply FastRouting.sound _ _ [18,96,129,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9361 c9361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7860
  · exact m9361_10
  · exact u7861
  · exact u7862
  · exact u7863
  · exact m9361_40

def r9362 : Route 9 := (fun mask => (mask,id))

def c9362 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9362 : Upper (D 5) (R 5) [18,96,129,258] 13 := by
  apply FastRouting.sound _ _ [18,96,129,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9362 c9362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7864
  · exact u7865
  · exact u7866
  · exact u7867
  · exact u7868
  · exact u7869

def r9363 : Route 9 := (fun mask => (mask,id))

def c9363 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9363 : Upper (D 5) (R 5) [18,96,129,260] 13 := by
  apply FastRouting.sound _ _ [18,96,129,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9363 c9363
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7870
  · exact u7871
  · exact u7872
  · exact u7873
  · exact u7874
  · exact u7875
  · exact u7876
  · exact u7877
  · exact u7878
  · exact u7879

def r9364 : Route 9 := (fun mask => (mask,id))

def c9364 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9364 : Upper (D 5) (R 5) [18,96,129,288] 13 := by
  apply FastRouting.sound _ _ [18,96,129,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9364 c9364
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7880
  · exact u7881
  · exact u7882
  · exact u7883
  · exact u7884
  · exact u7885

def r9365 : Route 9 := (fun mask => (mask,id))

def c9365 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9365 : Upper (D 5) (R 5) [18,96,130,260] 13 := by
  apply FastRouting.sound _ _ [18,96,130,260] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9365 c9365
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7886
  · exact u7887
  · exact u7888
  · exact u7889
  · exact u7890
  · exact u7891

def r9366 : Route 9 := (fun mask => (mask,id))

def c9366 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9366 : Upper (D 5) (R 5) [18,96,130,288] 13 := by
  apply FastRouting.sound _ _ [18,96,130,288] 13 (by decide) (choices 2) [5,9,12] r9366 c9366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7892
  · exact u7893
  · exact u7894

theorem m9367_9 : Upper (D 5) (R 5) [18,96,136,260,9] 13 :=
  permutation_upper _ _ _ [18,96,136,260,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7896

theorem m9367_10 : Upper (D 5) (R 5) [18,96,136,260,10] 13 :=
  permutation_upper _ _ _ [18,96,136,260,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7897

theorem m9367_40 : Upper (D 5) (R 5) [18,96,136,260,40] 13 :=
  permutation_upper _ _ _ [18,96,136,260,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7901

def r9367 : Route 9 := (fun mask => (mask,id))

def c9367 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9367 : Upper (D 5) (R 5) [18,96,136,260] 13 := by
  apply FastRouting.sound _ _ [18,96,136,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9367 c9367
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7895
  · exact u7896
  · exact u7897
  · exact m9367_9
  · exact m9367_10
  · exact u7898
  · exact u7899
  · exact u7900
  · exact u7901
  · exact m9367_40

def r9368 : Route 9 := (fun mask => (mask,id))

def c9368 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9368 : Upper (D 5) (R 5) [18,96,136,288] 13 := by
  apply FastRouting.sound _ _ [18,96,136,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9368 c9368
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7902
  · exact u7903
  · exact u7904
  · exact u7905
  · exact u7906
  · exact u7907

def b9369 : PairBound 9 := { available := 270, camps := [{ cop := 2, region := 8, targets := 2 },{ cop := 2, region := 8, targets := 4 }], pairs := [(3,1),(3,2)], upper := (rows 19 194 37 41 286 302 334 398 270), lower := (rows 19 194 37 41 16 32 64 128 256), losses := [] }

theorem u9369 : Upper (D 5) (R 5) [18,192,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9369
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9370 : Route 9 := (fun mask => (mask,id))

def c9370 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9370 : Upper (D 5) (R 5) [18,192,33,34] 13 := by
  apply FastRouting.sound _ _ [18,192,33,34] 13 (by decide) (choices 2) [5,9,12,257,260,264] r9370 c9370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7908
  · exact u7909
  · exact u7910
  · exact u7911
  · exact u7912
  · exact u7913

def b9371 : PairBound 9 := { available := 271, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 37 44 287 303 335 399 271), lower := (rows 19 194 37 44 16 32 64 128 256), losses := [] }

theorem u9371 : Upper (D 5) (R 5) [18,192,33,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9371
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9372 : Route 9 := (fun mask => (mask,id))

def c9372 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9372 : Upper (D 5) (R 5) [18,192,33,257] 13 := by
  apply FastRouting.sound _ _ [18,192,33,257] 13 (by decide) (choices 2) [6,10,12,34,36,40] r9372 c9372
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7914
  · exact u7915
  · exact u7916
  · exact u7917
  · exact u7918
  · exact u7919

def r9373 : Route 9 := (fun mask => (mask,id))

def c9373 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9373 : Upper (D 5) (R 5) [18,192,33,258] 13 := by
  apply FastRouting.sound _ _ [18,192,33,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9373 c9373
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7920
  · exact u7921
  · exact u7922
  · exact u7923
  · exact u7924
  · exact u7925

def r9374 : Route 9 := (fun mask => (mask,id))

def c9374 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9374 : Upper (D 5) (R 5) [18,192,33,260] 13 := by
  apply FastRouting.sound _ _ [18,192,33,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9374 c9374
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7926
  · exact u7927
  · exact u7928
  · exact u7929
  · exact u7930
  · exact u7931
  · exact u7932
  · exact u7933
  · exact u7934
  · exact u7935

def r9375 : Route 9 := (fun mask => (mask,id))

def c9375 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9375 : Upper (D 5) (R 5) [18,192,33,288] 13 := by
  apply FastRouting.sound _ _ [18,192,33,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r9375 c9375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7936
  · exact u7937
  · exact u7938
  · exact u7939
  · exact u7940
  · exact u7941

def b9376 : PairBound 9 := { available := 269, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 38 44 285 301 333 397 269), lower := (rows 19 194 38 44 16 32 64 128 256), losses := [] }

theorem u9376 : Upper (D 5) (R 5) [18,192,34,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9376
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9377 : Route 9 := (fun mask => (mask,id))

def c9377 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9377 : Upper (D 5) (R 5) [18,192,34,257] 13 := by
  apply FastRouting.sound _ _ [18,192,34,257] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9377 c9377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7942
  · exact u7943
  · exact u7944
  · exact u7945
  · exact u7946
  · exact u7947

def r9378 : Route 9 := (fun mask => (mask,id))

def c9378 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9378 : Upper (D 5) (R 5) [18,192,34,260] 13 := by
  apply FastRouting.sound _ _ [18,192,34,260] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9378 c9378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7948
  · exact u7949
  · exact u7950
  · exact u7951
  · exact u7952
  · exact u7953

def r9379 : Route 9 := (fun mask => (mask,id))

def c9379 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9379 : Upper (D 5) (R 5) [18,192,34,288] 13 := by
  apply FastRouting.sound _ _ [18,192,34,288] 13 (by decide) (choices 2) [5,9,12] r9379 c9379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u7954
  · exact u7955
  · exact u7956

def b9380 : PairBound 9 := { available := 271, camps := [{ cop := 5, region := 12, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 19 194 44 44 287 303 335 399 271), lower := (rows 19 194 44 44 16 32 64 128 256), losses := [] }

theorem u9380 : Upper (D 5) (R 5) [18,192,40,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9380
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r9381 : Route 9 := (fun mask => (mask,id))

def c9381 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9381 : Upper (D 5) (R 5) [18,192,40,257] 13 := by
  apply FastRouting.sound _ _ [18,192,40,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9381 c9381
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7957
  · exact u7958
  · exact u7959
  · exact u7960
  · exact u7961
  · exact u7962
  · exact u7963
  · exact u7964
  · exact u7965
  · exact u7966

def r9382 : Route 9 := (fun mask => (mask,id))

def c9382 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9382 : Upper (D 5) (R 5) [18,192,40,258] 13 := by
  apply FastRouting.sound _ _ [18,192,40,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r9382 c9382
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7967
  · exact u7968
  · exact u7969
  · exact u7970
  · exact u7971
  · exact u7972

def r9383 : Route 9 := (fun mask => (mask,id))

def c9383 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9383 : Upper (D 5) (R 5) [18,192,40,260] 13 := by
  apply FastRouting.sound _ _ [18,192,40,260] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r9383 c9383
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7973
  · exact u7974
  · exact u7975
  · exact u7976
  · exact u7977
  · exact u7978
  · exact u7979
  · exact u7980
  · exact u7981
  · exact u7982

def b9384 : PairBound 9 := { available := 15, camps := [{ cop := 2, region := 211, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 19 194 44 296 31 47 79 143 271), lower := (rows 19 194 44 296 16 32 64 128 256), losses := [] }

theorem u9384 : Upper (D 5) (R 5) [18,192,40,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9384
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9385 : PairBound 9 := { available := 286, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 69 140 286 318 350 414 286), lower := (rows 35 35 69 140 16 32 64 128 256), losses := [] }

theorem u9385 : Upper (D 5) (R 5) [34,33,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9385
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9386 : PairBound 9 := { available := 270, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 69 152 286 302 334 398 270), lower := (rows 35 35 69 152 16 32 64 128 256), losses := [] }

theorem u9386 : Upper (D 5) (R 5) [34,33,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9386
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9387 : PairBound 9 := { available := 30, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 69 392 30 62 94 158 286), lower := (rows 35 35 69 392 16 32 64 128 256), losses := [] }

theorem u9387 : Upper (D 5) (R 5) [34,33,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9387
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9388 : PairBound 9 := { available := 287, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 76 140 287 319 351 415 287), lower := (rows 35 35 76 140 16 32 64 128 256), losses := [] }

theorem u9388 : Upper (D 5) (R 5) [34,33,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9388
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9389 : PairBound 9 := { available := 271, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 76 152 287 303 335 399 271), lower := (rows 35 35 76 152 16 32 64 128 256), losses := [] }

theorem u9389 : Upper (D 5) (R 5) [34,33,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9389
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9390 : PairBound 9 := { available := 31, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 76 392 31 63 95 159 287), lower := (rows 35 35 76 392 16 32 64 128 256), losses := [] }

theorem u9390 : Upper (D 5) (R 5) [34,33,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9390
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9391 : PairBound 9 := { available := 15, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 84 392 31 47 79 143 271), lower := (rows 35 35 84 392 16 32 64 128 256), losses := [] }

theorem u9391 : Upper (D 5) (R 5) [34,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9391
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9392 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 69 138 285 317 349 413 285), lower := (rows 35 38 69 138 16 32 64 128 256), losses := [] }

theorem u9392 : Upper (D 5) (R 5) [34,36,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9392
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9393 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 69 140 283 315 347 411 283), lower := (rows 35 38 69 140 16 32 64 128 256), losses := [] }

theorem u9393 : Upper (D 5) (R 5) [34,36,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9393
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9394 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 69 152 287 303 335 399 271), lower := (rows 35 38 69 152 16 32 64 128 256), losses := [] }

theorem u9394 : Upper (D 5) (R 5) [34,36,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9394
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9395 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 69 392 31 63 95 159 287), lower := (rows 35 38 69 392 16 32 64 128 256), losses := [] }

theorem u9395 : Upper (D 5) (R 5) [34,36,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9395
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9396 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 70 137 285 317 349 413 285), lower := (rows 35 38 70 137 16 32 64 128 256), losses := [] }

theorem u9396 : Upper (D 5) (R 5) [34,36,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9396
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9397 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 70 140 281 313 345 409 281), lower := (rows 35 38 70 140 16 32 64 128 256), losses := [] }

theorem u9397 : Upper (D 5) (R 5) [34,36,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9397
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9398 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 70 152 285 301 333 397 269), lower := (rows 35 38 70 152 16 32 64 128 256), losses := [] }

theorem u9398 : Upper (D 5) (R 5) [34,36,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9398
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9399 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 70 392 29 61 93 157 285), lower := (rows 35 38 70 392 16 32 64 128 256), losses := [] }

theorem u9399 : Upper (D 5) (R 5) [34,36,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9399
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9400 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 76 137 287 319 351 415 287), lower := (rows 35 38 76 137 16 32 64 128 256), losses := [] }

theorem u9400 : Upper (D 5) (R 5) [34,36,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9400
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9401 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 76 138 285 317 349 413 285), lower := (rows 35 38 76 138 16 32 64 128 256), losses := [] }

theorem u9401 : Upper (D 5) (R 5) [34,36,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9401
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9402 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 76 140 283 315 347 411 283), lower := (rows 35 38 76 140 16 32 64 128 256), losses := [] }

theorem u9402 : Upper (D 5) (R 5) [34,36,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9402
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9403 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 76 152 287 303 335 399 271), lower := (rows 35 38 76 152 16 32 64 128 256), losses := [] }

theorem u9403 : Upper (D 5) (R 5) [34,36,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9403
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9404 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 76 392 31 63 95 159 287), lower := (rows 35 38 76 392 16 32 64 128 256), losses := [] }

theorem u9404 : Upper (D 5) (R 5) [34,36,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9404
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9405 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 84 137 287 303 335 399 271), lower := (rows 35 38 84 137 16 32 64 128 256), losses := [] }

theorem u9405 : Upper (D 5) (R 5) [34,36,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9405
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9406 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 84 138 285 301 333 397 269), lower := (rows 35 38 84 138 16 32 64 128 256), losses := [] }

theorem u9406 : Upper (D 5) (R 5) [34,36,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9406
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9407 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 84 140 283 299 331 395 267), lower := (rows 35 38 84 140 16 32 64 128 256), losses := [] }

theorem u9407 : Upper (D 5) (R 5) [34,36,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9407
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9408 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 84 392 31 47 79 143 271), lower := (rows 35 38 84 392 16 32 64 128 256), losses := [] }

theorem u9408 : Upper (D 5) (R 5) [34,36,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9408
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9409 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 196 265 31 63 95 159 287), lower := (rows 35 38 196 265 16 32 64 128 256), losses := [] }

theorem u9409 : Upper (D 5) (R 5) [34,36,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9409
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9410 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 196 266 29 61 93 157 285), lower := (rows 35 38 196 266 16 32 64 128 256), losses := [] }

theorem u9410 : Upper (D 5) (R 5) [34,36,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9410
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9411 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 196 268 27 59 91 155 283), lower := (rows 35 38 196 268 16 32 64 128 256), losses := [] }

theorem u9411 : Upper (D 5) (R 5) [34,36,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9411
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9412 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 196 280 31 47 79 143 271), lower := (rows 35 38 196 280 16 32 64 128 256), losses := [] }

theorem u9412 : Upper (D 5) (R 5) [34,36,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9412
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9413 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 69 138 285 301 333 397 269), lower := (rows 35 50 69 138 16 32 64 128 256), losses := [] }

theorem u9413 : Upper (D 5) (R 5) [34,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9413
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9414 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 69 140 287 303 335 399 271), lower := (rows 35 50 69 140 16 32 64 128 256), losses := [] }

theorem u9414 : Upper (D 5) (R 5) [34,48,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9414
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9415 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 69 392 31 47 79 143 271), lower := (rows 35 50 69 392 16 32 64 128 256), losses := [] }

theorem u9415 : Upper (D 5) (R 5) [34,48,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9415
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9416 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 70 140 285 301 333 397 269), lower := (rows 35 50 70 140 16 32 64 128 256), losses := [] }

theorem u9416 : Upper (D 5) (R 5) [34,48,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9416
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9417 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 70 392 29 45 77 141 269), lower := (rows 35 50 70 392 16 32 64 128 256), losses := [] }

theorem u9417 : Upper (D 5) (R 5) [34,48,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9417
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9418 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 76 140 287 303 335 399 271), lower := (rows 35 50 76 140 16 32 64 128 256), losses := [] }

theorem u9418 : Upper (D 5) (R 5) [34,48,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9418
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9419 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 76 392 31 47 79 143 271), lower := (rows 35 50 76 392 16 32 64 128 256), losses := [] }

theorem u9419 : Upper (D 5) (R 5) [34,48,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9419
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u9419
end Delivery.IrregularNine14.P05
