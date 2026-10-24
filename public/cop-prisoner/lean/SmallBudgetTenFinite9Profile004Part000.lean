import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile4_node4_cert : CutBound 9 := { lost := (rows 64 64 0 0 0 0 0 0 0), upper := (rows 19 35 196 200 272 288 64 128 256), lower := (rows 19 35 196 200 16 32 64 128 256), losses := [{ target := 6, region := (rows 511 511 4 8 511 511 0 511 511), good := (rows 435 435 439 443 435 435 435 435 435) }] }

theorem profile4_node4 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,192] 6 256 profile4_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,192] 6 256 profile4_node4_cert).mp (by decide +kernel))

def profile4_node5_cert : CutBound 9 := { lost := (rows 64 64 0 0 0 0 0 0 0), upper := (rows 19 35 196 328 400 416 64 128 256), lower := (rows 19 35 196 328 16 32 64 128 256), losses := [{ target := 6, region := (rows 511 511 4 8 511 511 0 511 511), good := (rows 435 435 439 443 435 435 435 435 435) }] }

theorem profile4_node5 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,320] 6 384 profile4_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192,320] 6 384 profile4_node5_cert).mp (by decide +kernel))

def profile4_node3_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 5 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile4_node3_route : Route 9 := (fun mask => match mask with | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node3 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33,192] 6 (by decide) (choices 2) [192,320] profile4_node3_route profile4_node3_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node4
  · exact profile4_node5

def profile4_node2_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile4_node2_route : Route 9 := (fun mask => match mask with | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node2 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,33] 6 (by decide) (choices 2) [192] profile4_node2_route profile4_node2_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile4_node3

def profile4_node6_cert : CutBound 9 := { lost := (rows 128 128 0 0 0 0 0 0 0), upper := (rows 19 67 484 488 496 480 64 128 256), lower := (rows 19 67 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 17 19 4 8 16 32 511 0 511), good := (rows 339 323 324 328 339 352 320 320 320) }] }

theorem profile4_node6 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,65] 6 480 profile4_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,65] 6 480 profile4_node6_cert).mp (by decide +kernel))

def profile4_node7_cert : CutBound 9 := { lost := (rows 0 384 0 0 0 0 0 0 0), upper := (rows 19 98 453 457 465 481 64 128 256), lower := (rows 19 98 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 1 34 4 8 16 32 511 0 511), good := (rows 339 354 324 328 336 354 320 320 320) },{ target := 8, region := (rows 1 34 4 8 16 32 511 511 0), good := (rows 211 226 196 200 208 226 192 192 192) }] }

theorem profile4_node7 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,96] 6 449 profile4_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,96] 6 449 profile4_node7_cert).mp (by decide +kernel))

def profile4_node8_cert : CutBound 9 := { lost := (rows 256 256 0 0 0 0 0 0 0), upper := (rows 19 194 485 489 497 481 64 128 256), lower := (rows 19 194 4 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 17 511 4 8 16 32 511 511 0), good := (rows 211 194 198 202 211 226 194 194 194) }] }

theorem profile4_node8 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,192] 6 481 profile4_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18,192] 6 481 profile4_node8_cert).mp (by decide +kernel))

def profile4_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile4_node1_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node1 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [18] 6 (by decide) (choices 2) [33,65,96,192] profile4_node1_route profile4_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile4_node2
  · exact profile4_node6
  · exact profile4_node7
  · exact profile4_node8

def profile4_node10_cert : CutBound 9 := { lost := (rows 0 384 0 0 0 0 0 0 0), upper := (rows 49 67 454 458 466 482 64 128 256), lower := (rows 49 67 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 371 323 324 328 336 352 320 320 320) },{ target := 8, region := (rows 1 3 4 8 16 32 511 511 0), good := (rows 243 195 196 200 208 224 192 192 192) }] }

theorem profile4_node10 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,65] 6 450 profile4_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,65] 6 450 profile4_node10_cert).mp (by decide +kernel))

def profile4_node12_cert : CutBound 9 := { lost := (rows 0 256 256 0 0 0 0 0 0), upper := (rows 49 194 7 456 464 480 64 128 256), lower := (rows 49 194 7 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 1 511 5 8 16 32 511 511 0), good := (rows 247 194 199 202 210 226 194 194 194) }] }

theorem profile4_node12 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,3] 6 448 profile4_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,3] 6 448 profile4_node12_cert).mp (by decide +kernel))

def profile4_node13_cert : CutBound 9 := { lost := (rows 64 0 0 64 0 0 0 0 0), upper := (rows 49 194 69 394 402 418 64 128 256), lower := (rows 49 194 69 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 18 34 0 511 511), good := (rows 433 443 389 392 400 416 384 384 384) }] }

theorem profile4_node13 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,65] 6 386 profile4_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,65] 6 386 profile4_node13_cert).mp (by decide +kernel))

def profile4_node14_cert : CutBound 9 := { lost := (rows 64 0 0 64 0 0 0 0 0), upper := (rows 49 194 70 393 401 417 64 128 256), lower := (rows 49 194 70 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 447 441 441 441 441 441 441) }] }

theorem profile4_node14 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,66] 6 385 profile4_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,66] 6 385 profile4_node14_cert).mp (by decide +kernel))

def profile4_node15_cert : CutBound 9 := { lost := (rows 64 0 0 64 0 0 0 0 0), upper := (rows 49 194 196 267 275 291 64 128 256), lower := (rows 49 194 196 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 18 34 0 511 511), good := (rows 433 443 388 392 400 416 384 384 384) }] }

theorem profile4_node15 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,192] 6 259 profile4_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,192] 6 259 profile4_node15_cert).mp (by decide +kernel))

def profile4_node16_cert : CutBound 9 := { lost := (rows 0 0 192 0 0 0 0 0 0), upper := (rows 49 194 261 458 466 482 64 128 256), lower := (rows 49 194 261 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 437 386 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 373 322 325 328 336 352 320 320 320) }] }

theorem profile4_node16 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,257] 6 450 profile4_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,257] 6 450 profile4_node16_cert).mp (by decide +kernel))

def profile4_node17_cert : CutBound 9 := { lost := (rows 0 0 192 0 0 0 0 0 0), upper := (rows 49 194 262 457 465 481 64 128 256), lower := (rows 49 194 262 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 8 16 32 0 511 511), good := (rows 433 390 390 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 6 8 16 32 511 0 511), good := (rows 369 326 326 328 336 352 320 320 320) }] }

theorem profile4_node17 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,258] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,258] 6 449 profile4_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,258] 6 449 profile4_node17_cert).mp (by decide +kernel))

def profile4_node18_cert : CutBound 9 := { lost := (rows 64 0 0 64 0 0 0 0 0), upper := (rows 49 194 324 395 403 419 64 128 256), lower := (rows 49 194 324 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 3 2 4 10 18 34 0 511 511), good := (rows 433 443 388 392 400 416 384 384 384) }] }

theorem profile4_node18 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,320] 6 387 profile4_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192,320] 6 387 profile4_node18_cert).mp (by decide +kernel))

def profile4_node11_column : Nat → Fin 9 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile4_node11_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node11 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48,192] 6 (by decide) (choices 2) [3,65,66,192,257,258,320] profile4_node11_route profile4_node11_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node12
  · exact profile4_node13
  · exact profile4_node14
  · exact profile4_node15
  · exact profile4_node16
  · exact profile4_node17
  · exact profile4_node18

def profile4_node9_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile4_node9_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node9 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [48] 6 (by decide) (choices 2) [65,192] profile4_node9_route profile4_node9_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile4_node10
  · exact profile4_node11

def profile4_node19_cert : CutBound 9 := { lost := (rows 384 0 0 0 0 0 0 0 0), upper := (rows 67 499 501 505 497 497 64 128 256), lower := (rows 67 2 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 16 32 511 0 511), good := (rows 323 323 324 328 336 352 320 320 320) },{ target := 8, region := (rows 3 2 4 8 16 32 511 511 0), good := (rows 195 195 196 200 208 224 192 192 192) }] }

theorem profile4_node19 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [66] 6 497 profile4_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [66] 6 497 profile4_node19_cert).mp (by decide +kernel))

def profile4_node20_cert : CutBound 9 := { lost := (rows 384 0 0 0 0 0 0 0 0), upper := (rows 81 483 487 491 499 483 64 128 256), lower := (rows 81 2 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 2 4 8 16 32 511 511 0), good := (rows 209 194 196 200 209 224 192 192 192) }] }

theorem profile4_node20 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [80] 6 483 profile4_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [80] 6 483 profile4_node20_cert).mp (by decide +kernel))

def profile4_node22_cert : CutBound 9 := { lost := (rows 256 256 0 0 0 0 0 0 0), upper := (rows 193 19 486 490 498 482 64 128 256), lower := (rows 193 19 4 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 511 18 4 8 16 32 511 511 0), good := (rows 193 211 197 201 211 225 193 193 193) }] }

theorem profile4_node22 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,17] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,17] 6 482 profile4_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,17] 6 482 profile4_node22_cert).mp (by decide +kernel))

def profile4_node24_cert : CutBound 9 := { lost := (rows 256 0 256 0 0 0 0 0 0), upper := (rows 193 50 7 456 464 480 64 128 256), lower := (rows 193 50 7 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 511 2 6 8 16 32 511 511 0), good := (rows 193 247 199 201 209 225 193 193 193) }] }

theorem profile4_node24 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,3] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,3] 6 448 profile4_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,3] 6 448 profile4_node24_cert).mp (by decide +kernel))

def profile4_node25_cert : CutBound 9 := { lost := (rows 0 64 0 64 0 0 0 0 0), upper := (rows 193 50 69 394 402 418 64 128 256), lower := (rows 193 50 69 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 447 442 442 442 442 442 442) }] }

theorem profile4_node25 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,65] 6 386 profile4_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,65] 6 386 profile4_node25_cert).mp (by decide +kernel))

def profile4_node26_cert : CutBound 9 := { lost := (rows 0 64 0 64 0 0 0 0 0), upper := (rows 193 50 70 393 401 417 64 128 256), lower := (rows 193 50 70 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 390 392 400 416 384 384 384) }] }

theorem profile4_node26 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,66] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,66] 6 385 profile4_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,66] 6 385 profile4_node26_cert).mp (by decide +kernel))

def profile4_node27_cert : CutBound 9 := { lost := (rows 0 64 0 64 0 0 0 0 0), upper := (rows 193 50 196 267 275 291 64 128 256), lower := (rows 193 50 196 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile4_node27 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,192] 6 259 profile4_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,192] 6 259 profile4_node27_cert).mp (by decide +kernel))

def profile4_node28_cert : CutBound 9 := { lost := (rows 0 0 192 0 0 0 0 0 0), upper := (rows 193 50 261 458 466 482 64 128 256), lower := (rows 193 50 261 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 5 8 16 32 0 511 511), good := (rows 389 434 389 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 5 8 16 32 511 0 511), good := (rows 325 370 325 328 336 352 320 320 320) }] }

theorem profile4_node28 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,257] 6 450 profile4_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,257] 6 450 profile4_node28_cert).mp (by decide +kernel))

def profile4_node29_cert : CutBound 9 := { lost := (rows 0 0 192 0 0 0 0 0 0), upper := (rows 193 50 262 457 465 481 64 128 256), lower := (rows 193 50 262 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 8 16 32 0 511 511), good := (rows 385 438 390 392 400 416 384 384 384) },{ target := 7, region := (rows 1 2 6 8 16 32 511 0 511), good := (rows 321 374 326 328 336 352 320 320 320) }] }

theorem profile4_node29 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,258] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,258] 6 449 profile4_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,258] 6 449 profile4_node29_cert).mp (by decide +kernel))

def profile4_node30_cert : CutBound 9 := { lost := (rows 0 64 0 64 0 0 0 0 0), upper := (rows 193 50 324 395 403 419 64 128 256), lower := (rows 193 50 324 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 9 17 33 0 511 511), good := (rows 443 434 388 392 400 416 384 384 384) }] }

theorem profile4_node30 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,320] 6 387 profile4_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48,320] 6 387 profile4_node30_cert).mp (by decide +kernel))

def profile4_node23_column : Nat → Fin 9 := fun mask => match mask with | 9 => 3 | 17 => 4 | 33 => 5 | 10 => 3 | 18 => 4 | 34 => 5 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile4_node23_route : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node23 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,48] 6 (by decide) (choices 2) [3,65,66,192,257,258,320] profile4_node23_route profile4_node23_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node24
  · exact profile4_node25
  · exact profile4_node26
  · exact profile4_node27
  · exact profile4_node28
  · exact profile4_node29
  · exact profile4_node30

def profile4_node31_cert : CutBound 9 := { lost := (rows 0 0 64 64 0 0 0 0 0), upper := (rows 193 67 438 442 434 434 64 128 256), lower := (rows 193 67 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 6 10 18 34 0 511 511), good := (rows 385 447 388 392 400 416 384 384 384) }] }

theorem profile4_node31 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,65] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,65] 6 434 profile4_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,65] 6 434 profile4_node31_cert).mp (by decide +kernel))

def profile4_node32_cert : CutBound 9 := { lost := (rows 256 384 0 0 0 0 0 0 0), upper := (rows 193 82 423 427 435 419 64 128 256), lower := (rows 193 82 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) },{ target := 8, region := (rows 511 18 4 8 16 32 511 511 0), good := (rows 193 211 197 201 211 225 193 193 193) }] }

theorem profile4_node32 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,80] 6 419 profile4_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,80] 6 419 profile4_node32_cert).mp (by decide +kernel))

def profile4_node33_cert : CutBound 9 := { lost := (rows 256 256 0 0 0 0 0 0 0), upper := (rows 193 194 311 315 307 307 64 128 256), lower := (rows 193 194 4 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 511 511 4 8 16 32 511 511 0), good := (rows 195 195 199 203 211 227 195 195 195) }] }

theorem profile4_node33 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,192] 6 307 profile4_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,192] 6 307 profile4_node33_cert).mp (by decide +kernel))

def profile4_node34_cert : CutBound 9 := { lost := (rows 0 192 0 0 0 0 0 0 0), upper := (rows 193 259 502 506 498 498 64 128 256), lower := (rows 193 259 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 3 4 8 16 32 0 511 511), good := (rows 387 387 388 392 400 416 384 384 384) },{ target := 7, region := (rows 1 3 4 8 16 32 511 0 511), good := (rows 323 323 324 328 336 352 320 320 320) }] }

theorem profile4_node34 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,257] 6 498 profile4_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,257] 6 498 profile4_node34_cert).mp (by decide +kernel))

def profile4_node35_cert : CutBound 9 := { lost := (rows 0 192 0 0 0 0 0 0 0), upper := (rows 193 274 487 491 499 483 64 128 256), lower := (rows 193 274 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 385 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) }] }

theorem profile4_node35 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,272] 6 483 profile4_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,272] 6 483 profile4_node35_cert).mp (by decide +kernel))

def profile4_node36_cert : CutBound 9 := { lost := (rows 256 128 0 0 0 0 0 0 0), upper := (rows 193 322 439 443 435 435 64 128 256), lower := (rows 193 322 4 8 16 32 64 128 256), losses := [{ target := 7, region := (rows 1 511 4 8 16 32 511 0 511), good := (rows 323 322 326 330 338 354 322 322 322) },{ target := 8, region := (rows 511 2 4 8 16 32 511 511 0), good := (rows 193 195 197 201 209 225 193 193 193) }] }

theorem profile4_node36 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,320] 6 435 profile4_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192,320] 6 435 profile4_node36_cert).mp (by decide +kernel))

def profile4_node21_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile4_node21_route : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node21 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [192] 6 (by decide) (choices 2) [17,48,65,80,192,257,272,320] profile4_node21_route profile4_node21_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile4_node22
  · exact profile4_node23
  · exact profile4_node31
  · exact profile4_node32
  · exact profile4_node33
  · exact profile4_node34
  · exact profile4_node35
  · exact profile4_node36

def profile4_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 2 | 10 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile4_node0_route : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile4_node0 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [] 6 (by decide) (choices 2) [18,48,66,80,192] profile4_node0_route profile4_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile4_node1
  · exact profile4_node9
  · exact profile4_node19
  · exact profile4_node20
  · exact profile4_node21

theorem profile4 : Upper (D (n:=9) [33,33,32,32,17,17,2,2,2]) (R (n:=9) [33,33,32,32,17,17,2,2,2]) [] 6 := profile4_node0


#print axioms profile4
end Delivery.SmallBudgetTenFinite9
