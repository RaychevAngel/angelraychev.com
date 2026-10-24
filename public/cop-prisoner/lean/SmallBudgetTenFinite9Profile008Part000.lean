import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile8_node2_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 25 11 484 488 496 480 480 128 256), lower := (rows 25 11 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 503 500 500 500 500 500 500 500) }] }

theorem profile8_node2 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,9] 6 480 profile8_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,9] 6 480 profile8_node2_cert).mp (by decide +kernel))

def profile8_node4_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 25 35 76 392 400 416 448 128 256), lower := (rows 25 35 76 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 3 4 0 511 511 511 511 511), good := (rows 499 499 500 496 496 496 496 496 496) }] }

theorem profile8_node4 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,72] 6 384 profile8_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,72] 6 384 profile8_node4_cert).mp (by decide +kernel))

def profile8_node5_cert : Bound 9 := { allowed := (rows 384 392 256 0 0 0 0 0 0), upper := (rows 25 35 140 456 464 480 448 128 256), lower := (rows 25 35 140 8 16 32 64 128 256), losses := [] }

theorem profile8_node5 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,136] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,136] 6 448 profile8_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,136] 6 448 profile8_node5_cert).mp (by decide +kernel))

def profile8_node6_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 25 35 196 392 408 424 456 128 256), lower := (rows 25 35 196 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 511 511), good := (rows 401 419 452 384 400 416 452 384 384) }] }

theorem profile8_node6 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,192] 6 392 profile8_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,192] 6 392 profile8_node6_cert).mp (by decide +kernel))

def profile8_node7_cert : Bound 9 := { allowed := (rows 384 392 8 0 0 0 0 0 0), upper := (rows 25 35 388 456 472 488 456 128 256), lower := (rows 25 35 388 8 16 32 64 128 256), losses := [] }

theorem profile8_node7 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,384] 6 456 profile8_node7_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33,384] 6 456 profile8_node7_cert).mp (by decide +kernel))

def profile8_node3_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile8_node3_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node3 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,33] 6 (by decide) (choices 2) [72,136,192,384] profile8_node3_route profile8_node3_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node4
  · exact profile8_node5
  · exact profile8_node6
  · exact profile8_node7

def profile8_node8_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 25 42 453 457 465 481 449 128 256), lower := (rows 25 42 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 5 0 17 33 65 511 511), good := (rows 501 418 388 384 400 416 448 384 384) }] }

theorem profile8_node8 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,40] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,40] 6 449 profile8_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,40] 6 449 profile8_node8_cert).mp (by decide +kernel))

def profile8_node10_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 25 98 13 392 400 416 448 128 256), lower := (rows 25 98 13 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 511 511 511 511 511), good := (rows 499 498 503 498 498 498 498 498 498) }] }

theorem profile8_node10 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,9] 6 384 profile8_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,9] 6 384 profile8_node10_cert).mp (by decide +kernel))

def profile8_node11_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 25 98 133 392 408 424 456 128 256), lower := (rows 25 98 133 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 511 511), good := (rows 405 482 389 384 400 416 448 384 384) }] }

theorem profile8_node11 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,129] 6 392 profile8_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,129] 6 392 profile8_node11_cert).mp (by decide +kernel))

def profile8_node12_cert : Bound 9 := { allowed := (rows 384 392 256 0 0 0 0 0 0), upper := (rows 25 98 140 393 401 417 449 128 256), lower := (rows 25 98 140 8 16 32 64 128 256), losses := [] }

theorem profile8_node12 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,136] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,136] 6 385 profile8_node12_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,136] 6 385 profile8_node12_cert).mp (by decide +kernel))

def profile8_node13_cert : Bound 9 := { allowed := (rows 384 392 8 0 0 0 0 0 0), upper := (rows 25 98 388 393 409 425 457 128 256), lower := (rows 25 98 388 8 16 32 64 128 256), losses := [] }

theorem profile8_node13 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,384] 6 393 profile8_node13_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96,384] 6 393 profile8_node13_cert).mp (by decide +kernel))

def profile8_node9_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 4 | 40 => 5 | 72 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile8_node9_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node9 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,96] 6 (by decide) (choices 2) [9,129,136,384] profile8_node9_route profile8_node9_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node10
  · exact profile8_node11
  · exact profile8_node12
  · exact profile8_node13

def profile8_node14_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 25 131 492 488 504 488 488 128 256), lower := (rows 25 131 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 511 511), good := (rows 403 387 388 384 400 416 448 384 384) }] }

theorem profile8_node14 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,129] 6 488 profile8_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,129] 6 488 profile8_node14_cert).mp (by decide +kernel))

def profile8_node15_cert : Bound 9 := { allowed := (rows 384 256 392 0 0 0 0 0 0), upper := (rows 25 138 485 489 497 481 481 128 256), lower := (rows 25 138 4 8 16 32 64 128 256), losses := [] }

theorem profile8_node15 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,136] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,136] 6 481 profile8_node15_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,136] 6 481 profile8_node15_cert).mp (by decide +kernel))

def profile8_node16_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 25 162 461 457 473 489 457 128 256), lower := (rows 25 162 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 511 511), good := (rows 401 418 388 384 400 418 448 384 384) }] }

theorem profile8_node16 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,160] 6 457 profile8_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,160] 6 457 profile8_node16_cert).mp (by decide +kernel))

def profile8_node17_cert : Bound 9 := { allowed := (rows 384 8 392 0 0 0 0 0 0), upper := (rows 25 386 493 489 505 489 489 128 256), lower := (rows 25 386 4 8 16 32 64 128 256), losses := [] }

theorem profile8_node17 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,384] 6 489 profile8_node17_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24,384] 6 489 profile8_node17_cert).mp (by decide +kernel))

def profile8_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile8_node1_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node1 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [24] 6 (by decide) (choices 2) [9,33,40,96,129,136,160,384] profile8_node1_route profile8_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node2
  · exact profile8_node3
  · exact profile8_node8
  · exact profile8_node9
  · exact profile8_node14
  · exact profile8_node15
  · exact profile8_node16
  · exact profile8_node17

def profile8_node20_cert : CutBound 9 := { lost := (rows 8 0 0 0 0 0 0 0 0), upper := (rows 49 11 76 392 400 416 448 128 256), lower := (rows 49 11 76 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 511 511 511 511 511), good := (rows 497 499 501 497 497 497 497 497 497) }] }

theorem profile8_node20 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,72] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,72] 6 384 profile8_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,72] 6 384 profile8_node20_cert).mp (by decide +kernel))

def profile8_node21_cert : Bound 9 := { allowed := (rows 392 384 256 0 0 0 0 0 0), upper := (rows 49 11 140 456 464 480 448 128 256), lower := (rows 49 11 140 8 16 32 64 128 256), losses := [] }

theorem profile8_node21 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,136] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,136] 6 448 profile8_node21_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,136] 6 448 profile8_node21_cert).mp (by decide +kernel))

def profile8_node22_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 49 11 196 392 408 424 456 128 256), lower := (rows 49 11 196 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 68 0 16 32 64 511 511), good := (rows 433 387 452 384 400 416 452 384 384) }] }

theorem profile8_node22 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,192] 6 392 profile8_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,192] 6 392 profile8_node22_cert).mp (by decide +kernel))

def profile8_node23_cert : Bound 9 := { allowed := (rows 392 384 8 0 0 0 0 0 0), upper := (rows 49 11 388 456 472 488 456 128 256), lower := (rows 49 11 388 8 16 32 64 128 256), losses := [] }

theorem profile8_node23 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,384] 6 456 profile8_node23_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9,384] 6 456 profile8_node23_cert).mp (by decide +kernel))

def profile8_node19_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile8_node19_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node19 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,9] 6 (by decide) (choices 2) [72,136,192,384] profile8_node19_route profile8_node19_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node20
  · exact profile8_node21
  · exact profile8_node22
  · exact profile8_node23

def profile8_node25_cert : CutBound 9 := { lost := (rows 0 0 256 0 0 0 0 0 0), upper := (rows 49 67 140 392 408 424 456 128 256), lower := (rows 49 67 140 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 1 2 12 8 16 32 64 511 0), good := (rows 177 195 140 140 144 160 192 128 128) }] }

theorem profile8_node25 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,136] 6 392 profile8_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,136] 6 392 profile8_node25_cert).mp (by decide +kernel))

def profile8_node26_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 49 67 388 392 408 424 456 128 256), lower := (rows 49 67 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 16 32 64 511 511), good := (rows 437 455 388 388 404 420 452 388 388) }] }

theorem profile8_node26 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,384] 6 392 profile8_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65,384] 6 392 profile8_node26_cert).mp (by decide +kernel))

def profile8_node24_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 4 | 40 => 5 | 72 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile8_node24_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node24 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,65] 6 (by decide) (choices 2) [136,384] profile8_node24_route profile8_node24_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile8_node25
  · exact profile8_node26

def profile8_node28_cert : CutBound 9 := { lost := (rows 8 0 0 0 0 0 0 0 0), upper := (rows 49 74 13 392 400 416 448 128 256), lower := (rows 49 74 13 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 511 511 511 511 511), good := (rows 497 499 501 497 497 497 497 497 497) }] }

theorem profile8_node28 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,9] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,9] 6 384 profile8_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,9] 6 384 profile8_node28_cert).mp (by decide +kernel))

def profile8_node29_cert : CutBound 9 := { lost := (rows 0 0 8 0 0 0 0 0 0), upper := (rows 49 74 133 392 408 424 456 128 256), lower := (rows 49 74 133 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 5 0 16 32 64 511 511), good := (rows 437 450 389 384 400 416 448 384 384) }] }

theorem profile8_node29 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,129] 6 392 profile8_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,129] 6 392 profile8_node29_cert).mp (by decide +kernel))

def profile8_node30_cert : Bound 9 := { allowed := (rows 392 384 256 0 0 0 0 0 0), upper := (rows 49 74 140 393 401 417 449 128 256), lower := (rows 49 74 140 8 16 32 64 128 256), losses := [] }

theorem profile8_node30 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,136] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,136] 6 385 profile8_node30_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,136] 6 385 profile8_node30_cert).mp (by decide +kernel))

def profile8_node31_cert : Bound 9 := { allowed := (rows 392 384 8 0 0 0 0 0 0), upper := (rows 49 74 388 393 409 425 457 128 256), lower := (rows 49 74 388 8 16 32 64 128 256), losses := [] }

theorem profile8_node31 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,384] 6 393 profile8_node31_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72,384] 6 393 profile8_node31_cert).mp (by decide +kernel))

def profile8_node27_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 17 => 4 | 33 => 5 | 65 => 6 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 4 | 40 => 5 | 72 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile8_node27_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node27 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,72] 6 (by decide) (choices 2) [9,129,136,384] profile8_node27_route profile8_node27_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile8_node28
  · exact profile8_node29
  · exact profile8_node30
  · exact profile8_node31

def profile8_node32_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 49 131 460 456 472 488 456 128 256), lower := (rows 49 131 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 3 4 0 16 32 64 511 511), good := (rows 435 387 388 384 400 416 448 384 384) }] }

theorem profile8_node32 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,129] 6 456 profile8_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,129] 6 456 profile8_node32_cert).mp (by decide +kernel))

def profile8_node33_cert : CutBound 9 := { lost := (rows 0 256 0 0 0 0 0 0 0), upper := (rows 49 138 461 457 473 489 457 128 256), lower := (rows 49 138 4 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 1 10 4 8 16 32 64 511 0), good := (rows 177 138 132 138 144 160 192 128 128) }] }

theorem profile8_node33 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,136] 6 457 profile8_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,136] 6 457 profile8_node33_cert).mp (by decide +kernel))

def profile8_node34_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 49 194 397 393 409 425 457 128 256), lower := (rows 49 194 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 511 511), good := (rows 433 450 388 384 400 416 450 384 384) }] }

theorem profile8_node34 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,192] 6 393 profile8_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,192] 6 393 profile8_node34_cert).mp (by decide +kernel))

def profile8_node35_cert : CutBound 9 := { lost := (rows 0 8 0 0 0 0 0 0 0), upper := (rows 49 386 461 457 473 489 457 128 256), lower := (rows 49 386 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 16 32 64 511 511), good := (rows 435 386 390 386 402 418 450 386 386) }] }

theorem profile8_node35 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,384] 6 457 profile8_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48,384] 6 457 profile8_node35_cert).mp (by decide +kernel))

def profile8_node18_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 4 | 40 => 5 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile8_node18_route : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node18 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [48] 6 (by decide) (choices 2) [9,65,72,129,136,192,384] profile8_node18_route profile8_node18_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile8_node19
  · exact profile8_node24
  · exact profile8_node27
  · exact profile8_node32
  · exact profile8_node33
  · exact profile8_node34
  · exact profile8_node35

def profile8_node36_cert : CutBound 9 := { lost := (rows 256 0 0 0 0 0 0 0 0), upper := (rows 137 507 509 505 505 505 505 128 256), lower := (rows 137 2 4 8 16 32 64 128 256), losses := [{ target := 8, region := (rows 9 2 4 8 16 32 64 511 0), good := (rows 137 130 132 137 144 160 192 128 128) }] }

theorem profile8_node36 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [136] 6 505 profile8_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [136] 6 505 profile8_node36_cert).mp (by decide +kernel))

def profile8_node37_cert : CutBound 9 := { lost := (rows 8 0 0 0 0 0 0 0 0), upper := (rows 145 491 493 489 505 489 489 128 256), lower := (rows 145 2 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 17 2 4 0 16 32 64 511 511), good := (rows 401 386 388 384 401 416 448 384 384) }] }

theorem profile8_node37 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [144] 6 489 profile8_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [144] 6 489 profile8_node37_cert).mp (by decide +kernel))

def profile8_node38_cert : CutBound 9 := { lost := (rows 8 0 0 0 0 0 0 0 0), upper := (rows 385 507 509 505 505 505 505 128 256), lower := (rows 385 2 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 16 32 64 511 511), good := (rows 385 387 389 385 401 417 449 385 385) }] }

theorem profile8_node38 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [384] 6 505 profile8_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [384] 6 505 profile8_node38_cert).mp (by decide +kernel))

def profile8_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0

def profile8_node0_route : Route 9 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | 7 => 8 | 8 => 7 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 320 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile8_node0 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [] 6 (by decide) (choices 2) [24,48,136,144,384] profile8_node0_route profile8_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile8_node1
  · exact profile8_node18
  · exact profile8_node36
  · exact profile8_node37
  · exact profile8_node38

theorem profile8 : Upper (D (n:=9) [33,32,32,18,17,17,17,2,2]) (R (n:=9) [33,32,32,18,17,17,17,2,2]) [] 6 := profile8_node0


#print axioms profile8
end Delivery.SmallBudgetTenFinite9
