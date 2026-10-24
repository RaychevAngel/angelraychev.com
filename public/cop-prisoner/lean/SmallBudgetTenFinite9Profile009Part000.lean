import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile9_node2_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 25 26 484 488 496 480 480 128 256), lower := (rows 25 26 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) }] }

theorem profile9_node2 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,24] 6 480 profile9_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,24] 6 480 profile9_node2_cert).mp (by decide +kernel))

def profile9_node4_cert : CutBound 9 := { lost := (rows 0 16 8 0 0 0 0 0 0), upper := (rows 25 42 84 392 400 416 448 128 256), lower := (rows 25 42 84 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 494 490 490 490 490 490 490) }] }

theorem profile9_node4 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,80] 6 384 profile9_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,80] 6 384 profile9_node4_cert).mp (by decide +kernel))

def profile9_node5_cert : Bound 9 := { allowed := (rows 384 400 256 0 0 0 0 0 0), upper := (rows 25 42 148 456 464 480 448 128 256), lower := (rows 25 42 148 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) }] }

theorem profile9_node5 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,144] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,144] 6 448 profile9_node5_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,144] 6 448 profile9_node5_cert).mp (by decide +kernel))

def profile9_node6_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 25 42 196 408 400 432 464 128 256), lower := (rows 25 42 196 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 2 68 8 0 32 64 511 511), good := (rows 393 426 452 392 384 416 452 384 384) }] }

theorem profile9_node6 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,192] 6 400 profile9_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,192] 6 400 profile9_node6_cert).mp (by decide +kernel))

def profile9_node7_cert : Bound 9 := { allowed := (rows 384 400 16 0 0 0 0 0 0), upper := (rows 25 42 388 472 464 496 464 128 256), lower := (rows 25 42 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) }] }

theorem profile9_node7 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,384] 6 464 profile9_node7_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40,384] 6 464 profile9_node7_cert).mp (by decide +kernel))

def profile9_node3_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile9_node3_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node3 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,40] 6 (by decide) (choices 2) [80,144,192,384] profile9_node3_route profile9_node3_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node4
  · exact profile9_node5
  · exact profile9_node6
  · exact profile9_node7

def profile9_node9_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 25 98 28 392 400 416 448 128 256), lower := (rows 25 98 28 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 511 511 511 511 511), good := (rows 499 498 502 498 498 498 498 498 498) },{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 494 490 490 490 490 490 490) }] }

theorem profile9_node9 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,24] 6 384 profile9_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,24] 6 384 profile9_node9_cert).mp (by decide +kernel))

def profile9_node10_cert : CutBound 9 := { lost := (rows 0 8 16 0 0 0 0 0 0), upper := (rows 25 98 140 408 400 432 464 128 256), lower := (rows 25 98 140 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 511 511 511 511 511), good := (rows 499 498 502 498 498 498 498 498 498) },{ target := 4, region := (rows 1 2 13 8 0 32 64 511 511), good := (rows 397 482 396 396 384 416 448 384 384) }] }

theorem profile9_node10 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,136] 6 400 profile9_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,136] 6 400 profile9_node10_cert).mp (by decide +kernel))

def profile9_node11_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 25 98 388 408 408 440 472 128 256), lower := (rows 25 98 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 16 32 64 511 511), good := (rows 405 486 388 388 404 420 452 388 388) },{ target := 4, region := (rows 1 2 511 8 0 32 64 511 511), good := (rows 397 486 388 396 388 420 452 388 388) }] }

theorem profile9_node11 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,384] 6 408 profile9_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96,384] 6 408 profile9_node11_cert).mp (by decide +kernel))

def profile9_node8_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile9_node8_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node8 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,96] 6 (by decide) (choices 2) [24,136,384] profile9_node8_route profile9_node8_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node9
  · exact profile9_node10
  · exact profile9_node11

def profile9_node12_cert : CutBound 9 := { lost := (rows 0 16 8 0 0 0 0 0 0), upper := (rows 25 138 500 504 496 496 496 128 256), lower := (rows 25 138 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 11 4 8 0 32 64 511 511), good := (rows 395 394 388 394 384 416 448 384 384) }] }

theorem profile9_node12 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,136] 6 496 profile9_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,136] 6 496 profile9_node12_cert).mp (by decide +kernel))

def profile9_node13_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 25 162 476 472 472 504 472 128 256), lower := (rows 25 162 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 34 4 0 16 32 64 511 511), good := (rows 401 418 388 384 400 418 448 384 384) },{ target := 4, region := (rows 1 34 4 8 0 32 64 511 511), good := (rows 393 418 388 392 384 418 448 384 384) }] }

theorem profile9_node13 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,160] 6 472 profile9_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,160] 6 472 profile9_node13_cert).mp (by decide +kernel))

def profile9_node14_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 25 386 508 504 504 504 504 128 256), lower := (rows 25 386 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 16 32 64 511 511), good := (rows 403 386 390 386 402 418 450 386 386) },{ target := 4, region := (rows 1 511 4 8 0 32 64 511 511), good := (rows 395 386 390 394 386 418 450 386 386) }] }

theorem profile9_node14 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,384] 6 504 profile9_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24,384] 6 504 profile9_node14_cert).mp (by decide +kernel))

def profile9_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0

def profile9_node1_route : Route 9 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node1 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [24] 6 (by decide) (choices 2) [24,40,96,136,160,384] profile9_node1_route profile9_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node2
  · exact profile9_node3
  · exact profile9_node8
  · exact profile9_node12
  · exact profile9_node13
  · exact profile9_node14

def profile9_node17_cert : CutBound 9 := { lost := (rows 16 0 8 0 0 0 0 0 0), upper := (rows 41 26 84 392 400 416 448 128 256), lower := (rows 41 26 84 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) }] }

theorem profile9_node17 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,80] 6 384 profile9_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,80] 6 384 profile9_node17_cert).mp (by decide +kernel))

def profile9_node18_cert : Bound 9 := { allowed := (rows 400 384 256 0 0 0 0 0 0), upper := (rows 41 26 148 456 464 480 448 128 256), lower := (rows 41 26 148 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) }] }

theorem profile9_node18 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,144] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,144] 6 448 profile9_node18_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,144] 6 448 profile9_node18_cert).mp (by decide +kernel))

def profile9_node19_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 41 26 196 408 400 432 464 128 256), lower := (rows 41 26 196 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 2 68 8 0 32 64 511 511), good := (rows 425 394 452 392 384 416 452 384 384) }] }

theorem profile9_node19 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,192] 6 400 profile9_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,192] 6 400 profile9_node19_cert).mp (by decide +kernel))

def profile9_node20_cert : Bound 9 := { allowed := (rows 400 384 16 0 0 0 0 0 0), upper := (rows 41 26 388 472 464 496 464 128 256), lower := (rows 41 26 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) }] }

theorem profile9_node20 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,384] 6 :=
  DegreeLoss.bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,384] 6 464 profile9_node20_cert
    ((DegreeLoss.boundCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24,384] 6 464 profile9_node20_cert).mp (by decide +kernel))

def profile9_node16_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile9_node16_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node16 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,24] 6 (by decide) (choices 2) [80,144,192,384] profile9_node16_route profile9_node16_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node17
  · exact profile9_node18
  · exact profile9_node19
  · exact profile9_node20

def profile9_node22_cert : CutBound 9 := { lost := (rows 0 0 264 0 0 0 0 0 0), upper := (rows 41 74 148 408 400 432 464 128 256), lower := (rows 41 74 148 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 8, region := (rows 1 2 20 8 16 32 64 511 0), good := (rows 169 202 148 136 148 160 192 128 128) }] }

theorem profile9_node22 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,144] 6 400 profile9_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,144] 6 400 profile9_node22_cert).mp (by decide +kernel))

def profile9_node23_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 41 74 388 408 400 432 464 128 256), lower := (rows 41 74 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 2 511 8 0 32 64 511 511), good := (rows 429 462 388 396 388 420 452 388 388) }] }

theorem profile9_node23 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,384] 6 400 profile9_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72,384] 6 400 profile9_node23_cert).mp (by decide +kernel))

def profile9_node21_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile9_node21_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node21 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,72] 6 (by decide) (choices 2) [144,384] profile9_node21_route profile9_node21_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile9_node22
  · exact profile9_node23

def profile9_node25_cert : CutBound 9 := { lost := (rows 16 8 0 0 0 0 0 0 0), upper := (rows 41 82 28 392 400 416 448 128 256), lower := (rows 41 82 28 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 511 511 511 511 511), good := (rows 499 498 502 498 498 498 498 498 498) },{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) }] }

theorem profile9_node25 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,24] 6 384 profile9_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,24] 6 384 profile9_node25_cert).mp (by decide +kernel))

def profile9_node26_cert : CutBound 9 := { lost := (rows 0 8 16 0 0 0 0 0 0), upper := (rows 41 82 140 408 400 432 464 128 256), lower := (rows 41 82 140 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 511 511 511 511 511), good := (rows 499 498 502 498 498 498 498 498 498) },{ target := 4, region := (rows 1 2 13 8 0 32 64 511 511), good := (rows 429 450 396 396 384 416 448 384 384) }] }

theorem profile9_node26 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,136] 6 400 profile9_node26_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,136] 6 400 profile9_node26_cert).mp (by decide +kernel))

def profile9_node27_cert : CutBound 9 := { lost := (rows 16 0 8 0 0 0 0 0 0), upper := (rows 41 82 148 392 408 424 456 128 256), lower := (rows 41 82 148 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 22 0 16 32 64 511 511), good := (rows 417 470 404 384 404 416 448 384 384) },{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) }] }

theorem profile9_node27 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,144] 6 392 profile9_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,144] 6 392 profile9_node27_cert).mp (by decide +kernel))

def profile9_node28_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 41 82 388 408 408 440 472 128 256), lower := (rows 41 82 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 16 32 64 511 511), good := (rows 421 470 388 388 404 420 452 388 388) },{ target := 4, region := (rows 1 2 511 8 0 32 64 511 511), good := (rows 429 454 388 396 388 420 452 388 388) }] }

theorem profile9_node28 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,384] 6 408 profile9_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80,384] 6 408 profile9_node28_cert).mp (by decide +kernel))

def profile9_node24_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile9_node24_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node24 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,80] 6 (by decide) (choices 2) [24,136,144,384] profile9_node24_route profile9_node24_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile9_node25
  · exact profile9_node26
  · exact profile9_node27
  · exact profile9_node28

def profile9_node29_cert : CutBound 9 := { lost := (rows 0 16 8 0 0 0 0 0 0), upper := (rows 41 138 468 472 464 496 464 128 256), lower := (rows 41 138 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 511 511 511 511 511), good := (rows 501 502 500 500 500 500 500 500 500) },{ target := 4, region := (rows 1 11 4 8 0 32 64 511 511), good := (rows 427 394 388 394 384 416 448 384 384) }] }

theorem profile9_node29 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,136] 6 464 profile9_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,136] 6 464 profile9_node29_cert).mp (by decide +kernel))

def profile9_node30_cert : CutBound 9 := { lost := (rows 0 264 0 0 0 0 0 0 0), upper := (rows 41 146 476 472 472 504 472 128 256), lower := (rows 41 146 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 18 4 0 16 32 64 511 511), good := (rows 417 402 388 384 402 416 448 384 384) },{ target := 8, region := (rows 1 18 4 8 16 32 64 511 0), good := (rows 169 146 132 136 146 160 192 128 128) }] }

theorem profile9_node30 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,144] 6 472 profile9_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,144] 6 472 profile9_node30_cert).mp (by decide +kernel))

def profile9_node31_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 41 194 412 408 408 440 472 128 256), lower := (rows 41 194 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 66 4 0 16 32 64 511 511), good := (rows 417 450 388 384 400 416 450 384 384) },{ target := 4, region := (rows 1 66 4 8 0 32 64 511 511), good := (rows 425 450 388 392 384 416 450 384 384) }] }

theorem profile9_node31 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,192] 6 408 profile9_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,192] 6 408 profile9_node31_cert).mp (by decide +kernel))

def profile9_node32_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 41 386 476 472 472 504 472 128 256), lower := (rows 41 386 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 16 32 64 511 511), good := (rows 419 386 390 386 402 418 450 386 386) },{ target := 4, region := (rows 1 511 4 8 0 32 64 511 511), good := (rows 427 386 390 394 386 418 450 386 386) }] }

theorem profile9_node32 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,384] 6 472 profile9_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40,384] 6 472 profile9_node32_cert).mp (by decide +kernel))

def profile9_node15_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile9_node15_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node15 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [40] 6 (by decide) (choices 2) [24,72,80,136,144,192,384] profile9_node15_route profile9_node15_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node16
  · exact profile9_node21
  · exact profile9_node24
  · exact profile9_node29
  · exact profile9_node30
  · exact profile9_node31
  · exact profile9_node32

def profile9_node35_cert : CutBound 9 := { lost := (rows 24 0 0 0 0 0 0 0 0), upper := (rows 97 26 28 392 400 416 448 128 256), lower := (rows 97 26 28 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 511 511 511 511 511), good := (rows 497 499 501 497 497 497 497 497 497) },{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) }] }

theorem profile9_node35 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,24] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,24] 6 384 profile9_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,24] 6 384 profile9_node35_cert).mp (by decide +kernel))

def profile9_node36_cert : CutBound 9 := { lost := (rows 8 0 16 0 0 0 0 0 0), upper := (rows 97 26 140 408 400 432 464 128 256), lower := (rows 97 26 140 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 511 511 511 511 511), good := (rows 497 499 501 497 497 497 497 497 497) },{ target := 4, region := (rows 1 2 14 8 0 32 64 511 511), good := (rows 481 398 396 396 384 416 448 384 384) }] }

theorem profile9_node36 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,136] 6 400 profile9_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,136] 6 400 profile9_node36_cert).mp (by decide +kernel))

def profile9_node37_cert : CutBound 9 := { lost := (rows 0 0 24 0 0 0 0 0 0), upper := (rows 97 26 388 408 408 440 472 128 256), lower := (rows 97 26 388 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 2 511 0 16 32 64 511 511), good := (rows 485 406 388 388 404 420 452 388 388) },{ target := 4, region := (rows 1 2 511 8 0 32 64 511 511), good := (rows 485 398 388 396 388 420 452 388 388) }] }

theorem profile9_node37 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,384] 6 408 profile9_node37_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24,384] 6 408 profile9_node37_cert).mp (by decide +kernel))

def profile9_node34_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile9_node34_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node34 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,24] 6 (by decide) (choices 2) [24,136,384] profile9_node34_route profile9_node34_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node35
  · exact profile9_node36
  · exact profile9_node37

def profile9_node38_cert : CutBound 9 := { lost := (rows 0 272 0 0 0 0 0 0 0), upper := (rows 97 138 412 408 408 440 472 128 256), lower := (rows 97 138 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 64 511 511), good := (rows 481 394 388 394 384 416 448 384 384) },{ target := 8, region := (rows 1 10 4 8 16 32 64 511 0), good := (rows 225 138 132 138 144 160 192 128 128) }] }

theorem profile9_node38 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,136] 6 408 profile9_node38_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,136] 6 408 profile9_node38_cert).mp (by decide +kernel))

def profile9_node39_cert : CutBound 9 := { lost := (rows 0 24 0 0 0 0 0 0 0), upper := (rows 97 386 412 408 408 440 472 128 256), lower := (rows 97 386 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 1 511 4 0 16 32 64 511 511), good := (rows 483 386 390 386 402 418 450 386 386) },{ target := 4, region := (rows 1 511 4 8 0 32 64 511 511), good := (rows 483 386 390 394 386 418 450 386 386) }] }

theorem profile9_node39 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,384] 6 408 profile9_node39_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96,384] 6 408 profile9_node39_cert).mp (by decide +kernel))

def profile9_node33_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0

def profile9_node33_route : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node33 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [96] 6 (by decide) (choices 2) [24,136,384] profile9_node33_route profile9_node33_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile9_node34
  · exact profile9_node38
  · exact profile9_node39

def profile9_node40_cert : CutBound 9 := { lost := (rows 272 0 0 0 0 0 0 0 0), upper := (rows 137 506 508 504 504 504 504 128 256), lower := (rows 137 2 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 9 2 4 8 0 32 64 511 511), good := (rows 393 386 388 393 384 416 448 384 384) },{ target := 8, region := (rows 9 2 4 8 16 32 64 511 0), good := (rows 137 130 132 137 144 160 192 128 128) }] }

theorem profile9_node40 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [136] 6 504 profile9_node40_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [136] 6 504 profile9_node40_cert).mp (by decide +kernel))

def profile9_node41_cert : CutBound 9 := { lost := (rows 24 0 0 0 0 0 0 0 0), upper := (rows 161 474 476 472 472 504 472 128 256), lower := (rows 161 2 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 33 2 4 0 16 32 64 511 511), good := (rows 417 386 388 384 400 417 448 384 384) },{ target := 4, region := (rows 33 2 4 8 0 32 64 511 511), good := (rows 417 386 388 392 384 417 448 384 384) }] }

theorem profile9_node41 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [160] 6 472 profile9_node41_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [160] 6 472 profile9_node41_cert).mp (by decide +kernel))

def profile9_node42_cert : CutBound 9 := { lost := (rows 24 0 0 0 0 0 0 0 0), upper := (rows 385 506 508 504 504 504 504 128 256), lower := (rows 385 2 4 8 16 32 64 128 256), losses := [{ target := 3, region := (rows 511 2 4 0 16 32 64 511 511), good := (rows 385 387 389 385 401 417 449 385 385) },{ target := 4, region := (rows 511 2 4 8 0 32 64 511 511), good := (rows 385 387 389 393 385 417 449 385 385) }] }

theorem profile9_node42 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [384] 6 504 profile9_node42_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [384] 6 504 profile9_node42_cert).mp (by decide +kernel))

def profile9_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0

def profile9_node0_route : Route 9 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile9_node0 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [] 6 (by decide) (choices 2) [24,40,96,136,160,384] profile9_node0_route profile9_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile9_node1
  · exact profile9_node15
  · exact profile9_node33
  · exact profile9_node40
  · exact profile9_node41
  · exact profile9_node42

theorem profile9 : Upper (D (n:=9) [32,32,32,18,18,17,17,2,2]) (R (n:=9) [32,32,32,18,18,17,17,2,2]) [] 6 := profile9_node0


#print axioms profile9
end Delivery.SmallBudgetTenFinite9
