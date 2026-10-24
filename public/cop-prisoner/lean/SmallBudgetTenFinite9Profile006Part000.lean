import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile6_node3_cert : CutBound 9 := { lost := (rows 64 0 0 80 0 0 0 0 0), upper := (rows 49 82 84 392 400 416 64 128 256), lower := (rows 49 82 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 511 0 511 511 511 511), good := (rows 489 490 492 488 488 488 488 488 488) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile6_node3 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,80] 6 384 profile6_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,80] 6 384 profile6_node3_cert).mp (by decide +kernel))

def profile6_node4_cert : CutBound 9 := { lost := (rows 0 128 64 16 0 0 0 0 0), upper := (rows 49 82 148 456 464 480 64 128 256), lower := (rows 49 82 148 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 511 0 511 511 511 511), good := (rows 489 490 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 2 23 8 16 32 0 511 511), good := (rows 437 406 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 23 4 8 16 32 511 0 511), good := (rows 371 338 342 328 338 352 320 320 320) }] }

theorem profile6_node4 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,144] 6 448 profile6_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,144] 6 448 profile6_node4_cert).mp (by decide +kernel))

def profile6_node5_cert : CutBound 9 := { lost := (rows 64 0 16 64 0 0 0 0 0), upper := (rows 49 82 196 408 400 432 64 128 256), lower := (rows 49 82 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 485 454 452 460 452 484 452 452 452) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile6_node5 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,192] 6 400 profile6_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,192] 6 400 profile6_node5_cert).mp (by decide +kernel))

def profile6_node6_cert : CutBound 9 := { lost := (rows 0 128 80 0 0 0 0 0 0), upper := (rows 49 82 388 472 464 496 64 128 256), lower := (rows 49 82 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 485 454 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 437 406 388 396 404 420 388 388 388) },{ target := 7, region := (rows 1 19 4 8 16 32 511 0 511), good := (rows 371 338 324 328 338 352 320 320 320) }] }

theorem profile6_node6 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,384] 6 464 profile6_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80,384] 6 464 profile6_node6_cert).mp (by decide +kernel))

def profile6_node2_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile6_node2_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile6_node2 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,80] 6 (by decide) (choices 2) [80,144,192,384] profile6_node2_route profile6_node2_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node3
  · exact profile6_node4
  · exact profile6_node5
  · exact profile6_node6

def profile6_node8_cert : CutBound 9 := { lost := (rows 64 16 0 64 0 0 0 0 0), upper := (rows 49 194 84 408 400 432 64 128 256), lower := (rows 49 194 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 483 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile6_node8 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,80] 6 400 profile6_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,80] 6 400 profile6_node8_cert).mp (by decide +kernel))

def profile6_node9_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 194 196 280 272 304 64 128 256), lower := (rows 49 194 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile6_node9 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,192] 6 272 profile6_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,192] 6 272 profile6_node9_cert).mp (by decide +kernel))

def profile6_node10_cert : CutBound 9 := { lost := (rows 0 16 192 0 0 0 0 0 0), upper := (rows 49 194 276 472 464 496 64 128 256), lower := (rows 49 194 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 483 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 2 21 8 16 32 0 511 511), good := (rows 437 386 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 21 8 16 32 511 0 511), good := (rows 373 322 340 328 340 352 320 320 320) }] }

theorem profile6_node10 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,272] 6 464 profile6_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,272] 6 464 profile6_node10_cert).mp (by decide +kernel))

def profile6_node11_cert : CutBound 9 := { lost := (rows 64 16 16 64 0 0 0 0 0), upper := (rows 49 194 324 408 400 432 64 128 256), lower := (rows 49 194 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile6_node11 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,320] 6 400 profile6_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192,320] 6 400 profile6_node11_cert).mp (by decide +kernel))

def profile6_node7_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile6_node7_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node7 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48,192] 6 (by decide) (choices 2) [80,192,272,320] profile6_node7_route profile6_node7_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node8
  · exact profile6_node9
  · exact profile6_node10
  · exact profile6_node11

def profile6_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile6_node1_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node1 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [48] 6 (by decide) (choices 2) [80,192] profile6_node1_route profile6_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile6_node2
  · exact profile6_node7

def profile6_node14_cert : CutBound 9 := { lost := (rows 0 64 0 80 0 0 0 0 0), upper := (rows 81 50 84 392 400 416 64 128 256), lower := (rows 81 50 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 511 0 511 511 511 511), good := (rows 489 490 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile6_node14 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,80] 6 384 profile6_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,80] 6 384 profile6_node14_cert).mp (by decide +kernel))

def profile6_node15_cert : CutBound 9 := { lost := (rows 128 0 64 16 0 0 0 0 0), upper := (rows 81 50 148 456 464 480 64 128 256), lower := (rows 81 50 148 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 4 511 0 511 511 511 511), good := (rows 489 490 492 488 488 488 488 488 488) },{ target := 6, region := (rows 1 2 23 8 16 32 0 511 511), good := (rows 405 438 404 392 404 416 384 384 384) },{ target := 7, region := (rows 23 2 4 8 16 32 511 0 511), good := (rows 337 371 341 328 337 352 320 320 320) }] }

theorem profile6_node15 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,144] 6 448 profile6_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,144] 6 448 profile6_node15_cert).mp (by decide +kernel))

def profile6_node16_cert : CutBound 9 := { lost := (rows 0 64 16 64 0 0 0 0 0), upper := (rows 81 50 196 408 400 432 64 128 256), lower := (rows 81 50 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 453 486 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile6_node16 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,192] 6 400 profile6_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,192] 6 400 profile6_node16_cert).mp (by decide +kernel))

def profile6_node17_cert : CutBound 9 := { lost := (rows 128 0 80 0 0 0 0 0 0), upper := (rows 81 50 388 472 464 496 64 128 256), lower := (rows 81 50 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 8 0 32 511 511 511), good := (rows 453 486 452 460 452 484 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 405 438 388 396 404 420 388 388 388) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 371 324 328 337 352 320 320 320) }] }

theorem profile6_node17 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,384] 6 464 profile6_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48,384] 6 464 profile6_node17_cert).mp (by decide +kernel))

def profile6_node13_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile6_node13_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile6_node13 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,48] 6 (by decide) (choices 2) [80,144,192,384] profile6_node13_route profile6_node13_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node14
  · exact profile6_node15
  · exact profile6_node16
  · exact profile6_node17

def profile6_node18_cert : CutBound 9 := { lost := (rows 128 128 64 64 0 0 0 0 0), upper := (rows 81 82 436 440 432 432 64 128 256), lower := (rows 81 82 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) },{ target := 7, region := (rows 19 19 4 8 16 32 511 0 511), good := (rows 339 339 324 328 339 352 320 320 320) }] }

theorem profile6_node18 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,80] 6 432 profile6_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,80] 6 432 profile6_node18_cert).mp (by decide +kernel))

def profile6_node19_cert : CutBound 9 := { lost := (rows 0 16 64 64 0 0 0 0 0), upper := (rows 81 98 404 408 400 432 64 128 256), lower := (rows 81 98 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node19 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,96] 6 400 profile6_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,96] 6 400 profile6_node19_cert).mp (by decide +kernel))

def profile6_node20_cert : CutBound 9 := { lost := (rows 384 320 0 0 0 0 0 0 0), upper := (rows 81 146 500 504 496 496 64 128 256), lower := (rows 81 146 4 8 16 32 64 128 256), losses := [{ target := 6, region := (rows 1 19 4 8 16 32 0 511 511), good := (rows 403 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 339 324 328 337 352 320 320 320) },{ target := 8, region := (rows 19 19 4 8 16 32 511 511 0), good := (rows 211 211 196 200 211 224 192 192 192) }] }

theorem profile6_node20 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,144] 6 496 profile6_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,144] 6 496 profile6_node20_cert).mp (by decide +kernel))

def profile6_node21_cert : CutBound 9 := { lost := (rows 128 80 0 0 0 0 0 0 0), upper := (rows 81 162 468 472 464 496 64 128 256), lower := (rows 81 162 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 401 418 388 392 400 418 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 352 320 320 320) }] }

theorem profile6_node21 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,160] 6 464 profile6_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,160] 6 464 profile6_node21_cert).mp (by decide +kernel))

def profile6_node22_cert : CutBound 9 := { lost := (rows 0 16 64 64 0 0 0 0 0), upper := (rows 81 194 436 440 432 432 64 128 256), lower := (rows 81 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node22 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,192] 6 432 profile6_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,192] 6 432 profile6_node22_cert).mp (by decide +kernel))

def profile6_node23_cert : CutBound 9 := { lost := (rows 128 80 0 0 0 0 0 0 0), upper := (rows 81 386 500 504 496 496 64 128 256), lower := (rows 81 386 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 32 0 511 511), good := (rows 403 386 390 394 402 418 386 386 386) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) }] }

theorem profile6_node23 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,384] 6 496 profile6_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80,384] 6 496 profile6_node23_cert).mp (by decide +kernel))

def profile6_node12_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile6_node12_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile6_node12 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [80] 6 (by decide) (choices 2) [48,80,96,144,160,192,384] profile6_node12_route profile6_node12_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node13
  · exact profile6_node18
  · exact profile6_node19
  · exact profile6_node20
  · exact profile6_node21
  · exact profile6_node22
  · exact profile6_node23

def profile6_node24_cert : CutBound 9 := { lost := (rows 400 0 0 0 0 0 0 0 0), upper := (rows 97 466 468 472 464 496 64 128 256), lower := (rows 97 2 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 33 2 4 8 0 32 511 511 511), good := (rows 481 450 452 456 448 481 448 448 448) },{ target := 7, region := (rows 33 2 4 8 16 32 511 0 511), good := (rows 353 322 324 328 336 353 320 320 320) },{ target := 8, region := (rows 33 2 4 8 16 32 511 511 0), good := (rows 225 194 196 200 208 225 192 192 192) }] }

theorem profile6_node24 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [96] 6 464 profile6_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [96] 6 464 profile6_node24_cert).mp (by decide +kernel))

def profile6_node27_cert : CutBound 9 := { lost := (rows 16 64 0 64 0 0 0 0 0), upper := (rows 193 50 84 408 400 432 64 128 256), lower := (rows 193 50 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile6_node27 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,80] 6 400 profile6_node27_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,80] 6 400 profile6_node27_cert).mp (by decide +kernel))

def profile6_node28_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 50 196 280 272 304 64 128 256), lower := (rows 193 50 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile6_node28 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,192] 6 272 profile6_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,192] 6 272 profile6_node28_cert).mp (by decide +kernel))

def profile6_node29_cert : CutBound 9 := { lost := (rows 16 0 192 0 0 0 0 0 0), upper := (rows 193 50 276 472 464 496 64 128 256), lower := (rows 193 50 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 2 22 8 16 32 0 511 511), good := (rows 385 438 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 22 8 16 32 511 0 511), good := (rows 321 374 340 328 340 352 320 320 320) }] }

theorem profile6_node29 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,272] 6 464 profile6_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,272] 6 464 profile6_node29_cert).mp (by decide +kernel))

def profile6_node30_cert : CutBound 9 := { lost := (rows 16 64 16 64 0 0 0 0 0), upper := (rows 193 50 324 408 400 432 64 128 256), lower := (rows 193 50 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile6_node30 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,320] 6 400 profile6_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48,320] 6 400 profile6_node30_cert).mp (by decide +kernel))

def profile6_node26_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0

def profile6_node26_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node26 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,48] 6 (by decide) (choices 2) [80,192,272,320] profile6_node26_route profile6_node26_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node27
  · exact profile6_node28
  · exact profile6_node29
  · exact profile6_node30

def profile6_node31_cert : CutBound 9 := { lost := (rows 16 0 64 64 0 0 0 0 0), upper := (rows 193 82 436 440 432 432 64 128 256), lower := (rows 193 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node31 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,80] 6 432 profile6_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,80] 6 432 profile6_node31_cert).mp (by decide +kernel))

def profile6_node32_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 98 404 408 400 432 64 128 256), lower := (rows 193 98 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 34 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 483 449 449 449) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node32 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,96] 6 400 profile6_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,96] 6 400 profile6_node32_cert).mp (by decide +kernel))

def profile6_node33_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 194 308 312 304 304 64 128 256), lower := (rows 193 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node33 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,192] 6 304 profile6_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,192] 6 304 profile6_node33_cert).mp (by decide +kernel))

def profile6_node34_cert : CutBound 9 := { lost := (rows 16 192 0 0 0 0 0 0 0), upper := (rows 193 274 500 504 496 496 64 128 256), lower := (rows 193 274 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 385 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) }] }

theorem profile6_node34 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,272] 6 496 profile6_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,272] 6 496 profile6_node34_cert).mp (by decide +kernel))

def profile6_node35_cert : CutBound 9 := { lost := (rows 16 80 0 0 0 0 0 0 0), upper := (rows 193 290 468 472 464 496 64 128 256), lower := (rows 193 290 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 34 4 8 0 32 511 511 511), good := (rows 449 483 453 457 449 483 449 449 449) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 385 418 388 392 400 418 384 384 384) }] }

theorem profile6_node35 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,288] 6 464 profile6_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,288] 6 464 profile6_node35_cert).mp (by decide +kernel))

def profile6_node36_cert : CutBound 9 := { lost := (rows 16 16 64 64 0 0 0 0 0), upper := (rows 193 322 436 440 432 432 64 128 256), lower := (rows 193 322 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile6_node36 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,320] 6 432 profile6_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192,320] 6 432 profile6_node36_cert).mp (by decide +kernel))

def profile6_node25_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile6_node25_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node25 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [192] 6 (by decide) (choices 2) [48,80,96,192,272,288,320] profile6_node25_route profile6_node25_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile6_node26
  · exact profile6_node31
  · exact profile6_node32
  · exact profile6_node33
  · exact profile6_node34
  · exact profile6_node35
  · exact profile6_node36

def profile6_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile6_node0_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile6_node0 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [] 6 (by decide) (choices 2) [48,80,96,192] profile6_node0_route profile6_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile6_node1
  · exact profile6_node12
  · exact profile6_node24
  · exact profile6_node25

theorem profile6 : Upper (D (n:=9) [32,32,32,32,19,17,2,2,2]) (R (n:=9) [32,32,32,32,19,17,2,2,2]) [] 6 := profile6_node0


#print axioms profile6
end Delivery.SmallBudgetTenFinite9
