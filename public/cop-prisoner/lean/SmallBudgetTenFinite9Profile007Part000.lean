import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile7_node2_cert : CutBound 9 := { lost := (rows 64 64 48 48 0 0 0 0 0), upper := (rows 49 50 452 456 464 480 64 128 256), lower := (rows 49 50 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 1 2 511 511 511 0 511 511 511), good := (rows 477 478 476 476 476 476 476 476 476) },{ target := 6, region := (rows 3 3 4 8 16 32 0 511 511), good := (rows 435 435 388 392 400 416 384 384 384) }] }

theorem profile7_node2 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,48] 6 448 profile7_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,48] 6 448 profile7_node2_cert).mp (by decide +kernel))

def profile7_node4_cert : CutBound 9 := { lost := (rows 64 32 16 112 0 0 0 0 0), upper := (rows 49 82 100 392 400 416 64 128 256), lower := (rows 49 82 100 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 1 511 4 511 511 0 511 511 511), good := (rows 475 474 478 474 474 474 474 474 474) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile7_node4 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,96] 6 384 profile7_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,96] 6 384 profile7_node4_cert).mp (by decide +kernel))

def profile7_node5_cert : CutBound 9 := { lost := (rows 0 160 80 48 0 0 0 0 0), upper := (rows 49 82 164 456 464 480 64 128 256), lower := (rows 49 82 164 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 1 511 4 511 511 0 511 511 511), good := (rows 475 474 478 474 474 474 474 474 474) },{ target := 6, region := (rows 1 2 37 8 16 32 0 511 511), good := (rows 437 402 420 392 400 420 384 384 384) },{ target := 7, region := (rows 1 19 4 8 16 32 511 0 511), good := (rows 371 338 356 328 338 352 320 320 320) }] }

theorem profile7_node5 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,160] 6 448 profile7_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,160] 6 448 profile7_node5_cert).mp (by decide +kernel))

def profile7_node6_cert : CutBound 9 := { lost := (rows 64 32 48 80 0 0 0 0 0), upper := (rows 49 82 196 424 432 416 64 128 256), lower := (rows 49 82 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 1 19 511 8 16 0 511 511 511), good := (rows 471 470 452 460 470 452 452 452 452) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile7_node6 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,192] 6 416 profile7_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,192] 6 416 profile7_node6_cert).mp (by decide +kernel))

def profile7_node7_cert : CutBound 9 := { lost := (rows 0 160 112 16 0 0 0 0 0), upper := (rows 49 82 388 488 496 480 64 128 256), lower := (rows 49 82 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 1 19 511 8 16 0 511 511 511), good := (rows 471 470 452 460 470 452 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 437 406 388 396 404 420 388 388 388) },{ target := 7, region := (rows 1 19 4 8 16 32 511 0 511), good := (rows 371 338 324 328 338 352 320 320 320) }] }

theorem profile7_node7 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,384] 6 480 profile7_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80,384] 6 480 profile7_node7_cert).mp (by decide +kernel))

def profile7_node3_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile7_node3_route : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile7_node3 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,80] 6 (by decide) (choices 2) [96,160,192,384] profile7_node3_route profile7_node3_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node4
  · exact profile7_node5
  · exact profile7_node6
  · exact profile7_node7

def profile7_node9_cert : CutBound 9 := { lost := (rows 64 48 64 48 0 0 0 0 0), upper := (rows 49 194 52 456 464 480 64 128 256), lower := (rows 49 194 52 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 494 490 490 490 490 490 490) },{ target := 5, region := (rows 1 511 4 511 511 0 511 511 511), good := (rows 475 474 478 474 474 474 474 474 474) },{ target := 6, region := (rows 5 2 5 8 16 32 0 511 511), good := (rows 437 386 437 392 400 416 384 384 384) }] }

theorem profile7_node9 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,48] 6 448 profile7_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,48] 6 448 profile7_node9_cert).mp (by decide +kernel))

def profile7_node10_cert : CutBound 9 := { lost := (rows 64 48 32 80 0 0 0 0 0), upper := (rows 49 194 84 424 432 416 64 128 256), lower := (rows 49 194 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 494 490 490 490 490 490 490) },{ target := 5, region := (rows 1 511 21 8 16 0 511 511 511), good := (rows 471 450 470 458 470 450 450 450 450) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile7_node10 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,80] 6 416 profile7_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,80] 6 416 profile7_node10_cert).mp (by decide +kernel))

def profile7_node11_cert : CutBound 9 := { lost := (rows 64 48 48 64 0 0 0 0 0), upper := (rows 49 194 196 312 304 304 64 128 256), lower := (rows 49 194 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 471 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile7_node11 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,192] 6 304 profile7_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,192] 6 304 profile7_node11_cert).mp (by decide +kernel))

def profile7_node12_cert : CutBound 9 := { lost := (rows 0 48 224 16 0 0 0 0 0), upper := (rows 49 194 276 488 496 480 64 128 256), lower := (rows 49 194 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 511 0 511 511 511 511), good := (rows 491 490 494 490 490 490 490 490 490) },{ target := 5, region := (rows 1 511 21 8 16 0 511 511 511), good := (rows 471 450 470 458 470 450 450 450 450) },{ target := 6, region := (rows 1 2 21 8 16 32 0 511 511), good := (rows 437 386 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 21 8 16 32 511 0 511), good := (rows 373 322 340 328 340 352 320 320 320) }] }

theorem profile7_node12 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,272] 6 480 profile7_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,272] 6 480 profile7_node12_cert).mp (by decide +kernel))

def profile7_node13_cert : CutBound 9 := { lost := (rows 64 48 48 64 0 0 0 0 0), upper := (rows 49 194 324 440 432 432 64 128 256), lower := (rows 49 194 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 511 8 0 32 511 511 511), good := (rows 487 454 454 462 454 486 454 454 454) },{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 471 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 511 2 4 511 511 511 0 511 511), good := (rows 441 443 445 441 441 441 441 441 441) }] }

theorem profile7_node13 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,320] 6 432 profile7_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192,320] 6 432 profile7_node13_cert).mp (by decide +kernel))

def profile7_node8_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node8_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile7_node8 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48,192] 6 (by decide) (choices 2) [48,80,192,272,320] profile7_node8_route profile7_node8_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile7_node9
  · exact profile7_node10
  · exact profile7_node11
  · exact profile7_node12
  · exact profile7_node13

def profile7_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node1_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile7_node1 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [48] 6 (by decide) (choices 2) [48,80,192] profile7_node1_route profile7_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node2
  · exact profile7_node3
  · exact profile7_node8

def profile7_node16_cert : CutBound 9 := { lost := (rows 32 64 16 112 0 0 0 0 0), upper := (rows 81 50 100 392 400 416 64 128 256), lower := (rows 81 50 100 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 511 2 4 511 511 0 511 511 511), good := (rows 473 475 477 473 473 473 473 473 473) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile7_node16 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,96] 6 384 profile7_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,96] 6 384 profile7_node16_cert).mp (by decide +kernel))

def profile7_node17_cert : CutBound 9 := { lost := (rows 160 0 80 48 0 0 0 0 0), upper := (rows 81 50 164 456 464 480 64 128 256), lower := (rows 81 50 164 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 511 2 4 511 511 0 511 511 511), good := (rows 473 475 477 473 473 473 473 473 473) },{ target := 6, region := (rows 1 2 38 8 16 32 0 511 511), good := (rows 401 438 420 392 400 420 384 384 384) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 371 356 328 337 352 320 320 320) }] }

theorem profile7_node17 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,160] 6 448 profile7_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,160] 6 448 profile7_node17_cert).mp (by decide +kernel))

def profile7_node18_cert : CutBound 9 := { lost := (rows 32 64 48 80 0 0 0 0 0), upper := (rows 81 50 196 424 432 416 64 128 256), lower := (rows 81 50 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 19 2 511 8 16 0 511 511 511), good := (rows 469 471 452 460 469 452 452 452 452) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile7_node18 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,192] 6 416 profile7_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,192] 6 416 profile7_node18_cert).mp (by decide +kernel))

def profile7_node19_cert : CutBound 9 := { lost := (rows 160 0 112 16 0 0 0 0 0), upper := (rows 81 50 388 488 496 480 64 128 256), lower := (rows 81 50 388 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 19 2 511 8 16 0 511 511 511), good := (rows 469 471 452 460 469 452 452 452 452) },{ target := 6, region := (rows 1 2 511 8 16 32 0 511 511), good := (rows 405 438 388 396 404 420 388 388 388) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 371 324 328 337 352 320 320 320) }] }

theorem profile7_node19 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,384] 6 480 profile7_node19_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48,384] 6 480 profile7_node19_cert).mp (by decide +kernel))

def profile7_node15_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile7_node15_route : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile7_node15 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,48] 6 (by decide) (choices 2) [96,160,192,384] profile7_node15_route profile7_node15_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact profile7_node16
  · exact profile7_node17
  · exact profile7_node18
  · exact profile7_node19

def profile7_node20_cert : CutBound 9 := { lost := (rows 32 32 80 80 0 0 0 0 0), upper := (rows 81 82 420 424 432 416 64 128 256), lower := (rows 81 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 19 19 4 8 16 0 511 511 511), good := (rows 467 467 452 456 467 448 448 448 448) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile7_node20 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,80] 6 416 profile7_node20_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,80] 6 416 profile7_node20_cert).mp (by decide +kernel))

def profile7_node21_cert : CutBound 9 := { lost := (rows 160 144 64 64 0 0 0 0 0), upper := (rows 81 98 436 440 432 432 64 128 256), lower := (rows 81 98 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 5, region := (rows 17 2 4 8 16 0 511 511 511), good := (rows 465 450 452 456 465 448 448 448 448) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) },{ target := 7, region := (rows 17 34 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 354 320 320 320) }] }

theorem profile7_node21 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,96] 6 432 profile7_node21_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,96] 6 432 profile7_node21_cert).mp (by decide +kernel))

def profile7_node22_cert : CutBound 9 := { lost := (rows 160 96 16 16 0 0 0 0 0), upper := (rows 81 146 484 488 496 480 64 128 256), lower := (rows 81 146 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 511 511 0 511 511 511 511), good := (rows 493 494 492 492 492 492 492 492 492) },{ target := 5, region := (rows 19 19 4 8 16 0 511 511 511), good := (rows 467 467 452 456 467 448 448 448 448) },{ target := 6, region := (rows 1 19 4 8 16 32 0 511 511), good := (rows 403 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 19 2 4 8 16 32 511 0 511), good := (rows 337 339 324 328 337 352 320 320 320) }] }

theorem profile7_node22 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,144] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,144] 6 480 profile7_node22_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,144] 6 480 profile7_node22_cert).mp (by decide +kernel))

def profile7_node23_cert : CutBound 9 := { lost := (rows 416 336 0 0 0 0 0 0 0), upper := (rows 81 162 500 504 496 496 64 128 256), lower := (rows 81 162 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 34 4 8 0 32 511 511 511), good := (rows 449 482 452 456 448 482 448 448 448) },{ target := 5, region := (rows 17 2 4 8 16 0 511 511 511), good := (rows 465 450 452 456 465 448 448 448 448) },{ target := 6, region := (rows 1 34 4 8 16 32 0 511 511), good := (rows 401 418 388 392 400 418 384 384 384) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 354 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 34 4 8 16 32 511 511 0), good := (rows 209 226 196 200 209 226 192 192 192) }] }

theorem profile7_node23 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,160] 6 496 profile7_node23_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,160] 6 496 profile7_node23_cert).mp (by decide +kernel))

def profile7_node24_cert : CutBound 9 := { lost := (rows 160 48 64 64 0 0 0 0 0), upper := (rows 81 194 436 440 432 432 64 128 256), lower := (rows 81 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 5, region := (rows 17 511 4 8 16 0 511 511 511), good := (rows 467 450 454 458 467 450 450 450 450) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) }] }

theorem profile7_node24 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,192] 6 432 profile7_node24_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,192] 6 432 profile7_node24_cert).mp (by decide +kernel))

def profile7_node25_cert : CutBound 9 := { lost := (rows 416 112 0 0 0 0 0 0 0), upper := (rows 81 386 500 504 496 496 64 128 256), lower := (rows 81 386 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 511 4 8 0 32 511 511 511), good := (rows 451 450 454 458 450 482 450 450 450) },{ target := 5, region := (rows 17 511 4 8 16 0 511 511 511), good := (rows 467 450 454 458 467 450 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 32 0 511 511), good := (rows 403 386 390 394 402 418 386 386 386) },{ target := 7, region := (rows 17 2 4 8 16 32 511 0 511), good := (rows 337 322 324 328 337 352 320 320 320) },{ target := 8, region := (rows 17 2 4 8 16 32 511 511 0), good := (rows 209 194 196 200 209 224 192 192 192) }] }

theorem profile7_node25 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,384] 6 496 profile7_node25_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80,384] 6 496 profile7_node25_cert).mp (by decide +kernel))

def profile7_node14_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node14_route : Route 9 := (fun mask => match mask with | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile7_node14 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [80] 6 (by decide) (choices 2) [48,80,96,144,160,192,384] profile7_node14_route profile7_node14_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile7_node15
  · exact profile7_node20
  · exact profile7_node21
  · exact profile7_node22
  · exact profile7_node23
  · exact profile7_node24
  · exact profile7_node25

def profile7_node28_cert : CutBound 9 := { lost := (rows 48 64 64 48 0 0 0 0 0), upper := (rows 193 50 52 456 464 480 64 128 256), lower := (rows 193 50 52 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 5, region := (rows 511 2 4 511 511 0 511 511 511), good := (rows 473 475 477 473 473 473 473 473 473) },{ target := 6, region := (rows 1 6 6 8 16 32 0 511 511), good := (rows 385 438 438 392 400 416 384 384 384) }] }

theorem profile7_node28 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,48] 6 448 profile7_node28_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,48] 6 448 profile7_node28_cert).mp (by decide +kernel))

def profile7_node29_cert : CutBound 9 := { lost := (rows 48 64 32 80 0 0 0 0 0), upper := (rows 193 50 84 424 432 416 64 128 256), lower := (rows 193 50 84 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 5, region := (rows 511 2 22 8 16 0 511 511 511), good := (rows 449 471 469 457 469 449 449 449 449) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile7_node29 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,80] 6 416 profile7_node29_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,80] 6 416 profile7_node29_cert).mp (by decide +kernel))

def profile7_node30_cert : CutBound 9 := { lost := (rows 48 64 48 64 0 0 0 0 0), upper := (rows 193 50 196 312 304 304 64 128 256), lower := (rows 193 50 196 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 5, region := (rows 511 2 511 8 16 0 511 511 511), good := (rows 453 471 453 461 469 453 453 453 453) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile7_node30 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,192] 6 304 profile7_node30_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,192] 6 304 profile7_node30_cert).mp (by decide +kernel))

def profile7_node31_cert : CutBound 9 := { lost := (rows 48 0 224 16 0 0 0 0 0), upper := (rows 193 50 276 488 496 480 64 128 256), lower := (rows 193 50 276 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 511 0 511 511 511 511), good := (rows 489 491 493 489 489 489 489 489 489) },{ target := 5, region := (rows 511 2 22 8 16 0 511 511 511), good := (rows 449 471 469 457 469 449 449 449 449) },{ target := 6, region := (rows 1 2 22 8 16 32 0 511 511), good := (rows 385 438 404 392 404 416 384 384 384) },{ target := 7, region := (rows 1 2 22 8 16 32 511 0 511), good := (rows 321 374 340 328 340 352 320 320 320) }] }

theorem profile7_node31 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,272] 6 480 profile7_node31_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,272] 6 480 profile7_node31_cert).mp (by decide +kernel))

def profile7_node32_cert : CutBound 9 := { lost := (rows 48 64 48 64 0 0 0 0 0), upper := (rows 193 50 324 440 432 432 64 128 256), lower := (rows 193 50 324 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 511 8 0 32 511 511 511), good := (rows 453 487 453 461 453 485 453 453 453) },{ target := 5, region := (rows 511 2 511 8 16 0 511 511 511), good := (rows 453 471 453 461 469 453 453 453 453) },{ target := 6, region := (rows 1 511 4 511 511 511 0 511 511), good := (rows 443 442 446 442 442 442 442 442 442) }] }

theorem profile7_node32 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,320] 6 432 profile7_node32_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48,320] 6 432 profile7_node32_cert).mp (by decide +kernel))

def profile7_node27_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node27_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile7_node27 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,48] 6 (by decide) (choices 2) [48,80,192,272,320] profile7_node27_route profile7_node27_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile7_node28
  · exact profile7_node29
  · exact profile7_node30
  · exact profile7_node31
  · exact profile7_node32

def profile7_node33_cert : CutBound 9 := { lost := (rows 48 160 64 64 0 0 0 0 0), upper := (rows 193 82 436 440 432 432 64 128 256), lower := (rows 193 82 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 5, region := (rows 511 18 4 8 16 0 511 511 511), good := (rows 449 467 453 457 467 449 449 449 449) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) }] }

theorem profile7_node33 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,80] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,80] 6 432 profile7_node33_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,80] 6 432 profile7_node33_cert).mp (by decide +kernel))

def profile7_node34_cert : CutBound 9 := { lost := (rows 48 48 64 64 0 0 0 0 0), upper := (rows 193 194 308 312 304 304 64 128 256), lower := (rows 193 194 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 5, region := (rows 511 511 4 8 16 0 511 511 511), good := (rows 451 451 455 459 467 451 451 451 451) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile7_node34 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,192] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,192] 6 304 profile7_node34_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,192] 6 304 profile7_node34_cert).mp (by decide +kernel))

def profile7_node35_cert : CutBound 9 := { lost := (rows 304 224 0 0 0 0 0 0 0), upper := (rows 193 274 500 504 496 496 64 128 256), lower := (rows 193 274 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 2 4 8 0 32 511 511 511), good := (rows 449 451 453 457 449 481 449 449 449) },{ target := 5, region := (rows 511 18 4 8 16 0 511 511 511), good := (rows 449 467 453 457 467 449 449 449 449) },{ target := 6, region := (rows 1 18 4 8 16 32 0 511 511), good := (rows 385 402 388 392 402 416 384 384 384) },{ target := 7, region := (rows 1 18 4 8 16 32 511 0 511), good := (rows 321 338 324 328 338 352 320 320 320) },{ target := 8, region := (rows 511 2 4 8 16 32 511 511 0), good := (rows 193 211 197 201 209 225 193 193 193) }] }

theorem profile7_node35 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,272] 6 496 profile7_node35_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,272] 6 496 profile7_node35_cert).mp (by decide +kernel))

def profile7_node36_cert : CutBound 9 := { lost := (rows 48 48 64 64 0 0 0 0 0), upper := (rows 193 322 436 440 432 432 64 128 256), lower := (rows 193 322 4 8 16 32 64 128 256), losses := [{ target := 4, region := (rows 511 511 4 8 0 32 511 511 511), good := (rows 451 451 455 459 451 483 451 451 451) },{ target := 5, region := (rows 511 511 4 8 16 0 511 511 511), good := (rows 451 451 455 459 467 451 451 451 451) },{ target := 6, region := (rows 1 2 511 511 511 511 0 511 511), good := (rows 445 446 444 444 444 444 444 444 444) }] }

theorem profile7_node36 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,320] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,320] 6 432 profile7_node36_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192,320] 6 432 profile7_node36_cert).mp (by decide +kernel))

def profile7_node26_column : Nat → Fin 9 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node26_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem profile7_node26 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [192] 6 (by decide) (choices 2) [48,80,192,272,320] profile7_node26_route profile7_node26_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile7_node27
  · exact profile7_node33
  · exact profile7_node34
  · exact profile7_node35
  · exact profile7_node36

def profile7_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile7_node0_route : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile7_node0 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [] 6 (by decide) (choices 2) [48,80,192] profile7_node0_route profile7_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile7_node1
  · exact profile7_node14
  · exact profile7_node26

theorem profile7 : Upper (D (n:=9) [32,32,32,32,18,18,2,2,2]) (R (n:=9) [32,32,32,32,18,18,2,2,2]) [] 6 := profile7_node0


#print axioms profile7
end Delivery.SmallBudgetTenFinite9
