import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile0_node2_cert : CutBound 9 := { lost := (rows 0 64 32 32 0 0 0 0 0), upper := (rows 113 35 452 456 464 32 64 128 256), lower := (rows 113 35 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 511 511 0 511 511 511), good := (rows 477 479 476 476 476 476 476 476 476) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 435 419 420 424 432 416 416 416 416) }] }

theorem profile0_node2 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,33] 6 448 profile0_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,33] 6 448 profile0_node2_cert).mp (by decide +kernel))

def profile0_node3_cert : CutBound 9 := { lost := (rows 0 0 96 96 0 0 0 0 0), upper := (rows 113 98 389 393 401 32 64 128 256), lower := (rows 113 98 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 511 0 511 511), good := (rows 445 418 420 424 432 416 416 416 416) }] }

theorem profile0_node3 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,96] 6 385 profile0_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,96] 6 385 profile0_node3_cert).mp (by decide +kernel))

def profile0_node4_cert : CutBound 9 := { lost := (rows 128 96 0 0 0 0 0 0 0), upper := (rows 113 131 484 488 496 32 64 128 256), lower := (rows 113 131 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 511 511 511), good := (rows 467 451 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 435 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 17 2 4 8 16 511 511 0 511), good := (rows 369 355 356 360 369 352 352 352 352) }] }

theorem profile0_node4 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,129] 6 480 profile0_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,129] 6 480 profile0_node4_cert).mp (by decide +kernel))

def profile0_node5_cert : CutBound 9 := { lost := (rows 0 64 32 32 0 0 0 0 0), upper := (rows 113 162 453 457 465 32 64 128 256), lower := (rows 113 162 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 4 8 16 511 0 511 511), good := (rows 435 418 422 426 434 418 418 418 418) }] }

theorem profile0_node5 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,160] 6 449 profile0_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,160] 6 449 profile0_node5_cert).mp (by decide +kernel))

def profile0_node6_cert : CutBound 9 := { lost := (rows 128 96 0 0 0 0 0 0 0), upper := (rows 113 386 485 489 497 32 64 128 256), lower := (rows 113 386 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 511 4 8 16 0 511 511 511), good := (rows 467 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 4 8 16 511 0 511 511), good := (rows 435 418 422 426 434 418 418 418 418) },{ target := 7, region := (rows 17 2 4 8 16 511 511 0 511), good := (rows 369 354 356 360 369 352 352 352 352) }] }

theorem profile0_node6 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,384] 6 481 profile0_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112,384] 6 481 profile0_node6_cert).mp (by decide +kernel))

def profile0_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile0_node1_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile0_node1 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [112] 6 (by decide) (choices 2) [33,96,129,160,384] profile0_node1_route profile0_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile0_node2
  · exact profile0_node3
  · exact profile0_node4
  · exact profile0_node5
  · exact profile0_node6

def profile0_node9_cert : CutBound 9 := { lost := (rows 0 96 0 96 0 0 0 0 0), upper := (rows 225 19 100 392 400 32 64 128 256), lower := (rows 225 19 100 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 511 511 0 511 511 511), good := (rows 475 475 476 472 472 472 472 472 472) },{ target := 6, region := (rows 1 3 4 511 511 511 0 511 511), good := (rows 443 443 444 440 440 440 440 440 440) }] }

theorem profile0_node9 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,96] 6 384 profile0_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,96] 6 384 profile0_node9_cert).mp (by decide +kernel))

def profile0_node10_cert : CutBound 9 := { lost := (rows 0 32 64 32 0 0 0 0 0), upper := (rows 225 19 292 456 464 32 64 128 256), lower := (rows 225 19 292 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 511 511 0 511 511 511), good := (rows 475 475 476 472 472 472 472 472 472) },{ target := 6, region := (rows 1 2 511 8 16 511 0 511 511), good := (rows 421 439 420 428 436 420 420 420 420) }] }

theorem profile0_node10 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,288] 6 448 profile0_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17,288] 6 448 profile0_node10_cert).mp (by decide +kernel))

def profile0_node8_column : Nat → Fin 9 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile0_node8_route : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile0_node8 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,17] 6 (by decide) (choices 2) [96,288] profile0_node8_route profile0_node8_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node9
  · exact profile0_node10

def profile0_node11_cert : CutBound 9 := { lost := (rows 0 64 32 32 0 0 0 0 0), upper := (rows 225 35 468 472 464 32 64 128 256), lower := (rows 225 35 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 511 511 511 0 511 511 511), good := (rows 477 479 476 476 476 476 476 476 476) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) }] }

theorem profile0_node11 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,33] 6 464 profile0_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,33] 6 464 profile0_node11_cert).mp (by decide +kernel))

def profile0_node12_cert : CutBound 9 := { lost := (rows 0 64 32 32 0 0 0 0 0), upper := (rows 225 50 453 457 465 32 64 128 256), lower := (rows 225 50 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 466 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 18 4 8 16 511 0 511 511), good := (rows 417 434 420 424 434 416 416 416 416) }] }

theorem profile0_node12 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,48] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,48] 6 449 profile0_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,48] 6 449 profile0_node12_cert).mp (by decide +kernel))

def profile0_node13_cert : CutBound 9 := { lost := (rows 0 0 96 96 0 0 0 0 0), upper := (rows 225 98 405 409 401 32 64 128 256), lower := (rows 225 98 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 511 0 511 511), good := (rows 445 418 420 424 432 416 416 416 416) }] }

theorem profile0_node13 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,96] 6 401 profile0_node13_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,96] 6 401 profile0_node13_cert).mp (by decide +kernel))

def profile0_node14_cert : CutBound 9 := { lost := (rows 0 224 0 0 0 0 0 0 0), upper := (rows 225 259 500 504 496 32 64 128 256), lower := (rows 225 259 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 3 4 8 16 0 511 511 511), good := (rows 451 451 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 1 3 4 8 16 511 511 0 511), good := (rows 355 355 356 360 368 352 352 352 352) }] }

theorem profile0_node14 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,257] 6 496 profile0_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,257] 6 496 profile0_node14_cert).mp (by decide +kernel))

def profile0_node15_cert : CutBound 9 := { lost := (rows 0 224 0 0 0 0 0 0 0), upper := (rows 225 274 485 489 497 32 64 128 256), lower := (rows 225 274 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 511 511 511), good := (rows 449 466 452 456 466 448 448 448 448) },{ target := 6, region := (rows 1 18 4 8 16 511 0 511 511), good := (rows 417 434 420 424 434 416 416 416 416) },{ target := 7, region := (rows 1 18 4 8 16 511 511 0 511), good := (rows 353 370 356 360 370 352 352 352 352) }] }

theorem profile0_node15 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,272] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,272] 6 481 profile0_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,272] 6 481 profile0_node15_cert).mp (by decide +kernel))

def profile0_node16_cert : CutBound 9 := { lost := (rows 0 64 32 32 0 0 0 0 0), upper := (rows 225 290 469 473 465 32 64 128 256), lower := (rows 225 290 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 4 8 16 511 0 511 511), good := (rows 419 418 422 426 434 418 418 418 418) }] }

theorem profile0_node16 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,288] 6 465 profile0_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224,288] 6 465 profile0_node16_cert).mp (by decide +kernel))

def profile0_node7_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0

def profile0_node7_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem profile0_node7 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [224] 6 (by decide) (choices 2) [17,33,48,96,257,272,288] profile0_node7_route profile0_node7_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile0_node8
  · exact profile0_node11
  · exact profile0_node12
  · exact profile0_node13
  · exact profile0_node14
  · exact profile0_node15
  · exact profile0_node16

def profile0_node0_column : Nat → Fin 9 := fun mask => match mask with | 14 => 1 | 22 => 1 | 38 => 1 | 70 => 1 | 134 => 1 | 262 => 1 | 26 => 1 | 42 => 1 | 74 => 1 | 138 => 1 | 266 => 1 | 50 => 1 | 82 => 1 | 146 => 1 | 274 => 1 | 98 => 1 | 162 => 1 | 290 => 1 | 194 => 1 | 322 => 1 | 386 => 1 | 28 => 2 | 44 => 2 | 76 => 2 | 140 => 2 | 268 => 2 | 52 => 2 | 84 => 2 | 148 => 2 | 276 => 2 | 100 => 2 | 164 => 2 | 292 => 2 | 196 => 2 | 324 => 2 | 388 => 2 | 56 => 3 | 88 => 3 | 152 => 3 | 280 => 3 | 104 => 3 | 168 => 3 | 296 => 3 | 200 => 3 | 328 => 3 | 392 => 3 | _ => 0

def profile0_node0_route : Route 9 := (fun mask => match mask with | 176 => (112,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 304 => (112,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 208 => (112,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 336 => (112,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 400 => (112,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | 352 => (224,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 416 => (224,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 448 => (224,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | _ => (mask,id))

theorem profile0_node0 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [] 6 (by decide) (choices 3) [112,224] profile0_node0_route profile0_node0_column
    (by change RowCover 9 3 (choices 3); exact cover ⟨3,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact profile0_node1
  · exact profile0_node7

theorem profile0 : Upper (D (n:=9) [49,32,32,32,17,2,2,2,2]) (R (n:=9) [49,32,32,32,17,2,2,2,2]) [] 6 := profile0_node0


#print axioms profile0
end Delivery.SmallBudgetTenFinite9
