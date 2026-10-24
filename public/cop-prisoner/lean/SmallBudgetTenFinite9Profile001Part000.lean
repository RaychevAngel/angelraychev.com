import SmallBudgetTenFinite9Common

namespace Delivery.SmallBudgetTenFinite9
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile1_node2_cert : CutBound 9 := { lost := (rows 384 448 32 32 32 0 0 0 0), upper := (rows 97 35 453 457 465 32 64 128 256), lower := (rows 97 35 4 8 16 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 7 11 19 0 511 511 511), good := (rows 477 479 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 8 16 511 0 511 511), good := (rows 419 419 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) },{ target := 8, region := (rows 511 511 4 8 16 511 511 511 0), good := (rows 227 227 231 235 243 227 227 227 227) }] }

theorem profile1_node2 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,33] 6 449 profile1_node2_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,33] 6 449 profile1_node2_cert).mp (by decide +kernel))

def profile1_node3_cert : CutBound 9 := { lost := (rows 128 129 96 96 96 0 0 0 0), upper := (rows 97 98 389 393 401 32 64 128 256), lower := (rows 97 98 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 511 511 511 511), good := (rows 482 482 486 490 498 482 482 482 482) },{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 2 5 9 17 511 0 511 511), good := (rows 445 418 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 511 4 8 16 511 511 0 511), good := (rows 355 355 359 363 371 355 355 355 355) }] }

theorem profile1_node3 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,96] 6 385 profile1_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,96] 6 385 profile1_node3_cert).mp (by decide +kernel))

def profile1_node5_cert : CutBound 9 := { lost := (rows 128 96 192 33 33 0 0 0 0), upper := (rows 97 131 37 456 464 32 64 128 256), lower := (rows 97 131 37 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 5, region := (rows 1 7 4 511 511 0 511 511 511), good := (rows 475 475 479 472 472 472 472 472 472) },{ target := 6, region := (rows 1 7 7 8 16 511 0 511 511), good := (rows 423 423 423 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile1_node5 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,33] 6 448 profile1_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,33] 6 448 profile1_node5_cert).mp (by decide +kernel))

def profile1_node6_cert : CutBound 9 := { lost := (rows 128 96 129 96 96 0 0 0 0), upper := (rows 97 131 100 393 401 32 64 128 256), lower := (rows 97 131 100 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 511 511 511 511), good := (rows 484 486 484 492 500 484 484 484 484) },{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 4 11 19 511 0 511 511), good := (rows 443 443 420 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile1_node6 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,96] 6 385 profile1_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,96] 6 385 profile1_node6_cert).mp (by decide +kernel))

def profile1_node7_cert : CutBound 9 := { lost := (rows 128 96 96 129 129 0 0 0 0), upper := (rows 97 131 133 360 368 32 64 128 256), lower := (rows 97 131 133 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 5, region := (rows 1 7 7 8 16 0 511 511 511), good := (rows 455 455 455 456 464 448 448 448 448) },{ target := 6, region := (rows 1 7 7 8 16 511 0 511 511), good := (rows 423 423 423 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node7 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,129] 6 352 profile1_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,129] 6 352 profile1_node7_cert).mp (by decide +kernel))

def profile1_node8_cert : CutBound 9 := { lost := (rows 128 96 65 160 160 0 0 0 0), upper := (rows 97 131 164 329 337 32 64 128 256), lower := (rows 97 131 164 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 511 511 511 511), good := (rows 484 486 484 492 500 484 484 484 484) },{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node8 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,160] 6 321 profile1_node8_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,160] 6 321 profile1_node8_cert).mp (by decide +kernel))

def profile1_node9_cert : CutBound 9 := { lost := (rows 128 96 224 1 1 0 0 0 0), upper := (rows 97 131 261 488 496 32 64 128 256), lower := (rows 97 131 261 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 511 511 511 511 511 511), good := (rows 504 506 508 504 504 504 504 504 504) },{ target := 5, region := (rows 1 7 7 8 16 0 511 511 511), good := (rows 455 455 455 456 464 448 448 448 448) },{ target := 6, region := (rows 1 7 7 8 16 511 0 511 511), good := (rows 423 423 423 424 432 416 416 416 416) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile1_node9 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,257] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,257] 6 480 profile1_node9_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,257] 6 480 profile1_node9_cert).mp (by decide +kernel))

def profile1_node10_cert : CutBound 9 := { lost := (rows 128 96 193 32 32 0 0 0 0), upper := (rows 97 131 292 457 465 32 64 128 256), lower := (rows 97 131 292 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 511 511 511 511), good := (rows 484 486 484 492 500 484 484 484 484) },{ target := 5, region := (rows 1 3 4 11 19 0 511 511 511), good := (rows 475 475 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile1_node10 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,288] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,288] 6 449 profile1_node10_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,288] 6 449 profile1_node10_cert).mp (by decide +kernel))

def profile1_node11_cert : CutBound 9 := { lost := (rows 128 96 97 128 128 0 0 0 0), upper := (rows 97 131 388 361 369 32 64 128 256), lower := (rows 97 131 388 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 511 8 16 511 511 511 511), good := (rows 484 486 484 492 500 484 484 484 484) },{ target := 5, region := (rows 1 3 511 8 16 0 511 511 511), good := (rows 455 455 452 460 468 452 452 452 452) },{ target := 6, region := (rows 1 3 511 8 16 511 0 511 511), good := (rows 423 423 420 428 436 420 420 420 420) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node11 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,384] 6 353 profile1_node11_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129,384] 6 353 profile1_node11_cert).mp (by decide +kernel))

def profile1_node4_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile1_node4_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

theorem profile1_node4 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,129] 6 (by decide) (choices 2) [33,96,129,160,257,288,384] profile1_node4_route profile1_node4_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact profile1_node5
  · exact profile1_node6
  · exact profile1_node7
  · exact profile1_node8
  · exact profile1_node9
  · exact profile1_node10
  · exact profile1_node11

def profile1_node12_cert : CutBound 9 := { lost := (rows 384 321 32 32 32 0 0 0 0), upper := (rows 97 162 453 457 465 32 64 128 256), lower := (rows 97 162 4 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 511 511 511 511), good := (rows 482 482 486 490 498 482 482 482 482) },{ target := 5, region := (rows 1 2 5 9 17 0 511 511 511), good := (rows 477 450 452 456 464 448 448 448 448) },{ target := 6, region := (rows 1 511 4 8 16 511 0 511 511), good := (rows 419 418 422 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 4 8 16 511 511 0 511), good := (rows 353 355 357 361 369 353 353 353 353) },{ target := 8, region := (rows 511 511 4 8 16 511 511 511 0), good := (rows 227 227 231 235 243 227 227 227 227) }] }

theorem profile1_node12 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,160] 6 449 profile1_node12_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,160] 6 449 profile1_node12_cert).mp (by decide +kernel))

def profile1_node14_cert : CutBound 9 := { lost := (rows 128 97 192 32 32 0 0 0 0), upper := (rows 97 386 37 457 465 32 64 128 256), lower := (rows 97 386 37 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 511 511 511 511), good := (rows 482 482 486 490 498 482 482 482 482) },{ target := 5, region := (rows 1 511 4 13 21 0 511 511 511), good := (rows 475 450 479 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 511 8 16 511 511 0 511), good := (rows 357 359 357 365 373 357 357 357 357) }] }

theorem profile1_node14 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,33] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,33] 6 449 profile1_node14_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,33] 6 449 profile1_node14_cert).mp (by decide +kernel))

def profile1_node15_cert : CutBound 9 := { lost := (rows 0 97 1 96 96 0 0 0 0), upper := (rows 97 386 100 393 401 32 64 128 256), lower := (rows 97 386 100 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 511 8 16 511 511 511 511), good := (rows 486 486 486 494 502 486 486 486 486) },{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 4 9 17 511 0 511 511), good := (rows 443 418 422 426 434 418 418 418 418) }] }

theorem profile1_node15 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,96] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,96] 6 385 profile1_node15_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,96] 6 385 profile1_node15_cert).mp (by decide +kernel))

def profile1_node16_cert : CutBound 9 := { lost := (rows 128 97 96 128 128 0 0 0 0), upper := (rows 97 386 133 361 369 32 64 128 256), lower := (rows 97 386 133 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 4 8 16 511 511 511 511), good := (rows 482 482 486 490 498 482 482 482 482) },{ target := 5, region := (rows 1 511 5 8 16 0 511 511 511), good := (rows 455 450 455 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 5 8 16 511 0 511 511), good := (rows 423 418 423 426 434 418 418 418 418) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node16 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,129] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,129] 6 353 profile1_node16_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,129] 6 353 profile1_node16_cert).mp (by decide +kernel))

def profile1_node17_cert : CutBound 9 := { lost := (rows 128 97 65 160 160 0 0 0 0), upper := (rows 97 386 164 329 337 32 64 128 256), lower := (rows 97 386 164 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 511 8 16 511 511 511 511), good := (rows 486 486 486 494 502 486 486 486 486) },{ target := 5, region := (rows 1 511 4 9 17 0 511 511 511), good := (rows 475 450 454 458 466 450 450 450 450) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node17 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,160] 6 321 profile1_node17_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,160] 6 321 profile1_node17_cert).mp (by decide +kernel))

def profile1_node18_cert : CutBound 9 := { lost := (rows 128 97 97 128 128 0 0 0 0), upper := (rows 97 386 388 105 113 32 64 128 256), lower := (rows 97 386 388 8 16 32 64 128 256), losses := [{ target := 0, region := (rows 0 511 511 8 16 511 511 511 511), good := (rows 486 486 486 494 502 486 486 486 486) },{ target := 5, region := (rows 1 511 511 8 16 0 511 511 511), good := (rows 455 454 454 462 470 454 454 454 454) },{ target := 6, region := (rows 1 511 511 8 16 511 0 511 511), good := (rows 423 422 422 430 438 422 422 422 422) },{ target := 7, region := (rows 511 2 4 511 511 511 511 0 511), good := (rows 377 379 381 377 377 377 377 377 377) }] }

theorem profile1_node18 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,384] 6 97 profile1_node18_cert
    ((DegreeLoss.cutCheck_true (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384,384] 6 97 profile1_node18_cert).mp (by decide +kernel))

def profile1_node13_column : Nat → Fin 9 := fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile1_node13_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile1_node13 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96,384] 6 (by decide) (choices 2) [33,96,129,160,384] profile1_node13_route profile1_node13_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile1_node14
  · exact profile1_node15
  · exact profile1_node16
  · exact profile1_node17
  · exact profile1_node18

def profile1_node1_column : Nat → Fin 9 := fun mask => match mask with | 5 => 2 | 9 => 3 | 17 => 4 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile1_node1_route : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

theorem profile1_node1 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [96] 6 (by decide) (choices 2) [33,96,129,160,384] profile1_node1_route profile1_node1_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact profile1_node2
  · exact profile1_node3
  · exact profile1_node4
  · exact profile1_node12
  · exact profile1_node13

def profile1_node0_column : Nat → Fin 9 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0

def profile1_node0_route : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (96,(fun i => match i.val with | 5 => 8 | 8 => 5 | _ => i)) | 384 => (96,(fun i => match i.val with | 5 => 7 | 6 => 8 | 7 => 5 | 8 => 6 | _ => i)) | _ => (mask,id))

theorem profile1_node0 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [] 6 (by decide) (choices 2) [96] profile1_node0_route profile1_node0_column
    (by change RowCover 9 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile1_node1

theorem profile1 : Upper (D (n:=9) [34,32,32,32,32,2,2,2,2]) (R (n:=9) [34,32,32,32,32,2,2,2,2]) [] 6 := profile1_node0


#print axioms profile1
end Delivery.SmallBudgetTenFinite9
