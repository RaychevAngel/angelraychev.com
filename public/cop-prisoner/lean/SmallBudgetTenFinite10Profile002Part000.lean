import SmallBudgetTenFinite10Common

namespace Delivery.SmallBudgetTenFinite10
open FiniteGame Extremal RowPrefix SmallBudgetProfiles
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def profile2_node3_cert : CutBound 10 := { lost := (rows 0 0 512 0 0 0 0 0 0 0), upper := (rows 25 98 388 904 912 928 960 128 256 512), lower := (rows 25 98 388 8 16 32 64 128 256 512), losses := [{ target := 9, region := (rows 1 2 1023 8 16 32 64 1023 1023 0), good := (rows 413 486 388 396 404 420 452 388 388 388) }] }

theorem profile2_node3 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,96,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,96,384] 6 896 profile2_node3_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,96,384] 6 896 profile2_node3_cert).mp (by decide +kernel))

def profile2_node2_column : Nat → Fin 10 := fun mask => match mask with | 3 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 544 => 5 | 192 => 6 | 320 => 6 | 576 => 6 | _ => 0

def profile2_node2_route : Route 10 := (fun mask => match mask with | 640 => (384,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 768 => (384,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node2 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,96] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,96] 6 (by decide) (choices 2) [384] profile2_node2_route profile2_node2_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact profile2_node3

def profile2_node4_cert : CutBound 10 := { lost := (rows 0 256 0 0 0 0 0 0 0 0), upper := (rows 25 162 964 968 976 992 960 128 256 512), lower := (rows 25 162 4 8 16 32 64 128 256 512), losses := [{ target := 8, region := (rows 1 34 4 8 16 32 64 1023 0 1023), good := (rows 665 674 644 648 656 674 704 640 640 640) }] }

theorem profile2_node4 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,160] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,160] 6 960 profile2_node4_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,160] 6 960 profile2_node4_cert).mp (by decide +kernel))

def profile2_node5_cert : CutBound 10 := { lost := (rows 0 512 0 0 0 0 0 0 0 0), upper := (rows 25 386 996 1000 1008 992 992 128 256 512), lower := (rows 25 386 4 8 16 32 64 128 256 512), losses := [{ target := 9, region := (rows 1 1023 4 8 16 32 64 1023 1023 0), good := (rows 411 386 390 394 402 418 450 386 386 386) }] }

theorem profile2_node5 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,384] 6 992 profile2_node5_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24,384] 6 992 profile2_node5_cert).mp (by decide +kernel))

def profile2_node1_column : Nat → Fin 10 := fun mask => match mask with | 5 => 0 | 9 => 0 | 17 => 0 | 33 => 0 | 65 => 0 | 129 => 0 | 257 => 0 | 513 => 0 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 520 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 528 => 4 | _ => 0

def profile2_node1_route : Route 10 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 544 => (160,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 8 | 8 => 7 | _ => i)) | 576 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | 7 => 9 | 9 => 7 | _ => i)) | 640 => (384,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 768 => (384,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node1 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [24] 6 (by decide) (choices 2) [96,160,384] profile2_node1_route profile2_node1_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node2
  · exact profile2_node4
  · exact profile2_node5

def profile2_node6_cert : CutBound 10 := { lost := (rows 256 0 0 0 0 0 0 0 0 0), upper := (rows 137 1010 1012 1016 1008 1008 1008 128 256 512), lower := (rows 137 2 4 8 16 32 64 128 256 512), losses := [{ target := 8, region := (rows 9 2 4 8 16 32 64 1023 0 1023), good := (rows 649 642 644 649 656 672 704 640 640 640) }] }

theorem profile2_node6 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [136] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [136] 6 1008 profile2_node6_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [136] 6 1008 profile2_node6_cert).mp (by decide +kernel))

def profile2_node7_cert : CutBound 10 := { lost := (rows 512 0 0 0 0 0 0 0 0 0), upper := (rows 385 1018 1020 1016 1016 1016 1016 128 256 512), lower := (rows 385 2 4 8 16 32 64 128 256 512), losses := [{ target := 9, region := (rows 1023 2 4 8 16 32 64 1023 1023 0), good := (rows 385 387 389 393 401 417 449 385 385 385) }] }

theorem profile2_node7 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [384] 6 :=
  DegreeLoss.cut_bound_sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [384] 6 1016 profile2_node7_cert
    ((DegreeLoss.cutCheck_true (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [384] 6 1016 profile2_node7_cert).mp (by decide +kernel))

def profile2_node0_column : Nat → Fin 10 := fun mask => match mask with | 6 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 514 => 1 | 12 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 516 => 2 | _ => 0

def profile2_node0_route : Route 10 := (fun mask => match mask with | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 72 => (24,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 520 => (136,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | 48 => (24,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 80 => (24,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 528 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 9 | 9 => 7 | _ => i)) | 96 => (24,(fun i => match i.val with | 3 => 5 | 4 => 6 | 5 => 3 | 6 => 4 | _ => i)) | 160 => (136,(fun i => match i.val with | 3 => 5 | 5 => 3 | _ => i)) | 288 => (136,(fun i => match i.val with | 3 => 5 | 5 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 544 => (136,(fun i => match i.val with | 3 => 5 | 5 => 3 | 7 => 9 | 9 => 7 | _ => i)) | 192 => (136,(fun i => match i.val with | 3 => 6 | 6 => 3 | _ => i)) | 320 => (136,(fun i => match i.val with | 3 => 6 | 6 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 576 => (136,(fun i => match i.val with | 3 => 6 | 6 => 3 | 7 => 9 | 9 => 7 | _ => i)) | 640 => (384,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 768 => (384,(fun i => match i.val with | 7 => 9 | 9 => 7 | _ => i)) | _ => (mask,id))

theorem profile2_node0 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [] 6 := by
  apply SmallFastRouting.sound (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [] 6 (by decide) (choices 2) [24,136,384] profile2_node0_route profile2_node0_column
    (by change RowCover 10 2 (choices 2); exact cover ⟨2,by decide⟩)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact profile2_node1
  · exact profile2_node6
  · exact profile2_node7

theorem profile2 : Upper (D (n:=10) [32,32,32,17,17,17,17,2,2,2]) (R (n:=10) [32,32,32,17,17,17,17,2,2,2]) [] 6 := profile2_node0


#print axioms profile2
end Delivery.SmallBudgetTenFinite10
