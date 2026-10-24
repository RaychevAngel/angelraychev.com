import IrregularTen14Base

namespace Delivery.IrregularTen14.Case00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 7 11 52 56 976 992 960 960 960 960), lower := (rows 7 11 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [6,9,48,48] 13 :=
  bound_sound D R [6,9,48,48] 13 bound_2
    ((Boolean.boundCheck_true D R [6,9,48,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 7 11 52 88 1008 992 992 992 992 992), lower := (rows 7 11 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [6,9,48,80] 13 :=
  bound_sound D R [6,9,48,80] 13 bound_3
    ((Boolean.boundCheck_true D R [6,9,48,80] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 7 11 52 200 1008 1008 1008 1008 1008 1008), lower := (rows 7 11 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_4 : Upper D R [6,9,48,192] 13 :=
  bound_sound D R [6,9,48,192] 13 bound_4
    ((Boolean.boundCheck_true D R [6,9,48,192] 13 bound_4).mp (by decide +kernel))

def bound_5 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 7 11 52 280 752 736 736 736 992 736), lower := (rows 7 11 52 280 16 32 64 128 256 512), losses := [] }

theorem upper_5 : Upper D R [6,9,48,272] 13 :=
  bound_sound D R [6,9,48,272] 13 bound_5
    ((Boolean.boundCheck_true D R [6,9,48,272] 13 bound_5).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 7 11 52 328 752 752 752 752 1008 752), lower := (rows 7 11 52 328 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [6,9,48,320] 13 :=
  bound_sound D R [6,9,48,320] 13 bound_6
    ((Boolean.boundCheck_true D R [6,9,48,320] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 7 11 52 776 48 240 208 208 464 720), lower := (rows 7 11 52 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 5 7 4 29 16 0 84 148 276 532), good := (rows 975 11 991 776 984 0 64 128 256 512) }] }

theorem upper_8 : Upper D R [6,9,48,768,32] 13 :=
  bound_sound D R [6,9,48,768,32] 13 bound_8
    ((Boolean.boundCheck_true D R [6,9,48,768,32] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 11 52 776 80 48 224 224 480 736), lower := (rows 7 11 52 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 45 0 32 100 164 292 548), good := (rows 975 11 1007 776 64 1000 64 128 256 512) }] }

theorem upper_10 : Upper D R [6,9,48,768,64,16] 13 :=
  bound_sound D R [6,9,48,768,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [6,9,48,768,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 176 176 192 176 0 0 0 0 0 0), upper := (rows 7 11 52 776 80 96 240 176 432 688), lower := (rows 7 11 52 776 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 5 7 4 13 16 32 0 132 260 516), good := (rows 911 11 959 776 16 32 0 128 256 512) }] }

theorem upper_11 : Upper D R [6,9,48,768,64,64] 13 :=
  bound_sound D R [6,9,48,768,64,64] 13 bound_11
    ((Boolean.boundCheck_true D R [6,9,48,768,64,64] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 11 52 776 80 160 80 224 480 736), lower := (rows 7 11 52 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 92 0 244 64 208 336 592), good := (rows 47 11 943 776 1000 160 1000 160 256 512) }] }

theorem upper_13 : Upper D R [6,9,48,768,64,128,16] 13 :=
  bound_sound D R [6,9,48,768,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [6,9,48,768,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 7 11 52 776 80 160 96 208 464 720), lower := (rows 7 11 52 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 5 7 4 92 80 0 64 208 336 592), good := (rows 15 11 927 776 984 128 984 128 256 512) }] }

theorem upper_14 : Upper D R [6,9,48,768,64,128,32] 13 :=
  bound_sound D R [6,9,48,768,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [6,9,48,768,64,128,32] 13 bound_14).mp (by decide +kernel))

def bound_15 : Bound 10 := { allowed := (rows 240 240 128 240 0 0 0 0 0 0), upper := (rows 7 11 52 776 80 160 192 240 368 624), lower := (rows 7 11 52 776 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 20 8 16 224 0 128 256 512), good := (rows 7 11 52 776 52 160 160 160 256 512) }] }

theorem upper_15 : Upper D R [6,9,48,768,64,128,128] 13 :=
  bound_sound D R [6,9,48,768,64,128,128] 13 bound_15
    ((Boolean.boundCheck_true D R [6,9,48,768,64,128,128] 13 bound_15).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [6,9,48,768,64,128] 13 := by
  apply routed_branch D R [6,9,48,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,48,768,64,128] (choices 1) [16,32,128] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_13
  · exact upper_14
  · exact upper_15

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [6,9,48,768,64] 13 := by
  apply routed_branch D R [6,9,48,768,64] 13 (by decide) (choices 1) [16,64,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,48,768,64] (choices 1) [16,64,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def route_7 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_7 : Upper D R [6,9,48,768] 13 := by
  apply routed_branch D R [6,9,48,768] 13 (by decide) (choices 1) [32,64] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,48,768] (choices 1) [32,64] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_8
  · exact upper_9

def route_1 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [6,9,48] 13 := by
  apply routed_branch D R [6,9,48] 13 (by decide) (choices 2) [48,80,192,272,320,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,9,48] (choices 2) [48,80,192,272,320,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5
  · exact upper_6
  · exact upper_7

def bound_17 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 56 752 736 736 736 992 736), lower := (rows 7 11 276 56 16 32 64 128 256 512), losses := [] }

theorem upper_17 : Upper D R [6,9,272,48] 13 :=
  bound_sound D R [6,9,272,48] 13 bound_17
    ((Boolean.boundCheck_true D R [6,9,272,48] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 7 11 276 104 752 752 752 752 1008 752), lower := (rows 7 11 276 104 16 32 64 128 256 512), losses := [] }

theorem upper_18 : Upper D R [6,9,272,96] 13 :=
  bound_sound D R [6,9,272,96] 13 bound_18
    ((Boolean.boundCheck_true D R [6,9,272,96] 13 bound_18).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 208 208 192 192 0 0 0 0 0 0), upper := (rows 7 11 276 536 48 96 96 192 448 704), lower := (rows 7 11 276 536 48 96 96 128 256 512), losses := [{ target := 5, region := (rows 29 30 20 24 16 0 64 224 352 608), good := (rows 7 11 287 543 927 960 960 128 256 512) }] }

theorem upper_22 : Upper D R [6,9,272,528,32,64,32] 13 :=
  bound_sound D R [6,9,272,528,32,64,32] 13 bound_22
    ((Boolean.boundCheck_true D R [6,9,272,528,32,64,32] 13 bound_22).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 208 208 192 224 0 0 0 0 0 0), upper := (rows 7 11 276 536 48 96 192 160 320 640), lower := (rows 7 11 276 536 48 96 192 160 320 512), losses := [{ target := 5, region := (rows 9 10 20 8 16 0 192 128 480 704), good := (rows 7 11 276 543 276 832 960 960 832 512) }] }

theorem upper_25 : Upper D R [6,9,272,528,32,64,128,32,64] 13 :=
  bound_sound D R [6,9,272,528,32,64,128,32,64] 13 bound_25
    ((Boolean.boundCheck_true D R [6,9,272,528,32,64,128,32,64] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 208 208 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 536 48 96 192 160 384 576), lower := (rows 7 11 276 536 48 96 192 160 384 512), losses := [{ target := 5, region := (rows 5 7 4 28 16 0 448 128 448 996), good := (rows 527 11 863 536 536 832 960 960 960 512) }] }

theorem upper_26 : Upper D R [6,9,272,528,32,64,128,32,128] 13 :=
  bound_sound D R [6,9,272,528,32,64,128,32,128] 13 bound_26
    ((Boolean.boundCheck_true D R [6,9,272,528,32,64,128,32,128] 13 bound_26).mp (by decide +kernel))

def route_24 : Route 10 := (fun mask => (mask,id))

theorem upper_24 : Upper D R [6,9,272,528,32,64,128,32] 13 := by
  apply routed_branch D R [6,9,272,528,32,64,128,32] 13 (by decide) (choices 1) [64,128] route_24
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528,32,64,128,32] (choices 1) [64,128] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_25
  · exact upper_26

def bound_28 : Bound 10 := { allowed := (rows 208 208 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 536 48 96 192 192 288 640), lower := (rows 7 11 276 536 48 96 192 192 288 512), losses := [{ target := 5, region := (rows 5 7 4 28 16 0 1023 1023 256 1023), good := (rows 719 715 991 728 728 704 704 704 960 704) }] }

theorem upper_28 : Upper D R [6,9,272,528,32,64,128,64,32] 13 :=
  bound_sound D R [6,9,272,528,32,64,128,64,32] 13 bound_28
    ((Boolean.boundCheck_true D R [6,9,272,528,32,64,128,64,32] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 208 208 192 224 0 0 0 0 0 0), upper := (rows 7 11 276 536 48 96 192 192 384 544), lower := (rows 7 11 276 536 48 96 192 192 384 512), losses := [{ target := 5, region := (rows 11 10 28 8 16 0 1023 1023 1023 512), good := (rows 455 463 468 991 468 448 448 448 448 960) }] }

theorem upper_29 : Upper D R [6,9,272,528,32,64,128,64,128] 13 :=
  bound_sound D R [6,9,272,528,32,64,128,64,128] 13 bound_29
    ((Boolean.boundCheck_true D R [6,9,272,528,32,64,128,64,128] 13 bound_29).mp (by decide +kernel))

def route_27 : Route 10 := (fun mask => (mask,id))

theorem upper_27 : Upper D R [6,9,272,528,32,64,128,64] 13 := by
  apply routed_branch D R [6,9,272,528,32,64,128,64] 13 (by decide) (choices 1) [32,128] route_27
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528,32,64,128,64] (choices 1) [32,128] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_28
  · exact upper_29

def route_23 : Route 10 := (fun mask => (mask,id))

theorem upper_23 : Upper D R [6,9,272,528,32,64,128] 13 := by
  apply routed_branch D R [6,9,272,528,32,64,128] 13 (by decide) (choices 1) [32,64] route_23
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528,32,64,128] (choices 1) [32,64] route_23).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_24
  · exact upper_27

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [6,9,272,528,32,64] 13 := by
  apply routed_branch D R [6,9,272,528,32,64] 13 (by decide) (choices 1) [32,128] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528,32,64] (choices 1) [32,128] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_22
  · exact upper_23

def route_20 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_20 : Upper D R [6,9,272,528,32] 13 := by
  apply routed_branch D R [6,9,272,528,32] 13 (by decide) (choices 1) [64] route_20
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528,32] (choices 1) [64] route_20).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_21

def route_19 : Route 10 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 128 => (32,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_19 : Upper D R [6,9,272,528] 13 := by
  apply routed_branch D R [6,9,272,528] 13 (by decide) (choices 1) [32] route_19
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,528] (choices 1) [32] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_20

def bound_31 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 11 276 552 48 240 208 208 464 720), lower := (rows 7 11 276 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 84 148 276 532), good := (rows 967 11 980 520 980 0 64 128 256 512) }] }

theorem upper_31 : Upper D R [6,9,272,544,32] 13 :=
  bound_sound D R [6,9,272,544,32] 13 bound_31
    ((Boolean.boundCheck_true D R [6,9,272,544,32] 13 bound_31).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 48 224 224 480 736), lower := (rows 7 11 276 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 104 168 296 552), good := (rows 7 971 260 1000 64 1000 64 128 256 512) }] }

theorem upper_33 : Upper D R [6,9,272,544,64,16] 13 :=
  bound_sound D R [6,9,272,544,64,16] 13 bound_33
    ((Boolean.boundCheck_true D R [6,9,272,544,64,16] 13 bound_33).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 96 80 160 416 672), lower := (rows 7 11 276 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 124 0 112 64 252 380 636), good := (rows 911 907 943 936 1000 1000 1000 128 256 512) }] }

theorem upper_35 : Upper D R [6,9,272,544,64,64,16] 13 :=
  bound_sound D R [6,9,272,544,64,64,16] 13 bound_35
    ((Boolean.boundCheck_true D R [6,9,272,544,64,64,16] 13 bound_35).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 96 96 144 400 656), lower := (rows 7 11 276 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 103 107 356 616 96 96 96 224 352 616) }] }

theorem upper_36 : Upper D R [6,9,272,544,64,64,32] 13 :=
  bound_sound D R [6,9,272,544,64,64,32] 13 bound_36
    ((Boolean.boundCheck_true D R [6,9,272,544,64,64,32] 13 bound_36).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 96 192 144 416 672), lower := (rows 7 11 276 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 5 6 4 248 0 240 192 128 448 704), good := (rows 7 11 303 552 872 872 1000 1000 256 512) }] }

theorem upper_38 : Upper D R [6,9,272,544,64,64,128,16] 13 :=
  bound_sound D R [6,9,272,544,64,64,128,16] 13 bound_38
    ((Boolean.boundCheck_true D R [6,9,272,544,64,64,128,16] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 96 192 160 400 656), lower := (rows 7 11 276 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 231 235 484 744 224 224 224 224 480 744) }] }

theorem upper_39 : Upper D R [6,9,272,544,64,64,128,32] 13 :=
  bound_sound D R [6,9,272,544,64,64,128,32] 13 bound_39
    ((Boolean.boundCheck_true D R [6,9,272,544,64,64,128,32] 13 bound_39).mp (by decide +kernel))

def route_37 : Route 10 := (fun mask => (mask,id))

theorem upper_37 : Upper D R [6,9,272,544,64,64,128] 13 := by
  apply routed_branch D R [6,9,272,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544,64,64,128] (choices 1) [16,32] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_38
  · exact upper_39

def route_34 : Route 10 := (fun mask => (mask,id))

theorem upper_34 : Upper D R [6,9,272,544,64,64] 13 := by
  apply routed_branch D R [6,9,272,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_34
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544,64,64] (choices 1) [16,32,128] route_34).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_35
  · exact upper_36
  · exact upper_37

def bound_41 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 160 80 224 480 736), lower := (rows 7 11 276 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 92 0 244 64 208 336 592), good := (rows 47 11 943 552 1000 160 1000 160 256 512) }] }

theorem upper_41 : Upper D R [6,9,272,544,64,128,16] 13 :=
  bound_sound D R [6,9,272,544,64,128,16] 13 bound_41
    ((Boolean.boundCheck_true D R [6,9,272,544,64,128,16] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 160 96 208 464 720), lower := (rows 7 11 276 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 84 8 80 0 64 208 336 592), good := (rows 7 11 916 520 980 128 980 128 256 512) }] }

theorem upper_42 : Upper D R [6,9,272,544,64,128,32] 13 :=
  bound_sound D R [6,9,272,544,64,128,32] 13 bound_42
    ((Boolean.boundCheck_true D R [6,9,272,544,64,128,32] 13 bound_42).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 160 192 144 352 608), lower := (rows 7 11 276 552 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 5 6 4 248 0 224 224 128 504 760), good := (rows 7 779 783 872 872 1000 1000 1000 256 512) }] }

theorem upper_44 : Upper D R [6,9,272,544,64,128,128,16] 13 :=
  bound_sound D R [6,9,272,544,64,128,128,16] 13 bound_44
    ((Boolean.boundCheck_true D R [6,9,272,544,64,128,128,16] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 160 192 160 336 592), lower := (rows 7 11 276 552 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 231 235 484 744 224 224 224 224 480 744) }] }

theorem upper_45 : Upper D R [6,9,272,544,64,128,128,32] 13 :=
  bound_sound D R [6,9,272,544,64,128,128,32] 13 bound_45
    ((Boolean.boundCheck_true D R [6,9,272,544,64,128,128,32] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 11 276 552 80 160 192 192 304 560), lower := (rows 7 11 276 552 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 231 235 484 744 224 224 224 224 480 744) }] }

theorem upper_46 : Upper D R [6,9,272,544,64,128,128,64] 13 :=
  bound_sound D R [6,9,272,544,64,128,128,64] 13 bound_46
    ((Boolean.boundCheck_true D R [6,9,272,544,64,128,128,64] 13 bound_46).mp (by decide +kernel))

def route_43 : Route 10 := (fun mask => (mask,id))

theorem upper_43 : Upper D R [6,9,272,544,64,128,128] 13 := by
  apply routed_branch D R [6,9,272,544,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_43
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544,64,128,128] (choices 1) [16,32,64] route_43).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_44
  · exact upper_45
  · exact upper_46

def route_40 : Route 10 := (fun mask => (mask,id))

theorem upper_40 : Upper D R [6,9,272,544,64,128] 13 := by
  apply routed_branch D R [6,9,272,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_40
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544,64,128] (choices 1) [16,32,128] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43

def route_32 : Route 10 := (fun mask => (mask,id))

theorem upper_32 : Upper D R [6,9,272,544,64] 13 := by
  apply routed_branch D R [6,9,272,544,64] 13 (by decide) (choices 1) [16,64,128] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544,64] (choices 1) [16,64,128] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_40

def route_30 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_30 : Upper D R [6,9,272,544] 13 := by
  apply routed_branch D R [6,9,272,544] 13 (by decide) (choices 1) [32,64] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,272,544] (choices 1) [32,64] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_31
  · exact upper_32

def route_16 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_16 : Upper D R [6,9,272] 13 := by
  apply routed_branch D R [6,9,272] 13 (by decide) (choices 2) [48,96,528,544] route_16
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,9,272] (choices 2) [48,96,528,544] route_16).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_17
  · exact upper_18
  · exact upper_19
  · exact upper_30

def bound_49 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 11 772 56 48 240 208 208 464 720), lower := (rows 7 11 772 56 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 11 10 30 8 16 0 88 152 280 536), good := (rows 7 975 772 991 980 0 64 128 256 512) }] }

theorem upper_49 : Upper D R [6,9,768,48,32] 13 :=
  bound_sound D R [6,9,768,48,32] 13 bound_49
    ((Boolean.boundCheck_true D R [6,9,768,48,32] 13 bound_49).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 772 56 80 48 224 224 480 736), lower := (rows 7 11 772 56 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 11 10 46 8 0 32 104 168 296 552), good := (rows 7 975 772 1007 64 996 64 128 256 512) }] }

theorem upper_51 : Upper D R [6,9,768,48,64,16] 13 :=
  bound_sound D R [6,9,768,48,64,16] 13 bound_51
    ((Boolean.boundCheck_true D R [6,9,768,48,64,16] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 176 176 176 192 0 0 0 0 0 0), upper := (rows 7 11 772 56 80 96 240 176 432 688), lower := (rows 7 11 772 56 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 11 10 14 8 16 32 0 136 264 520), good := (rows 7 911 772 959 16 32 0 128 256 512) }] }

theorem upper_52 : Upper D R [6,9,768,48,64,64] 13 :=
  bound_sound D R [6,9,768,48,64,64] 13 bound_52
    ((Boolean.boundCheck_true D R [6,9,768,48,64,64] 13 bound_52).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 11 772 56 80 160 80 224 480 736), lower := (rows 7 11 772 56 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 11 10 92 8 0 248 64 208 336 592), good := (rows 7 47 772 943 996 160 996 160 256 512) }] }

theorem upper_54 : Upper D R [6,9,768,48,64,128,16] 13 :=
  bound_sound D R [6,9,768,48,64,128,16] 13 bound_54
    ((Boolean.boundCheck_true D R [6,9,768,48,64,128,16] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 11 772 56 80 160 96 208 464 720), lower := (rows 7 11 772 56 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 11 10 92 8 80 0 64 208 336 592), good := (rows 7 15 772 927 980 128 980 128 256 512) }] }

theorem upper_55 : Upper D R [6,9,768,48,64,128,32] 13 :=
  bound_sound D R [6,9,768,48,64,128,32] 13 bound_55
    ((Boolean.boundCheck_true D R [6,9,768,48,64,128,32] 13 bound_55).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 240 240 240 128 0 0 0 0 0 0), upper := (rows 7 11 772 56 80 160 192 240 368 624), lower := (rows 7 11 772 56 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 4 24 16 224 0 128 256 512), good := (rows 7 11 772 56 56 160 160 160 256 512) }] }

theorem upper_56 : Upper D R [6,9,768,48,64,128,128] 13 :=
  bound_sound D R [6,9,768,48,64,128,128] 13 bound_56
    ((Boolean.boundCheck_true D R [6,9,768,48,64,128,128] 13 bound_56).mp (by decide +kernel))

def route_53 : Route 10 := (fun mask => (mask,id))

theorem upper_53 : Upper D R [6,9,768,48,64,128] 13 := by
  apply routed_branch D R [6,9,768,48,64,128] 13 (by decide) (choices 1) [16,32,128] route_53
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,768,48,64,128] (choices 1) [16,32,128] route_53).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_54
  · exact upper_55
  · exact upper_56

def route_50 : Route 10 := (fun mask => (mask,id))

theorem upper_50 : Upper D R [6,9,768,48,64] 13 := by
  apply routed_branch D R [6,9,768,48,64] 13 (by decide) (choices 1) [16,64,128] route_50
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,768,48,64] (choices 1) [16,64,128] route_50).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_51
  · exact upper_52
  · exact upper_53

def route_48 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_48 : Upper D R [6,9,768,48] 13 := by
  apply routed_branch D R [6,9,768,48] 13 (by decide) (choices 1) [32,64] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,9,768,48] (choices 1) [32,64] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_49
  · exact upper_50

def route_47 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_47 : Upper D R [6,9,768] 13 := by
  apply routed_branch D R [6,9,768] 13 (by decide) (choices 2) [48] route_47
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,9,768] (choices 2) [48] route_47).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_48

def route_0 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 544 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 320 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 576 => (272,(fun i => match i.val with | 4 => 6 | 6 => 4 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 640 => (272,(fun i => match i.val with | 4 => 7 | 7 => 4 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [6,9] 13 := by
  apply routed_branch D R [6,9] 13 (by decide) (choices 2) [48,272,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,9] (choices 2) [48,272,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_1
  · exact upper_16
  · exact upper_47

theorem upper : Upper D R [6,9] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case00
