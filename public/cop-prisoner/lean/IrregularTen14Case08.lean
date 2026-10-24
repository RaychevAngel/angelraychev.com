import IrregularTen14Base

namespace Delivery.IrregularTen14.Case08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 7 28 104 1008 992 992 992 992 992), lower := (rows 19 7 28 104 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,5,24,96] 13 :=
  bound_sound D R [18,5,24,96] 13 bound_2
    ((Boolean.boundCheck_true D R [18,5,24,96] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 7 28 296 752 736 736 736 992 736), lower := (rows 19 7 28 296 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,5,24,288] 13 :=
  bound_sound D R [18,5,24,288] 13 bound_3
    ((Boolean.boundCheck_true D R [18,5,24,288] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 19 7 28 776 240 224 224 224 480 736), lower := (rows 19 7 28 776 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 1023 0 1023 1023 1023 1023 1023), good := (rows 1003 1007 1004 1000 1000 1000 1000 1000 1000 1000) }] }

theorem upper_4 : Upper D R [18,5,24,768] 13 :=
  bound_sound D R [18,5,24,768] 13 bound_4
    ((Boolean.boundCheck_true D R [18,5,24,768] 13 bound_4).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,5,24] 13 := by
  apply routed_branch D R [18,5,24] 13 (by decide) (choices 2) [96,288,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,24] (choices 2) [96,288,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4

def bound_6 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 7 44 56 976 992 960 960 960 960), lower := (rows 19 7 44 56 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,5,40,48] 13 :=
  bound_sound D R [18,5,40,48] 13 bound_6
    ((Boolean.boundCheck_true D R [18,5,40,48] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 7 44 88 1008 992 992 992 992 992), lower := (rows 19 7 44 88 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,5,40,80] 13 :=
  bound_sound D R [18,5,40,80] 13 bound_7
    ((Boolean.boundCheck_true D R [18,5,40,80] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 7 44 104 976 1008 976 976 976 976), lower := (rows 19 7 44 104 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,5,40,96] 13 :=
  bound_sound D R [18,5,40,96] 13 bound_8
    ((Boolean.boundCheck_true D R [18,5,40,96] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 7 44 200 1008 1008 1008 1008 1008 1008), lower := (rows 19 7 44 200 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [18,5,40,192] 13 :=
  bound_sound D R [18,5,40,192] 13 bound_9
    ((Boolean.boundCheck_true D R [18,5,40,192] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 7 44 280 752 736 736 736 992 736), lower := (rows 19 7 44 280 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,5,40,272] 13 :=
  bound_sound D R [18,5,40,272] 13 bound_10
    ((Boolean.boundCheck_true D R [18,5,40,272] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 7 44 296 720 752 720 720 976 720), lower := (rows 19 7 44 296 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [18,5,40,288] 13 :=
  bound_sound D R [18,5,40,288] 13 bound_11
    ((Boolean.boundCheck_true D R [18,5,40,288] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 7 44 328 752 752 752 752 1008 752), lower := (rows 19 7 44 328 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [18,5,40,320] 13 :=
  bound_sound D R [18,5,40,320] 13 bound_12
    ((Boolean.boundCheck_true D R [18,5,40,320] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 7 44 776 48 240 208 208 464 720), lower := (rows 19 7 44 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 4 27 16 0 81 145 273 529), good := (rows 987 975 12 776 984 0 64 128 256 512) }] }

theorem upper_14 : Upper D R [18,5,40,768,32] 13 :=
  bound_sound D R [18,5,40,768,32] 13 bound_14
    ((Boolean.boundCheck_true D R [18,5,40,768,32] 13 bound_14).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 240 192 224 0 0 0 0 0 0), upper := (rows 19 7 44 776 80 48 224 224 480 736), lower := (rows 19 7 44 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 36 46 0 32 100 164 292 548), good := (rows 11 975 1004 776 64 1004 64 128 256 512) }] }

theorem upper_16 : Upper D R [18,5,40,768,64,16] 13 :=
  bound_sound D R [18,5,40,768,64,16] 13 bound_16
    ((Boolean.boundCheck_true D R [18,5,40,768,64,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 7 44 776 80 96 240 176 432 688), lower := (rows 19 7 44 776 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 5 6 4 8 112 0 64 128 256 512), good := (rows 19 7 31 776 80 80 80 128 256 512) }] }

theorem upper_17 : Upper D R [18,5,40,768,64,64] 13 :=
  bound_sound D R [18,5,40,768,64,64] 13 bound_17
    ((Boolean.boundCheck_true D R [18,5,40,768,64,64] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 7 44 776 80 160 80 224 480 736), lower := (rows 19 7 44 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 87 89 0 241 64 208 336 592), good := (rows 943 47 44 776 1004 160 1004 160 256 512) }] }

theorem upper_19 : Upper D R [18,5,40,768,64,128,16] 13 :=
  bound_sound D R [18,5,40,768,64,128,16] 13 bound_19
    ((Boolean.boundCheck_true D R [18,5,40,768,64,128,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 7 44 776 80 160 96 208 464 720), lower := (rows 19 7 44 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 4 89 80 0 64 208 336 592), good := (rows 923 15 12 776 984 128 984 128 256 512) }] }

theorem upper_20 : Upper D R [18,5,40,768,64,128,32] 13 :=
  bound_sound D R [18,5,40,768,64,128,32] 13 bound_20
    ((Boolean.boundCheck_true D R [18,5,40,768,64,128,32] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 192 208 208 240 0 0 0 0 0 0), upper := (rows 19 7 44 776 80 160 192 240 368 624), lower := (rows 19 7 44 776 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 7 6 4 8 244 0 224 128 256 512), good := (rows 19 23 95 776 80 208 208 208 256 512) }] }

theorem upper_21 : Upper D R [18,5,40,768,64,128,128] 13 :=
  bound_sound D R [18,5,40,768,64,128,128] 13 bound_21
    ((Boolean.boundCheck_true D R [18,5,40,768,64,128,128] 13 bound_21).mp (by decide +kernel))

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [18,5,40,768,64,128] 13 := by
  apply routed_branch D R [18,5,40,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,40,768,64,128] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [18,5,40,768,64] 13 := by
  apply routed_branch D R [18,5,40,768,64] 13 (by decide) (choices 1) [16,64,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,40,768,64] (choices 1) [16,64,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_13 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_13 : Upper D R [18,5,40,768] 13 := by
  apply routed_branch D R [18,5,40,768] 13 (by decide) (choices 1) [32,64] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,40,768] (choices 1) [32,64] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def route_5 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [18,5,40] 13 := by
  apply routed_branch D R [18,5,40] 13 (by decide) (choices 2) [48,80,96,192,272,288,320,768] route_5
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,40] (choices 2) [48,80,96,192,272,288,320,768] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_6
  · exact upper_7
  · exact upper_8
  · exact upper_9
  · exact upper_10
  · exact upper_11
  · exact upper_12
  · exact upper_13

def bound_22 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 7 52 1000 1016 1000 1000 1000 1000 1000), lower := (rows 19 7 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [18,5,48] 13 :=
  bound_sound D R [18,5,48] 13 bound_22
    ((Boolean.boundCheck_true D R [18,5,48] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 19 7 100 1016 1016 1016 1016 1016 1016 1016), lower := (rows 19 7 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [18,5,96] 13 :=
  bound_sound D R [18,5,96] 13 bound_23
    ((Boolean.boundCheck_true D R [18,5,96] 13 bound_23).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 7 268 56 752 736 736 736 992 736), lower := (rows 19 7 268 56 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [18,5,264,48] 13 :=
  bound_sound D R [18,5,264,48] 13 bound_25
    ((Boolean.boundCheck_true D R [18,5,264,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 7 268 104 752 752 752 752 1008 752), lower := (rows 19 7 268 104 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,5,264,96] 13 :=
  bound_sound D R [18,5,264,96] 13 bound_26
    ((Boolean.boundCheck_true D R [18,5,264,96] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 19 7 268 536 240 224 224 224 480 736), lower := (rows 19 7 268 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 12 8 0 1023 1023 1023 1023 1023), good := (rows 995 999 1004 1004 992 992 992 992 992 992) }] }

theorem upper_27 : Upper D R [18,5,264,528] 13 :=
  bound_sound D R [18,5,264,528] 13 bound_27
    ((Boolean.boundCheck_true D R [18,5,264,528] 13 bound_27).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 160 176 240 208 0 0 0 0 0 0), upper := (rows 19 7 268 552 48 240 208 208 464 720), lower := (rows 19 7 268 552 48 32 64 128 256 512), losses := [{ target := 6, region := (rows 5 6 4 8 56 32 0 128 256 512), good := (rows 19 7 287 568 48 48 0 128 256 512) }] }

theorem upper_29 : Upper D R [18,5,264,544,32] 13 :=
  bound_sound D R [18,5,264,544,32] 13 bound_29
    ((Boolean.boundCheck_true D R [18,5,264,544,32] 13 bound_29).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 224 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 48 224 224 480 736), lower := (rows 19 7 268 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 44 40 0 32 104 168 296 552), good := (rows 3 7 972 1004 64 1004 64 128 256 512) }] }

theorem upper_31 : Upper D R [18,5,264,544,64,16] 13 :=
  bound_sound D R [18,5,264,544,64,16] 13 bound_31
    ((Boolean.boundCheck_true D R [18,5,264,544,64,16] 13 bound_31).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 96 80 160 416 672), lower := (rows 19 7 268 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 127 121 0 112 64 249 377 633), good := (rows 943 911 908 940 1004 1004 1004 128 256 512) }] }

theorem upper_33 : Upper D R [18,5,264,544,64,64,16] 13 :=
  bound_sound D R [18,5,264,544,64,64,16] 13 bound_33
    ((Boolean.boundCheck_true D R [18,5,264,544,64,64,16] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 96 96 144 400 656), lower := (rows 19 7 268 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 99 103 364 616 96 96 96 224 352 616) }] }

theorem upper_34 : Upper D R [18,5,264,544,64,64,32] 13 :=
  bound_sound D R [18,5,264,544,64,64,32] 13 bound_34
    ((Boolean.boundCheck_true D R [18,5,264,544,64,64,32] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 96 192 144 416 672), lower := (rows 19 7 268 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 3 244 248 0 240 192 128 448 704), good := (rows 47 7 268 556 876 876 1004 1004 256 512) }] }

theorem upper_36 : Upper D R [18,5,264,544,64,64,128,16] 13 :=
  bound_sound D R [18,5,264,544,64,64,128,16] 13 bound_36
    ((Boolean.boundCheck_true D R [18,5,264,544,64,64,128,16] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 96 192 160 400 656), lower := (rows 19 7 268 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 227 231 492 744 224 224 224 224 480 744) }] }

theorem upper_37 : Upper D R [18,5,264,544,64,64,128,32] 13 :=
  bound_sound D R [18,5,264,544,64,64,128,32] 13 bound_37
    ((Boolean.boundCheck_true D R [18,5,264,544,64,64,128,32] 13 bound_37).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => (mask,id))

theorem upper_35 : Upper D R [18,5,264,544,64,64,128] 13 := by
  apply routed_branch D R [18,5,264,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,264,544,64,64,128] (choices 1) [16,32] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_36
  · exact upper_37

def route_32 : Route 10 := (fun mask => (mask,id))

theorem upper_32 : Upper D R [18,5,264,544,64,64] 13 := by
  apply routed_branch D R [18,5,264,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,264,544,64,64] (choices 1) [16,32,128] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_35

def bound_39 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 160 80 224 480 736), lower := (rows 19 7 268 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 3 85 89 0 241 64 208 336 592), good := (rows 943 47 268 552 1004 160 1004 160 256 512) }] }

theorem upper_39 : Upper D R [18,5,264,544,64,128,16] 13 :=
  bound_sound D R [18,5,264,544,64,128,16] 13 bound_39
    ((Boolean.boundCheck_true D R [18,5,264,544,64,128,16] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 96 112 240 208 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 160 96 208 464 720), lower := (rows 19 7 268 552 80 160 96 128 256 512), losses := [{ target := 7, region := (rows 7 6 4 8 124 32 104 0 256 512), good := (rows 19 23 351 632 80 112 112 0 256 512) }] }

theorem upper_40 : Upper D R [18,5,264,544,64,128,32] 13 :=
  bound_sound D R [18,5,264,544,64,128,32] 13 bound_40
    ((Boolean.boundCheck_true D R [18,5,264,544,64,128,32] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 192 208 240 208 0 0 0 0 0 0), upper := (rows 19 7 268 552 80 160 192 240 368 624), lower := (rows 19 7 268 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 5 6 4 8 248 0 224 128 256 512), good := (rows 19 7 287 600 80 208 208 208 256 512) }] }

theorem upper_41 : Upper D R [18,5,264,544,64,128,128] 13 :=
  bound_sound D R [18,5,264,544,64,128,128] 13 bound_41
    ((Boolean.boundCheck_true D R [18,5,264,544,64,128,128] 13 bound_41).mp (by decide +kernel))

def route_38 : Route 10 := (fun mask => (mask,id))

theorem upper_38 : Upper D R [18,5,264,544,64,128] 13 := by
  apply routed_branch D R [18,5,264,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_38
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,264,544,64,128] (choices 1) [16,32,128] route_38).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_39
  · exact upper_40
  · exact upper_41

def route_30 : Route 10 := (fun mask => (mask,id))

theorem upper_30 : Upper D R [18,5,264,544,64] 13 := by
  apply routed_branch D R [18,5,264,544,64] 13 (by decide) (choices 1) [16,64,128] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,264,544,64] (choices 1) [16,64,128] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_31
  · exact upper_32
  · exact upper_38

def route_28 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_28 : Upper D R [18,5,264,544] 13 := by
  apply routed_branch D R [18,5,264,544] 13 (by decide) (choices 1) [32,64] route_28
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,5,264,544] (choices 1) [32,64] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_29
  · exact upper_30

def route_24 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_24 : Upper D R [18,5,264] 13 := by
  apply routed_branch D R [18,5,264] 13 (by decide) (choices 2) [48,96,528,544] route_24
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,264] (choices 2) [48,96,528,544] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28

def bound_43 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 7 276 104 760 744 744 744 1000 744), lower := (rows 19 7 276 104 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [18,5,272,96] 13 :=
  bound_sound D R [18,5,272,96] 13 bound_43
    ((Boolean.boundCheck_true D R [18,5,272,96] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 7 276 552 248 232 232 232 488 744), lower := (rows 19 7 276 552 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [18,5,272,544] 13 :=
  bound_sound D R [18,5,272,544] 13 bound_44
    ((Boolean.boundCheck_true D R [18,5,272,544] 13 bound_44).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_42 : Upper D R [18,5,272] 13 := by
  apply routed_branch D R [18,5,272] 13 (by decide) (choices 2) [96,544] route_42
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,272] (choices 2) [96,544] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_43
  · exact upper_44

def bound_46 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 7 292 56 728 744 712 712 968 712), lower := (rows 19 7 292 56 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [18,5,288,48] 13 :=
  bound_sound D R [18,5,288,48] 13 bound_46
    ((Boolean.boundCheck_true D R [18,5,288,48] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 7 292 88 760 744 744 744 1000 744), lower := (rows 19 7 292 88 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [18,5,288,80] 13 :=
  bound_sound D R [18,5,288,80] 13 bound_47
    ((Boolean.boundCheck_true D R [18,5,288,80] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 7 292 104 728 760 728 728 984 728), lower := (rows 19 7 292 104 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [18,5,288,96] 13 :=
  bound_sound D R [18,5,288,96] 13 bound_48
    ((Boolean.boundCheck_true D R [18,5,288,96] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 7 292 200 760 760 760 760 1016 760), lower := (rows 19 7 292 200 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [18,5,288,192] 13 :=
  bound_sound D R [18,5,288,192] 13 bound_49
    ((Boolean.boundCheck_true D R [18,5,288,192] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 7 292 536 248 232 232 232 488 744), lower := (rows 19 7 292 536 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [18,5,288,528] 13 :=
  bound_sound D R [18,5,288,528] 13 bound_50
    ((Boolean.boundCheck_true D R [18,5,288,528] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 7 292 552 216 248 216 216 472 728), lower := (rows 19 7 292 552 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [18,5,288,544] 13 :=
  bound_sound D R [18,5,288,544] 13 bound_51
    ((Boolean.boundCheck_true D R [18,5,288,544] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 7 292 584 248 248 248 248 504 760), lower := (rows 19 7 292 584 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [18,5,288,576] 13 :=
  bound_sound D R [18,5,288,576] 13 bound_52
    ((Boolean.boundCheck_true D R [18,5,288,576] 13 bound_52).mp (by decide +kernel))

def route_45 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_45 : Upper D R [18,5,288] 13 := by
  apply routed_branch D R [18,5,288] 13 (by decide) (choices 2) [48,80,96,192,528,544,576] route_45
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,288] (choices 2) [48,80,96,192,528,544,576] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52

def bound_54 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 7 772 56 248 232 232 232 488 744), lower := (rows 19 7 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [18,5,768,48] 13 :=
  bound_sound D R [18,5,768,48] 13 bound_54
    ((Boolean.boundCheck_true D R [18,5,768,48] 13 bound_54).mp (by decide +kernel))

def bound_55 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 7 772 104 248 248 248 248 504 760), lower := (rows 19 7 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_55 : Upper D R [18,5,768,96] 13 :=
  bound_sound D R [18,5,768,96] 13 bound_55
    ((Boolean.boundCheck_true D R [18,5,768,96] 13 bound_55).mp (by decide +kernel))

def route_53 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_53 : Upper D R [18,5,768] 13 := by
  apply routed_branch D R [18,5,768] 13 (by decide) (choices 2) [48,96] route_53
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5,768] (choices 2) [48,96] route_53).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_54
  · exact upper_55

def route_0 : Route 10 := (fun mask => match mask with | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 520 => (264,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,5] 13 := by
  apply routed_branch D R [18,5] 13 (by decide) (choices 2) [24,40,48,96,264,272,288,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,5] (choices 2) [24,40,48,96,264,272,288,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_5
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_42
  · exact upper_45
  · exact upper_53

theorem upper : Upper D R [18,5] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case08
