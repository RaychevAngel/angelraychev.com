import IrregularTen14Base

namespace Delivery.IrregularTen14.Case09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 14 21 104 1008 992 992 992 992 992), lower := (rows 19 14 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [18,12,17,96] 13 :=
  bound_sound D R [18,12,17,96] 13 bound_2
    ((Boolean.boundCheck_true D R [18,12,17,96] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 14 21 296 752 736 736 736 992 736), lower := (rows 19 14 21 296 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [18,12,17,288] 13 :=
  bound_sound D R [18,12,17,288] 13 bound_3
    ((Boolean.boundCheck_true D R [18,12,17,288] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 14 21 776 240 224 224 224 480 736), lower := (rows 19 14 21 776 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 1023 0 1023 1023 1023 1023 1023), good := (rows 1003 1006 1007 1000 1000 1000 1000 1000 1000 1000) }] }

theorem upper_4 : Upper D R [18,12,17,768] 13 :=
  bound_sound D R [18,12,17,768] 13 bound_4
    ((Boolean.boundCheck_true D R [18,12,17,768] 13 bound_4).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [18,12,17] 13 := by
  apply routed_branch D R [18,12,17] 13 (by decide) (choices 2) [96,288,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,17] (choices 2) [96,288,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4

def bound_6 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 14 37 56 976 992 960 960 960 960), lower := (rows 19 14 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [18,12,33,48] 13 :=
  bound_sound D R [18,12,33,48] 13 bound_6
    ((Boolean.boundCheck_true D R [18,12,33,48] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 14 37 88 1008 992 992 992 992 992), lower := (rows 19 14 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [18,12,33,80] 13 :=
  bound_sound D R [18,12,33,80] 13 bound_7
    ((Boolean.boundCheck_true D R [18,12,33,80] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 14 37 104 976 1008 976 976 976 976), lower := (rows 19 14 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [18,12,33,96] 13 :=
  bound_sound D R [18,12,33,96] 13 bound_8
    ((Boolean.boundCheck_true D R [18,12,33,96] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 14 37 200 1008 1008 1008 1008 1008 1008), lower := (rows 19 14 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [18,12,33,192] 13 :=
  bound_sound D R [18,12,33,192] 13 bound_9
    ((Boolean.boundCheck_true D R [18,12,33,192] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 14 37 280 752 736 736 736 992 736), lower := (rows 19 14 37 280 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [18,12,33,272] 13 :=
  bound_sound D R [18,12,33,272] 13 bound_10
    ((Boolean.boundCheck_true D R [18,12,33,272] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 37 296 720 752 720 720 976 720), lower := (rows 19 14 37 296 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [18,12,33,288] 13 :=
  bound_sound D R [18,12,33,288] 13 bound_11
    ((Boolean.boundCheck_true D R [18,12,33,288] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 14 37 328 752 752 752 752 1008 752), lower := (rows 19 14 37 328 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [18,12,33,320] 13 :=
  bound_sound D R [18,12,33,320] 13 bound_12
    ((Boolean.boundCheck_true D R [18,12,33,320] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 14 37 776 48 240 208 208 464 720), lower := (rows 19 14 37 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 29 16 0 81 145 273 529), good := (rows 987 14 975 776 984 0 64 128 256 512) }] }

theorem upper_14 : Upper D R [18,12,33,768,32] 13 :=
  bound_sound D R [18,12,33,768,32] 13 bound_14
    ((Boolean.boundCheck_true D R [18,12,33,768,32] 13 bound_14).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 224 224 208 224 0 0 0 0 0 0), upper := (rows 19 14 37 776 80 48 224 224 480 736), lower := (rows 19 14 37 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 6 4 46 0 32 100 164 292 548), good := (rows 11 974 1007 776 64 1000 64 128 256 512) }] }

theorem upper_16 : Upper D R [18,12,33,768,64,16] 13 :=
  bound_sound D R [18,12,33,768,64,16] 13 bound_16
    ((Boolean.boundCheck_true D R [18,12,33,768,64,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 37 776 80 96 240 176 432 688), lower := (rows 19 14 37 776 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 112 64 128 256 512), good := (rows 39 14 37 776 96 96 96 128 256 512) }] }

theorem upper_17 : Upper D R [18,12,33,768,64,64] 13 :=
  bound_sound D R [18,12,33,768,64,64] 13 bound_17
    ((Boolean.boundCheck_true D R [18,12,33,768,64,64] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 14 37 776 80 160 80 224 480 736), lower := (rows 19 14 37 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 89 0 241 64 208 336 592), good := (rows 943 14 47 776 1000 160 1000 160 256 512) }] }

theorem upper_19 : Upper D R [18,12,33,768,64,128,16] 13 :=
  bound_sound D R [18,12,33,768,64,128,16] 13 bound_19
    ((Boolean.boundCheck_true D R [18,12,33,768,64,128,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 14 37 776 80 160 96 208 464 720), lower := (rows 19 14 37 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 6 4 89 80 0 64 208 336 592), good := (rows 923 14 15 776 984 128 984 128 256 512) }] }

theorem upper_20 : Upper D R [18,12,33,768,64,128,32] 13 :=
  bound_sound D R [18,12,33,768,64,128,32] 13 bound_20
    ((Boolean.boundCheck_true D R [18,12,33,768,64,128,32] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 19 14 37 776 80 160 192 240 368 624), lower := (rows 19 14 37 776 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 244 0 224 128 256 512), good := (rows 19 31 85 776 80 208 208 208 256 512) }] }

theorem upper_21 : Upper D R [18,12,33,768,64,128,128] 13 :=
  bound_sound D R [18,12,33,768,64,128,128] 13 bound_21
    ((Boolean.boundCheck_true D R [18,12,33,768,64,128,128] 13 bound_21).mp (by decide +kernel))

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [18,12,33,768,64,128] 13 := by
  apply routed_branch D R [18,12,33,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,33,768,64,128] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [18,12,33,768,64] 13 := by
  apply routed_branch D R [18,12,33,768,64] 13 (by decide) (choices 1) [16,64,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,33,768,64] (choices 1) [16,64,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_13 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_13 : Upper D R [18,12,33,768] 13 := by
  apply routed_branch D R [18,12,33,768] 13 (by decide) (choices 1) [32,64] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,33,768] (choices 1) [32,64] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def route_5 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [18,12,33] 13 := by
  apply routed_branch D R [18,12,33] 13 (by decide) (choices 2) [48,80,96,192,272,288,320,768] route_5
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,33] (choices 2) [48,80,96,192,272,288,320,768] route_5).mp (by decide +kernel))
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

def bound_22 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 52 1001 1009 993 993 993 993 993), lower := (rows 19 14 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [18,12,48] 13 :=
  bound_sound D R [18,12,48] 13 bound_22
    ((Boolean.boundCheck_true D R [18,12,48] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 240 144 240 0 0 0 0 0 0), upper := (rows 19 14 100 1017 1009 1009 1009 1009 1009 1009), lower := (rows 19 14 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [18,12,96] 13 :=
  bound_sound D R [18,12,96] 13 bound_23
    ((Boolean.boundCheck_true D R [18,12,96] 13 bound_23).mp (by decide +kernel))

def bound_25 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 261 56 752 736 736 736 992 736), lower := (rows 19 14 261 56 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [18,12,257,48] 13 :=
  bound_sound D R [18,12,257,48] 13 bound_25
    ((Boolean.boundCheck_true D R [18,12,257,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 14 261 104 752 752 752 752 1008 752), lower := (rows 19 14 261 104 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [18,12,257,96] 13 :=
  bound_sound D R [18,12,257,96] 13 bound_26
    ((Boolean.boundCheck_true D R [18,12,257,96] 13 bound_26).mp (by decide +kernel))

def bound_27 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 19 14 261 536 240 224 224 224 480 736), lower := (rows 19 14 261 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 5 8 0 1023 1023 1023 1023 1023), good := (rows 999 1006 997 1000 992 992 992 992 992 992) }] }

theorem upper_27 : Upper D R [18,12,257,528] 13 :=
  bound_sound D R [18,12,257,528] 13 bound_27
    ((Boolean.boundCheck_true D R [18,12,257,528] 13 bound_27).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 261 552 48 240 208 208 464 720), lower := (rows 19 14 261 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 81 145 273 529), good := (rows 983 14 965 520 976 0 64 128 256 512) }] }

theorem upper_29 : Upper D R [18,12,257,544,32] 13 :=
  bound_sound D R [18,12,257,544,32] 13 bound_29
    ((Boolean.boundCheck_true D R [18,12,257,544,32] 13 bound_29).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 48 224 224 480 736), lower := (rows 19 14 261 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 40 0 32 104 168 296 552), good := (rows 3 974 261 1000 64 1000 64 128 256 512) }] }

theorem upper_31 : Upper D R [18,12,257,544,64,16] 13 :=
  bound_sound D R [18,12,257,544,64,16] 13 bound_31
    ((Boolean.boundCheck_true D R [18,12,257,544,64,16] 13 bound_31).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 96 80 160 416 672), lower := (rows 19 14 261 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 121 0 112 64 249 377 633), good := (rows 943 910 911 936 1000 1000 1000 128 256 512) }] }

theorem upper_33 : Upper D R [18,12,257,544,64,64,16] 13 :=
  bound_sound D R [18,12,257,544,64,64,16] 13 bound_33
    ((Boolean.boundCheck_true D R [18,12,257,544,64,64,16] 13 bound_33).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 96 96 144 400 656), lower := (rows 19 14 261 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 99 110 357 616 96 96 96 224 352 616) }] }

theorem upper_34 : Upper D R [18,12,257,544,64,64,32] 13 :=
  bound_sound D R [18,12,257,544,64,64,32] 13 bound_34
    ((Boolean.boundCheck_true D R [18,12,257,544,64,64,32] 13 bound_34).mp (by decide +kernel))

def bound_36 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 96 192 144 416 672), lower := (rows 19 14 261 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 248 0 240 192 128 448 704), good := (rows 43 14 261 552 872 872 1000 1000 256 512) }] }

theorem upper_36 : Upper D R [18,12,257,544,64,64,128,16] 13 :=
  bound_sound D R [18,12,257,544,64,64,128,16] 13 bound_36
    ((Boolean.boundCheck_true D R [18,12,257,544,64,64,128,16] 13 bound_36).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 96 192 160 400 656), lower := (rows 19 14 261 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 227 238 485 744 224 224 224 224 480 744) }] }

theorem upper_37 : Upper D R [18,12,257,544,64,64,128,32] 13 :=
  bound_sound D R [18,12,257,544,64,64,128,32] 13 bound_37
    ((Boolean.boundCheck_true D R [18,12,257,544,64,64,128,32] 13 bound_37).mp (by decide +kernel))

def route_35 : Route 10 := (fun mask => (mask,id))

theorem upper_35 : Upper D R [18,12,257,544,64,64,128] 13 := by
  apply routed_branch D R [18,12,257,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_35
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,257,544,64,64,128] (choices 1) [16,32] route_35).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_36
  · exact upper_37

def route_32 : Route 10 := (fun mask => (mask,id))

theorem upper_32 : Upper D R [18,12,257,544,64,64] 13 := by
  apply routed_branch D R [18,12,257,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_32
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,257,544,64,64] (choices 1) [16,32,128] route_32).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_33
  · exact upper_34
  · exact upper_35

def bound_39 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 160 80 224 480 736), lower := (rows 19 14 261 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 7 5 89 0 241 64 208 336 592), good := (rows 943 14 303 552 1000 160 1000 160 256 512) }] }

theorem upper_39 : Upper D R [18,12,257,544,64,128,16] 13 :=
  bound_sound D R [18,12,257,544,64,128,16] 13 bound_39
    ((Boolean.boundCheck_true D R [18,12,257,544,64,128,16] 13 bound_39).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 160 96 208 464 720), lower := (rows 19 14 261 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 5 8 80 0 64 208 336 592), good := (rows 919 14 261 520 976 128 976 128 256 512) }] }

theorem upper_40 : Upper D R [18,12,257,544,64,128,32] 13 :=
  bound_sound D R [18,12,257,544,64,128,32] 13 bound_40
    ((Boolean.boundCheck_true D R [18,12,257,544,64,128,32] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 19 14 261 552 80 160 192 240 368 624), lower := (rows 19 14 261 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 248 0 224 128 256 512), good := (rows 19 31 261 600 80 208 208 208 256 512) }] }

theorem upper_41 : Upper D R [18,12,257,544,64,128,128] 13 :=
  bound_sound D R [18,12,257,544,64,128,128] 13 bound_41
    ((Boolean.boundCheck_true D R [18,12,257,544,64,128,128] 13 bound_41).mp (by decide +kernel))

def route_38 : Route 10 := (fun mask => (mask,id))

theorem upper_38 : Upper D R [18,12,257,544,64,128] 13 := by
  apply routed_branch D R [18,12,257,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_38
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,257,544,64,128] (choices 1) [16,32,128] route_38).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_39
  · exact upper_40
  · exact upper_41

def route_30 : Route 10 := (fun mask => (mask,id))

theorem upper_30 : Upper D R [18,12,257,544,64] 13 := by
  apply routed_branch D R [18,12,257,544,64] 13 (by decide) (choices 1) [16,64,128] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,257,544,64] (choices 1) [16,64,128] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_31
  · exact upper_32
  · exact upper_38

def route_28 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_28 : Upper D R [18,12,257,544] 13 := by
  apply routed_branch D R [18,12,257,544] 13 (by decide) (choices 1) [32,64] route_28
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,257,544] (choices 1) [32,64] route_28).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_29
  · exact upper_30

def route_24 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_24 : Upper D R [18,12,257] 13 := by
  apply routed_branch D R [18,12,257] 13 (by decide) (choices 2) [48,96,528,544] route_24
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,257] (choices 2) [48,96,528,544] route_24).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_28

def bound_43 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 14 276 41 752 736 736 736 992 736), lower := (rows 19 14 276 41 16 32 64 128 256 512), losses := [] }

theorem upper_43 : Upper D R [18,12,272,33] 13 :=
  bound_sound D R [18,12,272,33] 13 bound_43
    ((Boolean.boundCheck_true D R [18,12,272,33] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 224 240 224 144 0 0 0 0 0 0), upper := (rows 19 14 276 104 753 737 737 737 993 737), lower := (rows 19 14 276 104 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [18,12,272,96] 13 :=
  bound_sound D R [18,12,272,96] 13 bound_44
    ((Boolean.boundCheck_true D R [18,12,272,96] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 224 240 224 224 0 0 0 0 0 0), upper := (rows 19 14 276 521 240 224 224 224 480 736), lower := (rows 19 14 276 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 1023 1023), good := (rows 1003 1006 996 1001 992 992 992 992 992 992) }] }

theorem upper_45 : Upper D R [18,12,272,513] 13 :=
  bound_sound D R [18,12,272,513] 13 bound_45
    ((Boolean.boundCheck_true D R [18,12,272,513] 13 bound_45).mp (by decide +kernel))

def bound_46 : Bound 10 := { allowed := (rows 224 240 224 208 0 0 0 0 0 0), upper := (rows 19 14 276 552 241 225 225 225 481 737), lower := (rows 19 14 276 552 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [18,12,272,544] 13 :=
  bound_sound D R [18,12,272,544] 13 bound_46
    ((Boolean.boundCheck_true D R [18,12,272,544] 13 bound_46).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_42 : Upper D R [18,12,272] 13 := by
  apply routed_branch D R [18,12,272] 13 (by decide) (choices 2) [33,96,513,544] route_42
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,272] (choices 2) [33,96,513,544] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45
  · exact upper_46

def bound_48 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 14 292 25 752 736 736 736 992 736), lower := (rows 19 14 292 25 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [18,12,288,17] 13 :=
  bound_sound D R [18,12,288,17] 13 bound_48
    ((Boolean.boundCheck_true D R [18,12,288,17] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 292 41 720 752 720 720 976 720), lower := (rows 19 14 292 41 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [18,12,288,33] 13 :=
  bound_sound D R [18,12,288,33] 13 bound_49
    ((Boolean.boundCheck_true D R [18,12,288,33] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 224 240 208 192 0 0 0 0 0 0), upper := (rows 19 14 292 56 721 737 705 705 961 705), lower := (rows 19 14 292 56 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [18,12,288,48] 13 :=
  bound_sound D R [18,12,288,48] 13 bound_50
    ((Boolean.boundCheck_true D R [18,12,288,48] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 14 292 73 752 752 752 752 1008 752), lower := (rows 19 14 292 73 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [18,12,288,65] 13 :=
  bound_sound D R [18,12,288,65] 13 bound_51
    ((Boolean.boundCheck_true D R [18,12,288,65] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 224 240 208 160 0 0 0 0 0 0), upper := (rows 19 14 292 88 753 737 737 737 993 737), lower := (rows 19 14 292 88 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [18,12,288,80] 13 :=
  bound_sound D R [18,12,288,80] 13 bound_52
    ((Boolean.boundCheck_true D R [18,12,288,80] 13 bound_52).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 240 208 144 0 0 0 0 0 0), upper := (rows 19 14 292 104 721 753 721 721 977 721), lower := (rows 19 14 292 104 16 32 64 128 256 512), losses := [] }

theorem upper_53 : Upper D R [18,12,288,96] 13 :=
  bound_sound D R [18,12,288,96] 13 bound_53
    ((Boolean.boundCheck_true D R [18,12,288,96] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 224 240 208 48 0 0 0 0 0 0), upper := (rows 19 14 292 200 753 753 753 753 1009 753), lower := (rows 19 14 292 200 16 32 64 128 256 512), losses := [] }

theorem upper_54 : Upper D R [18,12,288,192] 13 :=
  bound_sound D R [18,12,288,192] 13 bound_54
    ((Boolean.boundCheck_true D R [18,12,288,192] 13 bound_54).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 292 521 48 240 208 208 464 720), lower := (rows 19 14 292 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 81 145 273 529), good := (rows 987 14 260 969 976 0 64 128 256 512) }] }

theorem upper_56 : Upper D R [18,12,288,513,32] 13 :=
  bound_sound D R [18,12,288,513,32] 13 bound_56
    ((Boolean.boundCheck_true D R [18,12,288,513,32] 13 bound_56).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 48 224 224 480 736), lower := (rows 19 14 292 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 36 8 0 32 100 164 292 548), good := (rows 3 974 996 521 64 996 64 128 256 512) }] }

theorem upper_58 : Upper D R [18,12,288,513,64,16] 13 :=
  bound_sound D R [18,12,288,513,64,16] 13 bound_58
    ((Boolean.boundCheck_true D R [18,12,288,513,64,16] 13 bound_58).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 96 80 160 416 672), lower := (rows 19 14 292 521 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 117 9 0 112 64 245 373 629), good := (rows 943 910 932 911 996 996 996 128 256 512) }] }

theorem upper_60 : Upper D R [18,12,288,513,64,64,16] 13 :=
  bound_sound D R [18,12,288,513,64,64,16] 13 bound_60
    ((Boolean.boundCheck_true D R [18,12,288,513,64,64,16] 13 bound_60).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 96 96 144 400 656), lower := (rows 19 14 292 521 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 128 256 512), good := (rows 99 110 356 617 96 96 96 224 356 608) }] }

theorem upper_61 : Upper D R [18,12,288,513,64,64,32] 13 :=
  bound_sound D R [18,12,288,513,64,64,32] 13 bound_61
    ((Boolean.boundCheck_true D R [18,12,288,513,64,64,32] 13 bound_61).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 96 192 144 416 672), lower := (rows 19 14 292 521 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 244 8 0 240 192 128 448 704), good := (rows 39 14 292 521 868 868 996 996 256 512) }] }

theorem upper_63 : Upper D R [18,12,288,513,64,64,128,16] 13 :=
  bound_sound D R [18,12,288,513,64,64,128,16] 13 bound_63
    ((Boolean.boundCheck_true D R [18,12,288,513,64,64,128,16] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 224 240 192 240 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 96 192 160 400 656), lower := (rows 19 14 292 521 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 1023 256 512), good := (rows 227 238 484 745 224 224 224 224 484 736) }] }

theorem upper_64 : Upper D R [18,12,288,513,64,64,128,32] 13 :=
  bound_sound D R [18,12,288,513,64,64,128,32] 13 bound_64
    ((Boolean.boundCheck_true D R [18,12,288,513,64,64,128,32] 13 bound_64).mp (by decide +kernel))

def route_62 : Route 10 := (fun mask => (mask,id))

theorem upper_62 : Upper D R [18,12,288,513,64,64,128] 13 := by
  apply routed_branch D R [18,12,288,513,64,64,128] 13 (by decide) (choices 1) [16,32] route_62
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,288,513,64,64,128] (choices 1) [16,32] route_62).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_63
  · exact upper_64

def route_59 : Route 10 := (fun mask => (mask,id))

theorem upper_59 : Upper D R [18,12,288,513,64,64] 13 := by
  apply routed_branch D R [18,12,288,513,64,64] 13 (by decide) (choices 1) [16,32,128] route_59
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,288,513,64,64] (choices 1) [16,32,128] route_59).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_60
  · exact upper_61
  · exact upper_62

def bound_66 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 160 80 224 480 736), lower := (rows 19 14 292 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 85 9 0 241 64 208 336 592), good := (rows 943 14 292 559 996 160 996 160 256 512) }] }

theorem upper_66 : Upper D R [18,12,288,513,64,128,16] 13 :=
  bound_sound D R [18,12,288,513,64,128,16] 13 bound_66
    ((Boolean.boundCheck_true D R [18,12,288,513,64,128,16] 13 bound_66).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 160 96 208 464 720), lower := (rows 19 14 292 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 4 9 80 0 64 208 336 592), good := (rows 923 14 260 521 976 128 976 128 256 512) }] }

theorem upper_67 : Upper D R [18,12,288,513,64,128,32] 13 :=
  bound_sound D R [18,12,288,513,64,128,32] 13 bound_67
    ((Boolean.boundCheck_true D R [18,12,288,513,64,128,32] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 192 240 208 240 0 0 0 0 0 0), upper := (rows 19 14 292 521 80 160 192 240 368 624), lower := (rows 19 14 292 521 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 244 0 224 128 256 512), good := (rows 19 31 340 521 80 208 208 208 256 512) }] }

theorem upper_68 : Upper D R [18,12,288,513,64,128,128] 13 :=
  bound_sound D R [18,12,288,513,64,128,128] 13 bound_68
    ((Boolean.boundCheck_true D R [18,12,288,513,64,128,128] 13 bound_68).mp (by decide +kernel))

def route_65 : Route 10 := (fun mask => (mask,id))

theorem upper_65 : Upper D R [18,12,288,513,64,128] 13 := by
  apply routed_branch D R [18,12,288,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_65
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,288,513,64,128] (choices 1) [16,32,128] route_65).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_66
  · exact upper_67
  · exact upper_68

def route_57 : Route 10 := (fun mask => (mask,id))

theorem upper_57 : Upper D R [18,12,288,513,64] 13 := by
  apply routed_branch D R [18,12,288,513,64] 13 (by decide) (choices 1) [16,64,128] route_57
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,288,513,64] (choices 1) [16,64,128] route_57).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_58
  · exact upper_59
  · exact upper_65

def route_55 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_55 : Upper D R [18,12,288,513] 13 := by
  apply routed_branch D R [18,12,288,513] 13 (by decide) (choices 1) [32,64] route_55
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,288,513] (choices 1) [32,64] route_55).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_56
  · exact upper_57

def bound_69 : Bound 10 := { allowed := (rows 224 240 208 224 0 0 0 0 0 0), upper := (rows 19 14 292 536 241 225 225 225 481 737), lower := (rows 19 14 292 536 16 32 64 128 256 512), losses := [] }

theorem upper_69 : Upper D R [18,12,288,528] 13 :=
  bound_sound D R [18,12,288,528] 13 bound_69
    ((Boolean.boundCheck_true D R [18,12,288,528] 13 bound_69).mp (by decide +kernel))

def bound_70 : Bound 10 := { allowed := (rows 224 240 208 208 0 0 0 0 0 0), upper := (rows 19 14 292 552 209 241 209 209 465 721), lower := (rows 19 14 292 552 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [18,12,288,544] 13 :=
  bound_sound D R [18,12,288,544] 13 bound_70
    ((Boolean.boundCheck_true D R [18,12,288,544] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 224 240 208 176 0 0 0 0 0 0), upper := (rows 19 14 292 584 241 241 241 241 497 753), lower := (rows 19 14 292 584 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [18,12,288,576] 13 :=
  bound_sound D R [18,12,288,576] 13 bound_71
    ((Boolean.boundCheck_true D R [18,12,288,576] 13 bound_71).mp (by decide +kernel))

def route_47 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_47 : Upper D R [18,12,288] 13 := by
  apply routed_branch D R [18,12,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_47
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,288] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_47).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_54
  · exact upper_55
  · exact upper_69
  · exact upper_70
  · exact upper_71

def bound_73 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 19 14 772 25 240 224 224 224 480 736), lower := (rows 19 14 772 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 1023 8 0 1023 1023 1023 1023 1023), good := (rows 999 1006 996 1007 996 996 996 996 996 996) }] }

theorem upper_73 : Upper D R [18,12,768,17] 13 :=
  bound_sound D R [18,12,768,17] 13 bound_73
    ((Boolean.boundCheck_true D R [18,12,768,17] 13 bound_73).mp (by decide +kernel))

def bound_75 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 14 772 41 48 240 208 208 464 720), lower := (rows 19 14 772 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 10 29 8 16 0 81 145 273 529), good := (rows 983 14 772 975 980 0 64 128 256 512) }] }

theorem upper_75 : Upper D R [18,12,768,33,32] 13 :=
  bound_sound D R [18,12,768,33,32] 13 bound_75
    ((Boolean.boundCheck_true D R [18,12,768,33,32] 13 bound_75).mp (by decide +kernel))

def bound_77 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 19 14 772 41 80 48 224 224 480 736), lower := (rows 19 14 772 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 46 8 0 32 104 168 296 552), good := (rows 7 974 772 1007 64 996 64 128 256 512) }] }

theorem upper_77 : Upper D R [18,12,768,33,64,16] 13 :=
  bound_sound D R [18,12,768,33,64,16] 13 bound_77
    ((Boolean.boundCheck_true D R [18,12,768,33,64,16] 13 bound_77).mp (by decide +kernel))

def bound_78 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 772 41 80 96 240 176 432 688), lower := (rows 19 14 772 41 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 112 64 128 256 512), good := (rows 43 14 772 41 96 96 96 128 256 512) }] }

theorem upper_78 : Upper D R [18,12,768,33,64,64] 13 :=
  bound_sound D R [18,12,768,33,64,64] 13 bound_78
    ((Boolean.boundCheck_true D R [18,12,768,33,64,64] 13 bound_78).mp (by decide +kernel))

def bound_80 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 19 14 772 41 80 160 80 224 480 736), lower := (rows 19 14 772 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 1 11 85 9 0 241 64 208 336 592), good := (rows 943 14 772 47 996 160 996 160 256 512) }] }

theorem upper_80 : Upper D R [18,12,768,33,64,128,16] 13 :=
  bound_sound D R [18,12,768,33,64,128,16] 13 bound_80
    ((Boolean.boundCheck_true D R [18,12,768,33,64,128,16] 13 bound_80).mp (by decide +kernel))

def bound_81 : Bound 10 := { allowed := (rows 224 208 208 208 0 0 0 0 0 0), upper := (rows 19 14 772 41 80 160 96 208 464 720), lower := (rows 19 14 772 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 10 85 8 80 0 64 208 336 592), good := (rows 919 14 772 15 980 128 980 128 256 512) }] }

theorem upper_81 : Upper D R [18,12,768,33,64,128,32] 13 :=
  bound_sound D R [18,12,768,33,64,128,32] 13 bound_81
    ((Boolean.boundCheck_true D R [18,12,768,33,64,128,32] 13 bound_81).mp (by decide +kernel))

def bound_82 : Bound 10 := { allowed := (rows 192 240 240 208 0 0 0 0 0 0), upper := (rows 19 14 772 41 80 160 192 240 368 624), lower := (rows 19 14 772 41 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 4 8 248 0 224 128 256 512), good := (rows 19 31 772 89 80 208 208 208 256 512) }] }

theorem upper_82 : Upper D R [18,12,768,33,64,128,128] 13 :=
  bound_sound D R [18,12,768,33,64,128,128] 13 bound_82
    ((Boolean.boundCheck_true D R [18,12,768,33,64,128,128] 13 bound_82).mp (by decide +kernel))

def route_79 : Route 10 := (fun mask => (mask,id))

theorem upper_79 : Upper D R [18,12,768,33,64,128] 13 := by
  apply routed_branch D R [18,12,768,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_79
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,768,33,64,128] (choices 1) [16,32,128] route_79).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_80
  · exact upper_81
  · exact upper_82

def route_76 : Route 10 := (fun mask => (mask,id))

theorem upper_76 : Upper D R [18,12,768,33,64] 13 := by
  apply routed_branch D R [18,12,768,33,64] 13 (by decide) (choices 1) [16,64,128] route_76
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,768,33,64] (choices 1) [16,64,128] route_76).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_77
  · exact upper_78
  · exact upper_79

def route_74 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_74 : Upper D R [18,12,768,33] 13 := by
  apply routed_branch D R [18,12,768,33] 13 (by decide) (choices 1) [32,64] route_74
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [18,12,768,33] (choices 1) [32,64] route_74).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_75
  · exact upper_76

def bound_83 : Bound 10 := { allowed := (rows 224 240 240 192 0 0 0 0 0 0), upper := (rows 19 14 772 56 241 225 225 225 481 737), lower := (rows 19 14 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_83 : Upper D R [18,12,768,48] 13 :=
  bound_sound D R [18,12,768,48] 13 bound_83
    ((Boolean.boundCheck_true D R [18,12,768,48] 13 bound_83).mp (by decide +kernel))

def bound_84 : Bound 10 := { allowed := (rows 224 240 240 144 0 0 0 0 0 0), upper := (rows 19 14 772 104 241 241 241 241 497 753), lower := (rows 19 14 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_84 : Upper D R [18,12,768,96] 13 :=
  bound_sound D R [18,12,768,96] 13 bound_84
    ((Boolean.boundCheck_true D R [18,12,768,96] 13 bound_84).mp (by decide +kernel))

def route_72 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_72 : Upper D R [18,12,768] 13 := by
  apply routed_branch D R [18,12,768] 13 (by decide) (choices 2) [17,33,48,96] route_72
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12,768] (choices 2) [17,33,48,96] route_72).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_73
  · exact upper_74
  · exact upper_83
  · exact upper_84

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [18,12] 13 := by
  apply routed_branch D R [18,12] 13 (by decide) (choices 2) [17,33,48,96,257,272,288,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [18,12] (choices 2) [17,33,48,96,257,272,288,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_5
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_42
  · exact upper_47
  · exact upper_72

theorem upper : Upper D R [18,12] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case09
