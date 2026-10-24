import IrregularTen14Base

namespace Delivery.IrregularTen14.Case02
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 7 26 21 104 1008 992 992 992 992 992), lower := (rows 7 26 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [6,24,17,96] 13 :=
  bound_sound D R [6,24,17,96] 13 bound_2
    ((Boolean.boundCheck_true D R [6,24,17,96] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 7 26 21 296 752 736 736 736 992 736), lower := (rows 7 26 21 296 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [6,24,17,288] 13 :=
  bound_sound D R [6,24,17,288] 13 bound_3
    ((Boolean.boundCheck_true D R [6,24,17,288] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 240 224 224 224 0 0 0 0 0 0), upper := (rows 7 26 21 776 240 224 224 224 480 736), lower := (rows 7 26 21 776 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 1023 0 1023 1023 1023 1023 1023), good := (rows 1007 1002 1005 1000 1000 1000 1000 1000 1000 1000) }] }

theorem upper_4 : Upper D R [6,24,17,768] 13 :=
  bound_sound D R [6,24,17,768] 13 bound_4
    ((Boolean.boundCheck_true D R [6,24,17,768] 13 bound_4).mp (by decide +kernel))

def route_1 : Route 10 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [6,24,17] 13 := by
  apply routed_branch D R [6,24,17] 13 (by decide) (choices 2) [96,288,768] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,17] (choices 2) [96,288,768] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4

def bound_6 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 7 26 37 56 976 992 960 960 960 960), lower := (rows 7 26 37 56 16 32 64 128 256 512), losses := [] }

theorem upper_6 : Upper D R [6,24,33,48] 13 :=
  bound_sound D R [6,24,33,48] 13 bound_6
    ((Boolean.boundCheck_true D R [6,24,33,48] 13 bound_6).mp (by decide +kernel))

def bound_7 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 7 26 37 88 1008 992 992 992 992 992), lower := (rows 7 26 37 88 16 32 64 128 256 512), losses := [] }

theorem upper_7 : Upper D R [6,24,33,80] 13 :=
  bound_sound D R [6,24,33,80] 13 bound_7
    ((Boolean.boundCheck_true D R [6,24,33,80] 13 bound_7).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 7 26 37 104 976 1008 976 976 976 976), lower := (rows 7 26 37 104 16 32 64 128 256 512), losses := [] }

theorem upper_8 : Upper D R [6,24,33,96] 13 :=
  bound_sound D R [6,24,33,96] 13 bound_8
    ((Boolean.boundCheck_true D R [6,24,33,96] 13 bound_8).mp (by decide +kernel))

def bound_9 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 7 26 37 200 1008 1008 1008 1008 1008 1008), lower := (rows 7 26 37 200 16 32 64 128 256 512), losses := [] }

theorem upper_9 : Upper D R [6,24,33,192] 13 :=
  bound_sound D R [6,24,33,192] 13 bound_9
    ((Boolean.boundCheck_true D R [6,24,33,192] 13 bound_9).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 7 26 37 280 752 736 736 736 992 736), lower := (rows 7 26 37 280 16 32 64 128 256 512), losses := [] }

theorem upper_10 : Upper D R [6,24,33,272] 13 :=
  bound_sound D R [6,24,33,272] 13 bound_10
    ((Boolean.boundCheck_true D R [6,24,33,272] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 37 296 720 752 720 720 976 720), lower := (rows 7 26 37 296 16 32 64 128 256 512), losses := [] }

theorem upper_11 : Upper D R [6,24,33,288] 13 :=
  bound_sound D R [6,24,33,288] 13 bound_11
    ((Boolean.boundCheck_true D R [6,24,33,288] 13 bound_11).mp (by decide +kernel))

def bound_12 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 7 26 37 328 752 752 752 752 1008 752), lower := (rows 7 26 37 328 16 32 64 128 256 512), losses := [] }

theorem upper_12 : Upper D R [6,24,33,320] 13 :=
  bound_sound D R [6,24,33,320] 13 bound_12
    ((Boolean.boundCheck_true D R [6,24,33,320] 13 bound_12).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 240 192 208 208 0 0 0 0 0 0), upper := (rows 7 26 37 776 48 240 208 208 464 720), lower := (rows 7 26 37 776 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 18 4 27 16 0 82 146 274 530), good := (rows 975 986 13 776 986 0 64 128 256 512) }] }

theorem upper_14 : Upper D R [6,24,33,768,32] 13 :=
  bound_sound D R [6,24,33,768,32] 13 bound_14
    ((Boolean.boundCheck_true D R [6,24,33,768,32] 13 bound_14).mp (by decide +kernel))

def bound_16 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 48 224 224 480 736), lower := (rows 7 26 37 776 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 45 0 32 100 164 292 548), good := (rows 975 10 1005 776 64 1000 64 128 256 512) }] }

theorem upper_16 : Upper D R [6,24,33,768,64,16] 13 :=
  bound_sound D R [6,24,33,768,64,16] 13 bound_16
    ((Boolean.boundCheck_true D R [6,24,33,768,64,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 96 240 176 432 688), lower := (rows 7 26 37 776 80 96 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 8 0 112 64 128 256 512), good := (rows 7 47 37 776 96 96 96 128 256 512) }] }

theorem upper_17 : Upper D R [6,24,33,768,64,64] 13 :=
  bound_sound D R [6,24,33,768,64,64] 13 bound_17
    ((Boolean.boundCheck_true D R [6,24,33,768,64,64] 13 bound_17).mp (by decide +kernel))

def bound_19 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 160 80 224 480 736), lower := (rows 7 26 37 776 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 90 0 242 64 208 336 592), good := (rows 47 943 37 776 1000 160 1000 160 256 512) }] }

theorem upper_19 : Upper D R [6,24,33,768,64,128,16] 13 :=
  bound_sound D R [6,24,33,768,64,128,16] 13 bound_19
    ((Boolean.boundCheck_true D R [6,24,33,768,64,128,16] 13 bound_19).mp (by decide +kernel))

def bound_20 : Bound 10 := { allowed := (rows 240 192 208 208 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 160 96 208 464 720), lower := (rows 7 26 37 776 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 82 4 90 80 0 64 208 336 592), good := (rows 15 922 5 776 986 128 986 128 256 512) }] }

theorem upper_20 : Upper D R [6,24,33,768,64,128,32] 13 :=
  bound_sound D R [6,24,33,768,64,128,32] 13 bound_20
    ((Boolean.boundCheck_true D R [6,24,33,768,64,128,32] 13 bound_20).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 160 192 144 352 608), lower := (rows 7 26 37 776 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 2 4 255 0 224 224 128 500 756), good := (rows 783 778 877 776 872 1000 1000 1000 256 512) }] }

theorem upper_22 : Upper D R [6,24,33,768,64,128,128,16] 13 :=
  bound_sound D R [6,24,33,768,64,128,128,16] 13 bound_22
    ((Boolean.boundCheck_true D R [6,24,33,768,64,128,128,16] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 160 192 160 336 592), lower := (rows 7 26 37 776 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 3 2 7 8 0 1023 1023 1023 256 512), good := (rows 231 239 229 1000 224 224 224 224 480 736) }] }

theorem upper_23 : Upper D R [6,24,33,768,64,128,128,32] 13 :=
  bound_sound D R [6,24,33,768,64,128,128,32] 13 bound_23
    ((Boolean.boundCheck_true D R [6,24,33,768,64,128,128,32] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 37 776 80 160 192 192 304 560), lower := (rows 7 26 37 776 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 3 2 7 8 0 1023 1023 1023 256 512), good := (rows 231 239 229 1000 224 224 224 224 480 736) }] }

theorem upper_24 : Upper D R [6,24,33,768,64,128,128,64] 13 :=
  bound_sound D R [6,24,33,768,64,128,128,64] 13 bound_24
    ((Boolean.boundCheck_true D R [6,24,33,768,64,128,128,64] 13 bound_24).mp (by decide +kernel))

def route_21 : Route 10 := (fun mask => (mask,id))

theorem upper_21 : Upper D R [6,24,33,768,64,128,128] 13 := by
  apply routed_branch D R [6,24,33,768,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_21
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,33,768,64,128,128] (choices 1) [16,32,64] route_21).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_22
  · exact upper_23
  · exact upper_24

def route_18 : Route 10 := (fun mask => (mask,id))

theorem upper_18 : Upper D R [6,24,33,768,64,128] 13 := by
  apply routed_branch D R [6,24,33,768,64,128] 13 (by decide) (choices 1) [16,32,128] route_18
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,33,768,64,128] (choices 1) [16,32,128] route_18).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_19
  · exact upper_20
  · exact upper_21

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [6,24,33,768,64] 13 := by
  apply routed_branch D R [6,24,33,768,64] 13 (by decide) (choices 1) [16,64,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,33,768,64] (choices 1) [16,64,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_13 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_13 : Upper D R [6,24,33,768] 13 := by
  apply routed_branch D R [6,24,33,768] 13 (by decide) (choices 1) [32,64] route_13
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,33,768] (choices 1) [32,64] route_13).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_14
  · exact upper_15

def route_5 : Route 10 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 576 => (320,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [6,24,33] 13 := by
  apply routed_branch D R [6,24,33] 13 (by decide) (choices 2) [48,80,96,192,272,288,320,768] route_5
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,33] (choices 2) [48,80,96,192,272,288,320,768] route_5).mp (by decide +kernel))
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

def bound_25 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 52 1001 1009 993 993 993 993 993), lower := (rows 7 26 52 8 16 32 64 128 256 512), losses := [] }

theorem upper_25 : Upper D R [6,24,48] 13 :=
  bound_sound D R [6,24,48] 13 bound_25
    ((Boolean.boundCheck_true D R [6,24,48] 13 bound_25).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 240 224 144 240 0 0 0 0 0 0), upper := (rows 7 26 100 1017 1009 1009 1009 1009 1009 1009), lower := (rows 7 26 100 8 16 32 64 128 256 512), losses := [] }

theorem upper_26 : Upper D R [6,24,96] 13 :=
  bound_sound D R [6,24,96] 13 bound_26
    ((Boolean.boundCheck_true D R [6,24,96] 13 bound_26).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 7 26 261 56 752 736 736 736 992 736), lower := (rows 7 26 261 56 16 32 64 128 256 512), losses := [] }

theorem upper_28 : Upper D R [6,24,257,48] 13 :=
  bound_sound D R [6,24,257,48] 13 bound_28
    ((Boolean.boundCheck_true D R [6,24,257,48] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 7 26 261 104 752 752 752 752 1008 752), lower := (rows 7 26 261 104 16 32 64 128 256 512), losses := [] }

theorem upper_29 : Upper D R [6,24,257,96] 13 :=
  bound_sound D R [6,24,257,96] 13 bound_29
    ((Boolean.boundCheck_true D R [6,24,257,96] 13 bound_29).mp (by decide +kernel))

def bound_30 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 7 26 261 536 240 224 224 224 480 736), lower := (rows 7 26 261 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 7 8 0 1023 1023 1023 1023 1023), good := (rows 999 1007 997 1000 992 992 992 992 992 992) }] }

theorem upper_30 : Upper D R [6,24,257,528] 13 :=
  bound_sound D R [6,24,257,528] 13 bound_30
    ((Boolean.boundCheck_true D R [6,24,257,528] 13 bound_30).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 261 552 48 240 208 208 464 720), lower := (rows 7 26 261 552 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 7 8 16 0 82 146 274 530), good := (rows 967 991 261 520 976 0 64 128 256 512) }] }

theorem upper_32 : Upper D R [6,24,257,544,32] 13 :=
  bound_sound D R [6,24,257,544,32] 13 bound_32
    ((Boolean.boundCheck_true D R [6,24,257,544,32] 13 bound_32).mp (by decide +kernel))

def bound_34 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 26 261 552 80 48 224 224 480 736), lower := (rows 7 26 261 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 40 0 32 104 168 296 552), good := (rows 7 975 261 1000 64 1000 64 128 256 512) }] }

theorem upper_34 : Upper D R [6,24,257,544,64,16] 13 :=
  bound_sound D R [6,24,257,544,64,16] 13 bound_34
    ((Boolean.boundCheck_true D R [6,24,257,544,64,16] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 7 26 261 552 80 96 240 176 432 688), lower := (rows 7 26 261 552 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 10 4 8 112 0 64 128 256 512), good := (rows 7 26 261 538 80 80 80 128 256 512) }] }

theorem upper_35 : Upper D R [6,24,257,544,64,64] 13 :=
  bound_sound D R [6,24,257,544,64,64] 13 bound_35
    ((Boolean.boundCheck_true D R [6,24,257,544,64,64] 13 bound_35).mp (by decide +kernel))

def bound_37 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 26 261 552 80 160 80 224 480 736), lower := (rows 7 26 261 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 6 90 0 242 64 208 336 592), good := (rows 47 943 261 552 1000 160 1000 160 256 512) }] }

theorem upper_37 : Upper D R [6,24,257,544,64,128,16] 13 :=
  bound_sound D R [6,24,257,544,64,128,16] 13 bound_37
    ((Boolean.boundCheck_true D R [6,24,257,544,64,128,16] 13 bound_37).mp (by decide +kernel))

def bound_38 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 261 552 80 160 96 208 464 720), lower := (rows 7 26 261 552 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 6 8 80 0 64 208 336 592), good := (rows 7 927 261 520 976 128 976 128 256 512) }] }

theorem upper_38 : Upper D R [6,24,257,544,64,128,32] 13 :=
  bound_sound D R [6,24,257,544,64,128,32] 13 bound_38
    ((Boolean.boundCheck_true D R [6,24,257,544,64,128,32] 13 bound_38).mp (by decide +kernel))

def bound_39 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 7 26 261 552 80 160 192 240 368 624), lower := (rows 7 26 261 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 10 4 8 248 0 224 128 256 512), good := (rows 7 26 261 602 80 208 208 208 256 512) }] }

theorem upper_39 : Upper D R [6,24,257,544,64,128,128] 13 :=
  bound_sound D R [6,24,257,544,64,128,128] 13 bound_39
    ((Boolean.boundCheck_true D R [6,24,257,544,64,128,128] 13 bound_39).mp (by decide +kernel))

def route_36 : Route 10 := (fun mask => (mask,id))

theorem upper_36 : Upper D R [6,24,257,544,64,128] 13 := by
  apply routed_branch D R [6,24,257,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_36
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,257,544,64,128] (choices 1) [16,32,128] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_37
  · exact upper_38
  · exact upper_39

def route_33 : Route 10 := (fun mask => (mask,id))

theorem upper_33 : Upper D R [6,24,257,544,64] 13 := by
  apply routed_branch D R [6,24,257,544,64] 13 (by decide) (choices 1) [16,64,128] route_33
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,257,544,64] (choices 1) [16,64,128] route_33).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_34
  · exact upper_35
  · exact upper_36

def route_31 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_31 : Upper D R [6,24,257,544] 13 := by
  apply routed_branch D R [6,24,257,544] 13 (by decide) (choices 1) [32,64] route_31
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,257,544] (choices 1) [32,64] route_31).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_32
  · exact upper_33

def route_27 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_27 : Upper D R [6,24,257] 13 := by
  apply routed_branch D R [6,24,257] 13 (by decide) (choices 2) [48,96,528,544] route_27
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,257] (choices 2) [48,96,528,544] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30
  · exact upper_31

def bound_41 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 7 26 276 41 752 736 736 736 992 736), lower := (rows 7 26 276 41 16 32 64 128 256 512), losses := [] }

theorem upper_41 : Upper D R [6,24,272,33] 13 :=
  bound_sound D R [6,24,272,33] 13 bound_41
    ((Boolean.boundCheck_true D R [6,24,272,33] 13 bound_41).mp (by decide +kernel))

def bound_42 : Bound 10 := { allowed := (rows 240 224 224 144 0 0 0 0 0 0), upper := (rows 7 26 276 104 753 737 737 737 993 737), lower := (rows 7 26 276 104 16 32 64 128 256 512), losses := [] }

theorem upper_42 : Upper D R [6,24,272,96] 13 :=
  bound_sound D R [6,24,272,96] 13 bound_42
    ((Boolean.boundCheck_true D R [6,24,272,96] 13 bound_42).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 240 224 224 224 0 0 0 0 0 0), upper := (rows 7 26 276 521 240 224 224 224 480 736), lower := (rows 7 26 276 521 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 1023 1023), good := (rows 1007 1002 996 1001 992 992 992 992 992 992) }] }

theorem upper_43 : Upper D R [6,24,272,513] 13 :=
  bound_sound D R [6,24,272,513] 13 bound_43
    ((Boolean.boundCheck_true D R [6,24,272,513] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 7 26 276 552 241 225 225 225 481 737), lower := (rows 7 26 276 552 16 32 64 128 256 512), losses := [] }

theorem upper_44 : Upper D R [6,24,272,544] 13 :=
  bound_sound D R [6,24,272,544] 13 bound_44
    ((Boolean.boundCheck_true D R [6,24,272,544] 13 bound_44).mp (by decide +kernel))

def route_40 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_40 : Upper D R [6,24,272] 13 := by
  apply routed_branch D R [6,24,272] 13 (by decide) (choices 2) [33,96,513,544] route_40
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,272] (choices 2) [33,96,513,544] route_40).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_41
  · exact upper_42
  · exact upper_43
  · exact upper_44

def bound_46 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 7 26 292 25 752 736 736 736 992 736), lower := (rows 7 26 292 25 16 32 64 128 256 512), losses := [] }

theorem upper_46 : Upper D R [6,24,288,17] 13 :=
  bound_sound D R [6,24,288,17] 13 bound_46
    ((Boolean.boundCheck_true D R [6,24,288,17] 13 bound_46).mp (by decide +kernel))

def bound_47 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 292 41 720 752 720 720 976 720), lower := (rows 7 26 292 41 16 32 64 128 256 512), losses := [] }

theorem upper_47 : Upper D R [6,24,288,33] 13 :=
  bound_sound D R [6,24,288,33] 13 bound_47
    ((Boolean.boundCheck_true D R [6,24,288,33] 13 bound_47).mp (by decide +kernel))

def bound_48 : Bound 10 := { allowed := (rows 240 224 208 192 0 0 0 0 0 0), upper := (rows 7 26 292 56 721 737 705 705 961 705), lower := (rows 7 26 292 56 16 32 64 128 256 512), losses := [] }

theorem upper_48 : Upper D R [6,24,288,48] 13 :=
  bound_sound D R [6,24,288,48] 13 bound_48
    ((Boolean.boundCheck_true D R [6,24,288,48] 13 bound_48).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 7 26 292 73 752 752 752 752 1008 752), lower := (rows 7 26 292 73 16 32 64 128 256 512), losses := [] }

theorem upper_49 : Upper D R [6,24,288,65] 13 :=
  bound_sound D R [6,24,288,65] 13 bound_49
    ((Boolean.boundCheck_true D R [6,24,288,65] 13 bound_49).mp (by decide +kernel))

def bound_50 : Bound 10 := { allowed := (rows 240 224 208 160 0 0 0 0 0 0), upper := (rows 7 26 292 88 753 737 737 737 993 737), lower := (rows 7 26 292 88 16 32 64 128 256 512), losses := [] }

theorem upper_50 : Upper D R [6,24,288,80] 13 :=
  bound_sound D R [6,24,288,80] 13 bound_50
    ((Boolean.boundCheck_true D R [6,24,288,80] 13 bound_50).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 224 208 144 0 0 0 0 0 0), upper := (rows 7 26 292 104 721 753 721 721 977 721), lower := (rows 7 26 292 104 16 32 64 128 256 512), losses := [] }

theorem upper_51 : Upper D R [6,24,288,96] 13 :=
  bound_sound D R [6,24,288,96] 13 bound_51
    ((Boolean.boundCheck_true D R [6,24,288,96] 13 bound_51).mp (by decide +kernel))

def bound_52 : Bound 10 := { allowed := (rows 240 224 208 48 0 0 0 0 0 0), upper := (rows 7 26 292 200 753 753 753 753 1009 753), lower := (rows 7 26 292 200 16 32 64 128 256 512), losses := [] }

theorem upper_52 : Upper D R [6,24,288,192] 13 :=
  bound_sound D R [6,24,288,192] 13 bound_52
    ((Boolean.boundCheck_true D R [6,24,288,192] 13 bound_52).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 292 521 48 240 208 208 464 720), lower := (rows 7 26 292 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 82 146 274 530), good := (rows 975 986 260 521 976 0 64 128 256 512) }] }

theorem upper_54 : Upper D R [6,24,288,513,32] 13 :=
  bound_sound D R [6,24,288,513,32] 13 bound_54
    ((Boolean.boundCheck_true D R [6,24,288,513,32] 13 bound_54).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 240 224 192 224 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 48 224 224 480 736), lower := (rows 7 26 292 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 2 36 9 0 32 100 164 292 548), good := (rows 975 10 996 521 64 996 64 128 256 512) }] }

theorem upper_56 : Upper D R [6,24,288,513,64,16] 13 :=
  bound_sound D R [6,24,288,513,64,16] 13 bound_56
    ((Boolean.boundCheck_true D R [6,24,288,513,64,16] 13 bound_56).mp (by decide +kernel))

def bound_58 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 96 80 160 416 672), lower := (rows 7 26 292 521 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 118 11 0 112 64 246 374 630), good := (rows 911 943 932 521 996 996 996 128 256 512) }] }

theorem upper_58 : Upper D R [6,24,288,513,64,64,16] 13 :=
  bound_sound D R [6,24,288,513,64,64,16] 13 bound_58
    ((Boolean.boundCheck_true D R [6,24,288,513,64,64,16] 13 bound_58).mp (by decide +kernel))

def bound_59 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 96 96 144 400 656), lower := (rows 7 26 292 521 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 128 256 512), good := (rows 103 106 356 617 96 96 96 224 356 608) }] }

theorem upper_59 : Upper D R [6,24,288,513,64,64,32] 13 :=
  bound_sound D R [6,24,288,513,64,64,32] 13 bound_59
    ((Boolean.boundCheck_true D R [6,24,288,513,64,64,32] 13 bound_59).mp (by decide +kernel))

def bound_61 : Bound 10 := { allowed := (rows 224 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 96 192 144 416 672), lower := (rows 7 26 292 521 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 3 2 244 8 0 240 192 128 448 704), good := (rows 7 47 292 521 868 868 996 996 256 512) }] }

theorem upper_61 : Upper D R [6,24,288,513,64,64,128,16] 13 :=
  bound_sound D R [6,24,288,513,64,64,128,16] 13 bound_61
    ((Boolean.boundCheck_true D R [6,24,288,513,64,64,128,16] 13 bound_61).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 96 192 160 400 656), lower := (rows 7 26 292 521 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 1023 256 512), good := (rows 231 234 484 745 224 224 224 224 484 736) }] }

theorem upper_62 : Upper D R [6,24,288,513,64,64,128,32] 13 :=
  bound_sound D R [6,24,288,513,64,64,128,32] 13 bound_62
    ((Boolean.boundCheck_true D R [6,24,288,513,64,64,128,32] 13 bound_62).mp (by decide +kernel))

def route_60 : Route 10 := (fun mask => (mask,id))

theorem upper_60 : Upper D R [6,24,288,513,64,64,128] 13 := by
  apply routed_branch D R [6,24,288,513,64,64,128] 13 (by decide) (choices 1) [16,32] route_60
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513,64,64,128] (choices 1) [16,32] route_60).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_61
  · exact upper_62

def route_57 : Route 10 := (fun mask => (mask,id))

theorem upper_57 : Upper D R [6,24,288,513,64,64] 13 := by
  apply routed_branch D R [6,24,288,513,64,64] 13 (by decide) (choices 1) [16,32,128] route_57
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513,64,64] (choices 1) [16,32,128] route_57).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_58
  · exact upper_59
  · exact upper_60

def bound_64 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 160 80 224 480 736), lower := (rows 7 26 292 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 86 10 0 242 64 208 336 592), good := (rows 47 943 292 521 996 160 996 160 256 512) }] }

theorem upper_64 : Upper D R [6,24,288,513,64,128,16] 13 :=
  bound_sound D R [6,24,288,513,64,128,16] 13 bound_64
    ((Boolean.boundCheck_true D R [6,24,288,513,64,128,16] 13 bound_64).mp (by decide +kernel))

def bound_65 : Bound 10 := { allowed := (rows 240 96 208 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 160 96 208 464 720), lower := (rows 7 26 292 521 80 160 96 128 256 512), losses := [{ target := 7, region := (rows 1 10 4 8 117 32 100 0 256 512), good := (rows 87 26 372 539 80 112 112 0 256 512) }] }

theorem upper_65 : Upper D R [6,24,288,513,64,128,32] 13 :=
  bound_sound D R [6,24,288,513,64,128,32] 13 bound_65
    ((Boolean.boundCheck_true D R [6,24,288,513,64,128,32] 13 bound_65).mp (by decide +kernel))

def bound_67 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 160 192 144 352 608), lower := (rows 7 26 292 521 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 3 2 244 11 0 224 224 128 500 756), good := (rows 783 783 868 521 868 996 996 996 256 512) }] }

theorem upper_67 : Upper D R [6,24,288,513,64,128,128,16] 13 :=
  bound_sound D R [6,24,288,513,64,128,128,16] 13 bound_67
    ((Boolean.boundCheck_true D R [6,24,288,513,64,128,128,16] 13 bound_67).mp (by decide +kernel))

def bound_68 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 160 192 160 336 592), lower := (rows 7 26 292 521 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 1023 256 512), good := (rows 231 234 484 745 224 224 224 224 484 736) }] }

theorem upper_68 : Upper D R [6,24,288,513,64,128,128,32] 13 :=
  bound_sound D R [6,24,288,513,64,128,128,32] 13 bound_68
    ((Boolean.boundCheck_true D R [6,24,288,513,64,128,128,32] 13 bound_68).mp (by decide +kernel))

def bound_69 : Bound 10 := { allowed := (rows 240 224 192 240 0 0 0 0 0 0), upper := (rows 7 26 292 521 80 160 192 192 304 560), lower := (rows 7 26 292 521 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 260 8 0 1023 1023 1023 256 512), good := (rows 231 234 484 745 224 224 224 224 484 736) }] }

theorem upper_69 : Upper D R [6,24,288,513,64,128,128,64] 13 :=
  bound_sound D R [6,24,288,513,64,128,128,64] 13 bound_69
    ((Boolean.boundCheck_true D R [6,24,288,513,64,128,128,64] 13 bound_69).mp (by decide +kernel))

def route_66 : Route 10 := (fun mask => (mask,id))

theorem upper_66 : Upper D R [6,24,288,513,64,128,128] 13 := by
  apply routed_branch D R [6,24,288,513,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_66
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513,64,128,128] (choices 1) [16,32,64] route_66).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_67
  · exact upper_68
  · exact upper_69

def route_63 : Route 10 := (fun mask => (mask,id))

theorem upper_63 : Upper D R [6,24,288,513,64,128] 13 := by
  apply routed_branch D R [6,24,288,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_63
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513,64,128] (choices 1) [16,32,128] route_63).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_64
  · exact upper_65
  · exact upper_66

def route_55 : Route 10 := (fun mask => (mask,id))

theorem upper_55 : Upper D R [6,24,288,513,64] 13 := by
  apply routed_branch D R [6,24,288,513,64] 13 (by decide) (choices 1) [16,64,128] route_55
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513,64] (choices 1) [16,64,128] route_55).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_56
  · exact upper_57
  · exact upper_63

def route_53 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_53 : Upper D R [6,24,288,513] 13 := by
  apply routed_branch D R [6,24,288,513] 13 (by decide) (choices 1) [32,64] route_53
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,288,513] (choices 1) [32,64] route_53).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_54
  · exact upper_55

def bound_70 : Bound 10 := { allowed := (rows 240 224 208 224 0 0 0 0 0 0), upper := (rows 7 26 292 536 241 225 225 225 481 737), lower := (rows 7 26 292 536 16 32 64 128 256 512), losses := [] }

theorem upper_70 : Upper D R [6,24,288,528] 13 :=
  bound_sound D R [6,24,288,528] 13 bound_70
    ((Boolean.boundCheck_true D R [6,24,288,528] 13 bound_70).mp (by decide +kernel))

def bound_71 : Bound 10 := { allowed := (rows 240 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 292 552 209 241 209 209 465 721), lower := (rows 7 26 292 552 16 32 64 128 256 512), losses := [] }

theorem upper_71 : Upper D R [6,24,288,544] 13 :=
  bound_sound D R [6,24,288,544] 13 bound_71
    ((Boolean.boundCheck_true D R [6,24,288,544] 13 bound_71).mp (by decide +kernel))

def bound_72 : Bound 10 := { allowed := (rows 240 224 208 176 0 0 0 0 0 0), upper := (rows 7 26 292 584 241 241 241 241 497 753), lower := (rows 7 26 292 584 16 32 64 128 256 512), losses := [] }

theorem upper_72 : Upper D R [6,24,288,576] 13 :=
  bound_sound D R [6,24,288,576] 13 bound_72
    ((Boolean.boundCheck_true D R [6,24,288,576] 13 bound_72).mp (by decide +kernel))

def route_45 : Route 10 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_45 : Upper D R [6,24,288] 13 := by
  apply routed_branch D R [6,24,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_45
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,288] (choices 2) [17,33,48,65,80,96,192,513,528,544,576] route_45).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_46
  · exact upper_47
  · exact upper_48
  · exact upper_49
  · exact upper_50
  · exact upper_51
  · exact upper_52
  · exact upper_53
  · exact upper_70
  · exact upper_71
  · exact upper_72

def bound_74 : Bound 10 := { allowed := (rows 224 224 224 224 0 0 0 0 0 0), upper := (rows 7 26 772 25 240 224 224 224 480 736), lower := (rows 7 26 772 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 1023 8 0 1023 1023 1023 1023 1023), good := (rows 999 1007 996 1005 996 996 996 996 996 996) }] }

theorem upper_74 : Upper D R [6,24,768,17] 13 :=
  bound_sound D R [6,24,768,17] 13 bound_74
    ((Boolean.boundCheck_true D R [6,24,768,17] 13 bound_74).mp (by decide +kernel))

def bound_76 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 772 41 48 240 208 208 464 720), lower := (rows 7 26 772 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 3 2 23 8 16 0 82 146 274 530), good := (rows 967 991 772 13 980 0 64 128 256 512) }] }

theorem upper_76 : Upper D R [6,24,768,33,32] 13 :=
  bound_sound D R [6,24,768,33,32] 13 bound_76
    ((Boolean.boundCheck_true D R [6,24,768,33,32] 13 bound_76).mp (by decide +kernel))

def bound_78 : Bound 10 := { allowed := (rows 224 224 224 208 0 0 0 0 0 0), upper := (rows 7 26 772 41 80 48 224 224 480 736), lower := (rows 7 26 772 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 3 2 46 8 0 32 104 168 296 552), good := (rows 7 975 772 1005 64 996 64 128 256 512) }] }

theorem upper_78 : Upper D R [6,24,768,33,64,16] 13 :=
  bound_sound D R [6,24,768,33,64,16] 13 bound_78
    ((Boolean.boundCheck_true D R [6,24,768,33,64,16] 13 bound_78).mp (by decide +kernel))

def bound_79 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 7 26 772 41 80 96 240 176 432 688), lower := (rows 7 26 772 41 80 96 64 128 256 512), losses := [{ target := 5, region := (rows 1 10 4 8 112 0 64 128 256 512), good := (rows 7 26 772 27 80 80 80 128 256 512) }] }

theorem upper_79 : Upper D R [6,24,768,33,64,64] 13 :=
  bound_sound D R [6,24,768,33,64,64] 13 bound_79
    ((Boolean.boundCheck_true D R [6,24,768,33,64,64] 13 bound_79).mp (by decide +kernel))

def bound_81 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 26 772 41 80 160 80 224 480 736), lower := (rows 7 26 772 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 3 2 86 11 0 242 64 208 336 592), good := (rows 47 943 772 41 996 160 996 160 256 512) }] }

theorem upper_81 : Upper D R [6,24,768,33,64,128,16] 13 :=
  bound_sound D R [6,24,768,33,64,128,16] 13 bound_81
    ((Boolean.boundCheck_true D R [6,24,768,33,64,128,16] 13 bound_81).mp (by decide +kernel))

def bound_82 : Bound 10 := { allowed := (rows 208 224 208 208 0 0 0 0 0 0), upper := (rows 7 26 772 41 80 160 96 208 464 720), lower := (rows 7 26 772 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 3 2 86 8 80 0 64 208 336 592), good := (rows 7 927 772 9 980 128 980 128 256 512) }] }

theorem upper_82 : Upper D R [6,24,768,33,64,128,32] 13 :=
  bound_sound D R [6,24,768,33,64,128,32] 13 bound_82
    ((Boolean.boundCheck_true D R [6,24,768,33,64,128,32] 13 bound_82).mp (by decide +kernel))

def bound_83 : Bound 10 := { allowed := (rows 240 192 240 208 0 0 0 0 0 0), upper := (rows 7 26 772 41 80 160 192 240 368 624), lower := (rows 7 26 772 41 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 1 10 4 8 248 0 224 128 256 512), good := (rows 7 26 772 91 80 208 208 208 256 512) }] }

theorem upper_83 : Upper D R [6,24,768,33,64,128,128] 13 :=
  bound_sound D R [6,24,768,33,64,128,128] 13 bound_83
    ((Boolean.boundCheck_true D R [6,24,768,33,64,128,128] 13 bound_83).mp (by decide +kernel))

def route_80 : Route 10 := (fun mask => (mask,id))

theorem upper_80 : Upper D R [6,24,768,33,64,128] 13 := by
  apply routed_branch D R [6,24,768,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_80
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,768,33,64,128] (choices 1) [16,32,128] route_80).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_81
  · exact upper_82
  · exact upper_83

def route_77 : Route 10 := (fun mask => (mask,id))

theorem upper_77 : Upper D R [6,24,768,33,64] 13 := by
  apply routed_branch D R [6,24,768,33,64] 13 (by decide) (choices 1) [16,64,128] route_77
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,768,33,64] (choices 1) [16,64,128] route_77).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_78
  · exact upper_79
  · exact upper_80

def route_75 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_75 : Upper D R [6,24,768,33] 13 := by
  apply routed_branch D R [6,24,768,33] 13 (by decide) (choices 1) [32,64] route_75
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,24,768,33] (choices 1) [32,64] route_75).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_76
  · exact upper_77

def bound_84 : Bound 10 := { allowed := (rows 240 224 240 192 0 0 0 0 0 0), upper := (rows 7 26 772 56 241 225 225 225 481 737), lower := (rows 7 26 772 56 16 32 64 128 256 512), losses := [] }

theorem upper_84 : Upper D R [6,24,768,48] 13 :=
  bound_sound D R [6,24,768,48] 13 bound_84
    ((Boolean.boundCheck_true D R [6,24,768,48] 13 bound_84).mp (by decide +kernel))

def bound_85 : Bound 10 := { allowed := (rows 240 224 240 144 0 0 0 0 0 0), upper := (rows 7 26 772 104 241 241 241 241 497 753), lower := (rows 7 26 772 104 16 32 64 128 256 512), losses := [] }

theorem upper_85 : Upper D R [6,24,768,96] 13 :=
  bound_sound D R [6,24,768,96] 13 bound_85
    ((Boolean.boundCheck_true D R [6,24,768,96] 13 bound_85).mp (by decide +kernel))

def route_73 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_73 : Upper D R [6,24,768] 13 := by
  apply routed_branch D R [6,24,768] 13 (by decide) (choices 2) [17,33,48,96] route_73
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24,768] (choices 2) [17,33,48,96] route_73).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_74
  · exact upper_75
  · exact upper_84
  · exact upper_85

def route_0 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 513 => (257,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 528 => (272,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 544 => (288,(fun i => match i.val with | 8 => 9 | 9 => 8 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 576 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | 8 => 9 | 9 => 8 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 640 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | 8 => 9 | 9 => 8 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [6,24] 13 := by
  apply routed_branch D R [6,24] 13 (by decide) (choices 2) [17,33,48,96,257,272,288,768] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,24] (choices 2) [17,33,48,96,257,272,288,768] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_5
  · exact upper_25
  · exact upper_26
  · exact upper_27
  · exact upper_40
  · exact upper_45
  · exact upper_73

theorem upper : Upper D R [6,24] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case02
