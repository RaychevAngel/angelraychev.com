import IrregularTen14Base

namespace Delivery.IrregularTen14.Case05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def bound_2 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 56 752 736 736 736 992 736), lower := (rows 7 266 21 56 16 32 64 128 256 512), losses := [] }

theorem upper_2 : Upper D R [6,264,17,48] 13 :=
  bound_sound D R [6,264,17,48] 13 bound_2
    ((Boolean.boundCheck_true D R [6,264,17,48] 13 bound_2).mp (by decide +kernel))

def bound_3 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 7 266 21 104 752 752 752 752 1008 752), lower := (rows 7 266 21 104 16 32 64 128 256 512), losses := [] }

theorem upper_3 : Upper D R [6,264,17,96] 13 :=
  bound_sound D R [6,264,17,96] 13 bound_3
    ((Boolean.boundCheck_true D R [6,264,17,96] 13 bound_3).mp (by decide +kernel))

def bound_4 : Bound 10 := { allowed := (rows 240 224 224 224 0 0 0 0 0 0), upper := (rows 7 266 21 536 240 224 224 224 480 736), lower := (rows 7 266 21 536 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 4 8 0 1023 1023 1023 1023 1023), good := (rows 999 1002 997 1002 992 992 992 992 992 992) }] }

theorem upper_4 : Upper D R [6,264,17,528] 13 :=
  bound_sound D R [6,264,17,528] 13 bound_4
    ((Boolean.boundCheck_true D R [6,264,17,528] 13 bound_4).mp (by decide +kernel))

def bound_6 : Bound 10 := { allowed := (rows 176 240 160 208 0 0 0 0 0 0), upper := (rows 7 266 21 552 48 240 208 208 464 720), lower := (rows 7 266 21 552 48 32 64 128 256 512), losses := [{ target := 6, region := (rows 3 2 6 8 56 32 0 128 256 512), good := (rows 7 287 21 568 48 48 0 128 256 512) }] }

theorem upper_6 : Upper D R [6,264,17,544,32] 13 :=
  bound_sound D R [6,264,17,544,32] 13 bound_6
    ((Boolean.boundCheck_true D R [6,264,17,544,32] 13 bound_6).mp (by decide +kernel))

def bound_8 : Bound 10 := { allowed := (rows 240 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 48 224 224 480 736), lower := (rows 7 266 21 552 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 42 4 40 0 32 104 168 296 552), good := (rows 7 970 5 1002 64 1002 64 128 256 512) }] }

theorem upper_8 : Upper D R [6,264,17,544,64,16] 13 :=
  bound_sound D R [6,264,17,544,64,16] 13 bound_8
    ((Boolean.boundCheck_true D R [6,264,17,544,64,16] 13 bound_8).mp (by decide +kernel))

def bound_10 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 96 80 160 416 672), lower := (rows 7 266 21 552 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 5 127 4 124 0 112 64 252 380 636), good := (rows 911 906 943 938 1002 1002 1002 128 256 512) }] }

theorem upper_10 : Upper D R [6,264,17,544,64,64,16] 13 :=
  bound_sound D R [6,264,17,544,64,64,16] 13 bound_10
    ((Boolean.boundCheck_true D R [6,264,17,544,64,64,16] 13 bound_10).mp (by decide +kernel))

def bound_11 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 96 96 144 400 656), lower := (rows 7 266 21 552 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 128 256 512), good := (rows 103 362 101 616 96 96 96 224 352 616) }] }

theorem upper_11 : Upper D R [6,264,17,544,64,64,32] 13 :=
  bound_sound D R [6,264,17,544,64,64,32] 13 bound_11
    ((Boolean.boundCheck_true D R [6,264,17,544,64,64,32] 13 bound_11).mp (by decide +kernel))

def bound_13 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 96 192 144 416 672), lower := (rows 7 266 21 552 80 96 192 144 256 512), losses := [{ target := 4, region := (rows 5 242 4 248 0 240 192 128 448 704), good := (rows 7 266 47 554 874 874 1002 1002 256 512) }] }

theorem upper_13 : Upper D R [6,264,17,544,64,64,128,16] 13 :=
  bound_sound D R [6,264,17,544,64,64,128,16] 13 bound_13
    ((Boolean.boundCheck_true D R [6,264,17,544,64,64,128,16] 13 bound_13).mp (by decide +kernel))

def bound_14 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 96 192 160 400 656), lower := (rows 7 266 21 552 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 520 0 1023 1023 1023 256 512), good := (rows 231 490 229 744 224 224 224 224 480 744) }] }

theorem upper_14 : Upper D R [6,264,17,544,64,64,128,32] 13 :=
  bound_sound D R [6,264,17,544,64,64,128,32] 13 bound_14
    ((Boolean.boundCheck_true D R [6,264,17,544,64,64,128,32] 13 bound_14).mp (by decide +kernel))

def route_12 : Route 10 := (fun mask => (mask,id))

theorem upper_12 : Upper D R [6,264,17,544,64,64,128] 13 := by
  apply routed_branch D R [6,264,17,544,64,64,128] 13 (by decide) (choices 1) [16,32] route_12
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,17,544,64,64,128] (choices 1) [16,32] route_12).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_13
  · exact upper_14

def route_9 : Route 10 := (fun mask => (mask,id))

theorem upper_9 : Upper D R [6,264,17,544,64,64] 13 := by
  apply routed_branch D R [6,264,17,544,64,64] 13 (by decide) (choices 1) [16,32,128] route_9
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,17,544,64,64] (choices 1) [16,32,128] route_9).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_10
  · exact upper_11
  · exact upper_12

def bound_16 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 160 80 224 480 736), lower := (rows 7 266 21 552 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 86 4 92 0 244 64 208 336 592), good := (rows 47 266 943 552 1002 160 1002 160 256 512) }] }

theorem upper_16 : Upper D R [6,264,17,544,64,128,16] 13 :=
  bound_sound D R [6,264,17,544,64,128,16] 13 bound_16
    ((Boolean.boundCheck_true D R [6,264,17,544,64,128,16] 13 bound_16).mp (by decide +kernel))

def bound_17 : Bound 10 := { allowed := (rows 112 240 96 208 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 160 96 208 464 720), lower := (rows 7 266 21 552 80 160 96 128 256 512), losses := [{ target := 7, region := (rows 3 2 7 8 122 32 104 0 256 512), good := (rows 23 351 21 632 80 112 112 0 256 512) }] }

theorem upper_17 : Upper D R [6,264,17,544,64,128,32] 13 :=
  bound_sound D R [6,264,17,544,64,128,32] 13 bound_17
    ((Boolean.boundCheck_true D R [6,264,17,544,64,128,32] 13 bound_17).mp (by decide +kernel))

def bound_18 : Bound 10 := { allowed := (rows 208 240 192 208 0 0 0 0 0 0), upper := (rows 7 266 21 552 80 160 192 240 368 624), lower := (rows 7 266 21 552 80 160 192 128 256 512), losses := [{ target := 5, region := (rows 3 2 6 8 248 0 224 128 256 512), good := (rows 7 287 21 600 80 208 208 208 256 512) }] }

theorem upper_18 : Upper D R [6,264,17,544,64,128,128] 13 :=
  bound_sound D R [6,264,17,544,64,128,128] 13 bound_18
    ((Boolean.boundCheck_true D R [6,264,17,544,64,128,128] 13 bound_18).mp (by decide +kernel))

def route_15 : Route 10 := (fun mask => (mask,id))

theorem upper_15 : Upper D R [6,264,17,544,64,128] 13 := by
  apply routed_branch D R [6,264,17,544,64,128] 13 (by decide) (choices 1) [16,32,128] route_15
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,17,544,64,128] (choices 1) [16,32,128] route_15).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_16
  · exact upper_17
  · exact upper_18

def route_7 : Route 10 := (fun mask => (mask,id))

theorem upper_7 : Upper D R [6,264,17,544,64] 13 := by
  apply routed_branch D R [6,264,17,544,64] 13 (by decide) (choices 1) [16,64,128] route_7
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,17,544,64] (choices 1) [16,64,128] route_7).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_8
  · exact upper_9
  · exact upper_15

def route_5 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_5 : Upper D R [6,264,17,544] 13 := by
  apply routed_branch D R [6,264,17,544] 13 (by decide) (choices 1) [32,64] route_5
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,17,544] (choices 1) [32,64] route_5).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_6
  · exact upper_7

def route_1 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 576 => (544,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 640 => (544,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_1 : Upper D R [6,264,17] 13 := by
  apply routed_branch D R [6,264,17] 13 (by decide) (choices 2) [48,96,528,544] route_1
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,264,17] (choices 2) [48,96,528,544] route_1).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_2
  · exact upper_3
  · exact upper_4
  · exact upper_5

def bound_20 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 7 266 52 25 752 736 736 736 992 736), lower := (rows 7 266 52 25 16 32 64 128 256 512), losses := [] }

theorem upper_20 : Upper D R [6,264,48,17] 13 :=
  bound_sound D R [6,264,48,17] 13 bound_20
    ((Boolean.boundCheck_true D R [6,264,48,17] 13 bound_20).mp (by decide +kernel))

def bound_21 : Bound 10 := { allowed := (rows 240 240 192 192 0 0 0 0 0 0), upper := (rows 7 266 52 56 721 737 705 705 961 705), lower := (rows 7 266 52 56 16 32 64 128 256 512), losses := [] }

theorem upper_21 : Upper D R [6,264,48,48] 13 :=
  bound_sound D R [6,264,48,48] 13 bound_21
    ((Boolean.boundCheck_true D R [6,264,48,48] 13 bound_21).mp (by decide +kernel))

def bound_22 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 7 266 52 73 752 752 752 752 1008 752), lower := (rows 7 266 52 73 16 32 64 128 256 512), losses := [] }

theorem upper_22 : Upper D R [6,264,48,65] 13 :=
  bound_sound D R [6,264,48,65] 13 bound_22
    ((Boolean.boundCheck_true D R [6,264,48,65] 13 bound_22).mp (by decide +kernel))

def bound_23 : Bound 10 := { allowed := (rows 240 240 192 160 0 0 0 0 0 0), upper := (rows 7 266 52 88 753 737 737 737 993 737), lower := (rows 7 266 52 88 16 32 64 128 256 512), losses := [] }

theorem upper_23 : Upper D R [6,264,48,80] 13 :=
  bound_sound D R [6,264,48,80] 13 bound_23
    ((Boolean.boundCheck_true D R [6,264,48,80] 13 bound_23).mp (by decide +kernel))

def bound_24 : Bound 10 := { allowed := (rows 240 240 192 48 0 0 0 0 0 0), upper := (rows 7 266 52 200 753 753 753 753 1009 753), lower := (rows 7 266 52 200 16 32 64 128 256 512), losses := [] }

theorem upper_24 : Upper D R [6,264,48,192] 13 :=
  bound_sound D R [6,264,48,192] 13 bound_24
    ((Boolean.boundCheck_true D R [6,264,48,192] 13 bound_24).mp (by decide +kernel))

def bound_26 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 7 266 52 521 48 240 208 208 464 720), lower := (rows 7 266 52 521 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 5 7 4 13 16 0 84 148 276 532), good := (rows 975 266 991 523 976 0 64 128 256 512) }] }

theorem upper_26 : Upper D R [6,264,48,513,32] 13 :=
  bound_sound D R [6,264,48,513,32] 13 bound_26
    ((Boolean.boundCheck_true D R [6,264,48,513,32] 13 bound_26).mp (by decide +kernel))

def bound_28 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 266 52 521 80 48 224 224 480 736), lower := (rows 7 266 52 521 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 5 7 4 13 0 32 100 164 292 548), good := (rows 975 266 1007 523 64 992 64 128 256 512) }] }

theorem upper_28 : Upper D R [6,264,48,513,64,16] 13 :=
  bound_sound D R [6,264,48,513,64,16] 13 bound_28
    ((Boolean.boundCheck_true D R [6,264,48,513,64,16] 13 bound_28).mp (by decide +kernel))

def bound_29 : Bound 10 := { allowed := (rows 176 176 192 176 0 0 0 0 0 0), upper := (rows 7 266 52 521 80 96 240 176 432 688), lower := (rows 7 266 52 521 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 5 7 4 13 16 32 0 132 260 516), good := (rows 911 266 959 523 16 32 0 128 256 512) }] }

theorem upper_29 : Upper D R [6,264,48,513,64,64] 13 :=
  bound_sound D R [6,264,48,513,64,64] 13 bound_29
    ((Boolean.boundCheck_true D R [6,264,48,513,64,64] 13 bound_29).mp (by decide +kernel))

def bound_31 : Bound 10 := { allowed := (rows 224 224 192 224 0 0 0 0 0 0), upper := (rows 7 266 52 521 80 160 80 224 480 736), lower := (rows 7 266 52 521 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 6 4 12 0 244 64 208 336 592), good := (rows 47 266 943 521 992 160 992 160 256 512) }] }

theorem upper_31 : Upper D R [6,264,48,513,64,128,16] 13 :=
  bound_sound D R [6,264,48,513,64,128,16] 13 bound_31
    ((Boolean.boundCheck_true D R [6,264,48,513,64,128,16] 13 bound_31).mp (by decide +kernel))

def bound_32 : Bound 10 := { allowed := (rows 208 208 192 208 0 0 0 0 0 0), upper := (rows 7 266 52 521 80 160 96 208 464 720), lower := (rows 7 266 52 521 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 5 6 4 12 80 0 64 208 336 592), good := (rows 15 266 927 521 976 128 976 128 256 512) }] }

theorem upper_32 : Upper D R [6,264,48,513,64,128,32] 13 :=
  bound_sound D R [6,264,48,513,64,128,32] 13 bound_32
    ((Boolean.boundCheck_true D R [6,264,48,513,64,128,32] 13 bound_32).mp (by decide +kernel))

def bound_33 : Bound 10 := { allowed := (rows 240 240 128 240 0 0 0 0 0 0), upper := (rows 7 266 52 521 80 160 192 240 368 624), lower := (rows 7 266 52 521 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 20 8 16 224 0 128 256 512), good := (rows 7 266 52 521 52 160 160 160 256 512) }] }

theorem upper_33 : Upper D R [6,264,48,513,64,128,128] 13 :=
  bound_sound D R [6,264,48,513,64,128,128] 13 bound_33
    ((Boolean.boundCheck_true D R [6,264,48,513,64,128,128] 13 bound_33).mp (by decide +kernel))

def route_30 : Route 10 := (fun mask => (mask,id))

theorem upper_30 : Upper D R [6,264,48,513,64,128] 13 := by
  apply routed_branch D R [6,264,48,513,64,128] 13 (by decide) (choices 1) [16,32,128] route_30
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,48,513,64,128] (choices 1) [16,32,128] route_30).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_31
  · exact upper_32
  · exact upper_33

def route_27 : Route 10 := (fun mask => (mask,id))

theorem upper_27 : Upper D R [6,264,48,513,64] 13 := by
  apply routed_branch D R [6,264,48,513,64] 13 (by decide) (choices 1) [16,64,128] route_27
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,48,513,64] (choices 1) [16,64,128] route_27).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_28
  · exact upper_29
  · exact upper_30

def route_25 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_25 : Upper D R [6,264,48,513] 13 := by
  apply routed_branch D R [6,264,48,513] 13 (by decide) (choices 1) [32,64] route_25
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,48,513] (choices 1) [32,64] route_25).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_26
  · exact upper_27

def bound_34 : Bound 10 := { allowed := (rows 240 240 192 224 0 0 0 0 0 0), upper := (rows 7 266 52 536 241 225 225 225 481 737), lower := (rows 7 266 52 536 16 32 64 128 256 512), losses := [] }

theorem upper_34 : Upper D R [6,264,48,528] 13 :=
  bound_sound D R [6,264,48,528] 13 bound_34
    ((Boolean.boundCheck_true D R [6,264,48,528] 13 bound_34).mp (by decide +kernel))

def bound_35 : Bound 10 := { allowed := (rows 240 240 192 176 0 0 0 0 0 0), upper := (rows 7 266 52 584 241 241 241 241 497 753), lower := (rows 7 266 52 584 16 32 64 128 256 512), losses := [] }

theorem upper_35 : Upper D R [6,264,48,576] 13 :=
  bound_sound D R [6,264,48,576] 13 bound_35
    ((Boolean.boundCheck_true D R [6,264,48,576] 13 bound_35).mp (by decide +kernel))

def route_19 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 640 => (576,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_19 : Upper D R [6,264,48] 13 := by
  apply routed_branch D R [6,264,48] 13 (by decide) (choices 2) [17,48,65,80,192,513,528,576] route_19
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,264,48] (choices 2) [17,48,65,80,192,513,528,576] route_19).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact upper_20
  · exact upper_21
  · exact upper_22
  · exact upper_23
  · exact upper_24
  · exact upper_25
  · exact upper_34
  · exact upper_35

def bound_38 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 266 517 56 48 240 208 208 464 720), lower := (rows 7 266 517 56 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 11 10 14 8 16 0 88 152 280 536), good := (rows 7 975 517 991 976 0 64 128 256 512) }] }

theorem upper_38 : Upper D R [6,264,513,48,32] 13 :=
  bound_sound D R [6,264,513,48,32] 13 bound_38
    ((Boolean.boundCheck_true D R [6,264,513,48,32] 13 bound_38).mp (by decide +kernel))

def bound_40 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 517 56 80 48 224 224 480 736), lower := (rows 7 266 517 56 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 11 10 14 8 0 32 104 168 296 552), good := (rows 7 975 517 1007 64 992 64 128 256 512) }] }

theorem upper_40 : Upper D R [6,264,513,48,64,16] 13 :=
  bound_sound D R [6,264,513,48,64,16] 13 bound_40
    ((Boolean.boundCheck_true D R [6,264,513,48,64,16] 13 bound_40).mp (by decide +kernel))

def bound_41 : Bound 10 := { allowed := (rows 176 176 176 192 0 0 0 0 0 0), upper := (rows 7 266 517 56 80 96 240 176 432 688), lower := (rows 7 266 517 56 80 96 64 128 256 512), losses := [{ target := 6, region := (rows 11 10 14 8 16 32 0 136 264 520), good := (rows 7 911 517 959 16 32 0 128 256 512) }] }

theorem upper_41 : Upper D R [6,264,513,48,64,64] 13 :=
  bound_sound D R [6,264,513,48,64,64] 13 bound_41
    ((Boolean.boundCheck_true D R [6,264,513,48,64,64] 13 bound_41).mp (by decide +kernel))

def bound_43 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 517 56 80 160 80 224 480 736), lower := (rows 7 266 517 56 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 11 10 12 8 0 248 64 208 336 592), good := (rows 7 303 517 943 992 160 992 160 256 512) }] }

theorem upper_43 : Upper D R [6,264,513,48,64,128,16] 13 :=
  bound_sound D R [6,264,513,48,64,128,16] 13 bound_43
    ((Boolean.boundCheck_true D R [6,264,513,48,64,128,16] 13 bound_43).mp (by decide +kernel))

def bound_44 : Bound 10 := { allowed := (rows 208 208 208 192 0 0 0 0 0 0), upper := (rows 7 266 517 56 80 160 96 208 464 720), lower := (rows 7 266 517 56 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 11 10 12 8 80 0 64 208 336 592), good := (rows 7 271 517 927 976 128 976 128 256 512) }] }

theorem upper_44 : Upper D R [6,264,513,48,64,128,32] 13 :=
  bound_sound D R [6,264,513,48,64,128,32] 13 bound_44
    ((Boolean.boundCheck_true D R [6,264,513,48,64,128,32] 13 bound_44).mp (by decide +kernel))

def bound_45 : Bound 10 := { allowed := (rows 240 240 240 128 0 0 0 0 0 0), upper := (rows 7 266 517 56 80 160 192 240 368 624), lower := (rows 7 266 517 56 80 160 192 128 256 512), losses := [{ target := 6, region := (rows 1 2 4 24 16 224 0 128 256 512), good := (rows 7 266 517 56 56 160 160 160 256 512) }] }

theorem upper_45 : Upper D R [6,264,513,48,64,128,128] 13 :=
  bound_sound D R [6,264,513,48,64,128,128] 13 bound_45
    ((Boolean.boundCheck_true D R [6,264,513,48,64,128,128] 13 bound_45).mp (by decide +kernel))

def route_42 : Route 10 := (fun mask => (mask,id))

theorem upper_42 : Upper D R [6,264,513,48,64,128] 13 := by
  apply routed_branch D R [6,264,513,48,64,128] 13 (by decide) (choices 1) [16,32,128] route_42
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,513,48,64,128] (choices 1) [16,32,128] route_42).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_43
  · exact upper_44
  · exact upper_45

def route_39 : Route 10 := (fun mask => (mask,id))

theorem upper_39 : Upper D R [6,264,513,48,64] 13 := by
  apply routed_branch D R [6,264,513,48,64] 13 (by decide) (choices 1) [16,64,128] route_39
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,513,48,64] (choices 1) [16,64,128] route_39).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_40
  · exact upper_41
  · exact upper_42

def route_37 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_37 : Upper D R [6,264,513,48] 13 := by
  apply routed_branch D R [6,264,513,48] 13 (by decide) (choices 1) [32,64] route_37
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,513,48] (choices 1) [32,64] route_37).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_38
  · exact upper_39

def route_36 : Route 10 := (fun mask => match mask with | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_36 : Upper D R [6,264,513] 13 := by
  apply routed_branch D R [6,264,513] 13 (by decide) (choices 2) [48] route_36
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,264,513] (choices 2) [48] route_36).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  · exact upper_37

def bound_47 : Bound 10 := { allowed := (rows 240 224 224 224 0 0 0 0 0 0), upper := (rows 7 266 532 25 240 224 224 224 480 736), lower := (rows 7 266 532 25 16 32 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 4 8 0 1023 1023 1023 1023 1023), good := (rows 999 1002 996 1003 992 992 992 992 992 992) }] }

theorem upper_47 : Upper D R [6,264,528,17] 13 :=
  bound_sound D R [6,264,528,17] 13 bound_47
    ((Boolean.boundCheck_true D R [6,264,528,17] 13 bound_47).mp (by decide +kernel))

def bound_49 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 266 532 41 48 240 208 208 464 720), lower := (rows 7 266 532 41 48 32 64 128 256 512), losses := [{ target := 5, region := (rows 1 2 20 8 16 0 84 148 276 532), good := (rows 967 266 980 9 980 0 64 128 256 512) }] }

theorem upper_49 : Upper D R [6,264,528,33,32] 13 :=
  bound_sound D R [6,264,528,33,32] 13 bound_49
    ((Boolean.boundCheck_true D R [6,264,528,33,32] 13 bound_49).mp (by decide +kernel))

def bound_51 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 48 224 224 480 736), lower := (rows 7 266 532 41 80 48 64 128 256 512), losses := [{ target := 4, region := (rows 1 10 4 8 0 32 104 168 296 552), good := (rows 7 970 516 1003 64 992 64 128 256 512) }] }

theorem upper_51 : Upper D R [6,264,528,33,64,16] 13 :=
  bound_sound D R [6,264,528,33,64,16] 13 bound_51
    ((Boolean.boundCheck_true D R [6,264,528,33,64,16] 13 bound_51).mp (by decide +kernel))

def bound_53 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 96 80 160 416 672), lower := (rows 7 266 532 41 80 96 80 128 256 512), losses := [{ target := 4, region := (rows 5 15 4 12 0 112 64 252 380 636), good := (rows 911 906 943 939 992 992 992 128 256 512) }] }

theorem upper_53 : Upper D R [6,264,528,33,64,64,16] 13 :=
  bound_sound D R [6,264,528,33,64,64,16] 13 bound_53
    ((Boolean.boundCheck_true D R [6,264,528,33,64,64,16] 13 bound_53).mp (by decide +kernel))

def bound_54 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 96 96 144 400 656), lower := (rows 7 266 532 41 80 96 96 128 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 128 256 512), good := (rows 111 362 612 105 96 96 96 224 352 608) }] }

theorem upper_54 : Upper D R [6,264,528,33,64,64,32] 13 :=
  bound_sound D R [6,264,528,33,64,64,32] 13 bound_54
    ((Boolean.boundCheck_true D R [6,264,528,33,64,64,32] 13 bound_54).mp (by decide +kernel))

def bound_56 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 96 192 144 416 672), lower := (rows 7 266 532 41 80 96 192 144 256 512), losses := [{ target := 5, region := (rows 1 2 516 8 1023 0 1023 1023 256 512), good := (rows 215 474 724 217 208 208 208 208 464 724) }] }

theorem upper_56 : Upper D R [6,264,528,33,64,64,128,16] 13 :=
  bound_sound D R [6,264,528,33,64,64,128,16] 13 bound_56
    ((Boolean.boundCheck_true D R [6,264,528,33,64,64,128,16] 13 bound_56).mp (by decide +kernel))

def bound_57 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 96 192 160 400 656), lower := (rows 7 266 532 41 80 96 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 239 490 740 233 224 224 224 224 480 736) }] }

theorem upper_57 : Upper D R [6,264,528,33,64,64,128,32] 13 :=
  bound_sound D R [6,264,528,33,64,64,128,32] 13 bound_57
    ((Boolean.boundCheck_true D R [6,264,528,33,64,64,128,32] 13 bound_57).mp (by decide +kernel))

def route_55 : Route 10 := (fun mask => (mask,id))

theorem upper_55 : Upper D R [6,264,528,33,64,64,128] 13 := by
  apply routed_branch D R [6,264,528,33,64,64,128] 13 (by decide) (choices 1) [16,32] route_55
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33,64,64,128] (choices 1) [16,32] route_55).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_56
  · exact upper_57

def route_52 : Route 10 := (fun mask => (mask,id))

theorem upper_52 : Upper D R [6,264,528,33,64,64] 13 := by
  apply routed_branch D R [6,264,528,33,64,64] 13 (by decide) (choices 1) [16,32,128] route_52
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33,64,64] (choices 1) [16,32,128] route_52).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_53
  · exact upper_54
  · exact upper_55

def bound_59 : Bound 10 := { allowed := (rows 224 224 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 160 80 224 480 736), lower := (rows 7 266 532 41 80 160 80 128 256 512), losses := [{ target := 4, region := (rows 5 6 4 13 0 244 64 208 336 592), good := (rows 47 266 943 41 992 160 992 160 256 512) }] }

theorem upper_59 : Upper D R [6,264,528,33,64,128,16] 13 :=
  bound_sound D R [6,264,528,33,64,128,16] 13 bound_59
    ((Boolean.boundCheck_true D R [6,264,528,33,64,128,16] 13 bound_59).mp (by decide +kernel))

def bound_60 : Bound 10 := { allowed := (rows 240 240 192 208 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 160 96 208 464 720), lower := (rows 7 266 532 41 80 160 96 128 256 512), losses := [{ target := 5, region := (rows 1 2 84 8 80 0 64 208 336 592), good := (rows 7 266 916 9 980 128 980 128 256 512) }] }

theorem upper_60 : Upper D R [6,264,528,33,64,128,32] 13 :=
  bound_sound D R [6,264,528,33,64,128,32] 13 bound_60
    ((Boolean.boundCheck_true D R [6,264,528,33,64,128,32] 13 bound_60).mp (by decide +kernel))

def bound_62 : Bound 10 := { allowed := (rows 240 224 224 208 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 160 192 144 352 608), lower := (rows 7 266 532 41 80 160 192 144 256 512), losses := [{ target := 4, region := (rows 1 10 4 8 0 224 224 128 504 760), good := (rows 7 778 772 875 864 992 992 992 256 512) }] }

theorem upper_62 : Upper D R [6,264,528,33,64,128,128,16] 13 :=
  bound_sound D R [6,264,528,33,64,128,128,16] 13 bound_62
    ((Boolean.boundCheck_true D R [6,264,528,33,64,128,128,16] 13 bound_62).mp (by decide +kernel))

def bound_63 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 160 192 160 336 592), lower := (rows 7 266 532 41 80 160 192 160 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 239 490 740 233 224 224 224 224 480 736) }] }

theorem upper_63 : Upper D R [6,264,528,33,64,128,128,32] 13 :=
  bound_sound D R [6,264,528,33,64,128,128,32] 13 bound_63
    ((Boolean.boundCheck_true D R [6,264,528,33,64,128,128,32] 13 bound_63).mp (by decide +kernel))

def bound_64 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 41 80 160 192 192 304 560), lower := (rows 7 266 532 41 80 160 192 192 256 512), losses := [{ target := 4, region := (rows 1 2 4 9 0 1023 1023 1023 256 512), good := (rows 239 490 740 233 224 224 224 224 480 736) }] }

theorem upper_64 : Upper D R [6,264,528,33,64,128,128,64] 13 :=
  bound_sound D R [6,264,528,33,64,128,128,64] 13 bound_64
    ((Boolean.boundCheck_true D R [6,264,528,33,64,128,128,64] 13 bound_64).mp (by decide +kernel))

def route_61 : Route 10 := (fun mask => (mask,id))

theorem upper_61 : Upper D R [6,264,528,33,64,128,128] 13 := by
  apply routed_branch D R [6,264,528,33,64,128,128] 13 (by decide) (choices 1) [16,32,64] route_61
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33,64,128,128] (choices 1) [16,32,64] route_61).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_62
  · exact upper_63
  · exact upper_64

def route_58 : Route 10 := (fun mask => (mask,id))

theorem upper_58 : Upper D R [6,264,528,33,64,128] 13 := by
  apply routed_branch D R [6,264,528,33,64,128] 13 (by decide) (choices 1) [16,32,128] route_58
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33,64,128] (choices 1) [16,32,128] route_58).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_59
  · exact upper_60
  · exact upper_61

def route_50 : Route 10 := (fun mask => (mask,id))

theorem upper_50 : Upper D R [6,264,528,33,64] 13 := by
  apply routed_branch D R [6,264,528,33,64] 13 (by decide) (choices 1) [16,64,128] route_50
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33,64] (choices 1) [16,64,128] route_50).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact upper_51
  · exact upper_52
  · exact upper_58

def route_48 : Route 10 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

theorem upper_48 : Upper D R [6,264,528,33] 13 := by
  apply routed_branch D R [6,264,528,33] 13 (by decide) (choices 1) [32,64] route_48
    (by exact cover_one)
    ((Boolean.routesCheck_true D R [6,264,528,33] (choices 1) [32,64] route_48).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact upper_49
  · exact upper_50

def bound_65 : Bound 10 := { allowed := (rows 240 240 224 192 0 0 0 0 0 0), upper := (rows 7 266 532 56 241 225 225 225 481 737), lower := (rows 7 266 532 56 16 32 64 128 256 512), losses := [] }

theorem upper_65 : Upper D R [6,264,528,48] 13 :=
  bound_sound D R [6,264,528,48] 13 bound_65
    ((Boolean.boundCheck_true D R [6,264,528,48] 13 bound_65).mp (by decide +kernel))

def bound_66 : Bound 10 := { allowed := (rows 240 240 224 144 0 0 0 0 0 0), upper := (rows 7 266 532 104 241 241 241 241 497 753), lower := (rows 7 266 532 104 16 32 64 128 256 512), losses := [] }

theorem upper_66 : Upper D R [6,264,528,96] 13 :=
  bound_sound D R [6,264,528,96] 13 bound_66
    ((Boolean.boundCheck_true D R [6,264,528,96] 13 bound_66).mp (by decide +kernel))

def route_46 : Route 10 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

theorem upper_46 : Upper D R [6,264,528] 13 := by
  apply routed_branch D R [6,264,528] 13 (by decide) (choices 2) [17,33,48,96] route_46
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,264,528] (choices 2) [17,33,48,96] route_46).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_47
  · exact upper_48
  · exact upper_65
  · exact upper_66

def route_0 : Route 10 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 129 => (17,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 544 => (528,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | 576 => (528,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 640 => (528,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | _ => (mask,id))

theorem upper_0 : Upper D R [6,264] 13 := by
  apply routed_branch D R [6,264] 13 (by decide) (choices 2) [17,48,513,528] route_0
    (by exact cover_two)
    ((Boolean.routesCheck_true D R [6,264] (choices 2) [17,48,513,528] route_0).mp (by decide +kernel))
  intro mask member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact upper_1
  · exact upper_19
  · exact upper_36
  · exact upper_46

theorem upper : Upper D R [6,264] 13 := upper_0

#print axioms upper
end Delivery.IrregularTen14.Case05
