import PrefixEnvelope

/-! Four literal odd-order envelope repairs. Every intermediary and count is
checked by the kernel; no result from the external certificate is assumed. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Delivery.FiniteDenseEnvelopes
open FiniteGame Extremal RobustTwoMove

def baseMask (n s : Nat) : Nat :=
  match n,s with
  | 23,0 => 6291456
  | 23,1 => 6144
  | 23,2 => 12288
  | 23,3 => 24576
  | 23,4 => 49152
  | 23,5 => 4227072
  | 23,6 => 196608
  | 23,7 => 393216
  | 23,8 => 786432
  | 23,9 => 1572864
  | 23,10 => 3145728
  | 23,11 => 80
  | 23,12 => 160
  | 23,13 => 320
  | 23,14 => 640
  | 23,15 => 1280
  | 23,16 => 513
  | 23,17 => 1026
  | 23,18 => 5
  | 23,19 => 10
  | 23,20 => 20
  | 23,21 => 40
  | 23,22 => 67584
  | 25,0 => 25165824
  | 25,1 => 12288
  | 25,2 => 24576
  | 25,3 => 49152
  | 25,4 => 98304
  | 25,5 => 16842752
  | 25,6 => 393216
  | 25,7 => 786432
  | 25,8 => 1572864
  | 25,9 => 3145728
  | 25,10 => 6291456
  | 25,11 => 12582912
  | 25,12 => 80
  | 25,13 => 160
  | 25,14 => 320
  | 25,15 => 640
  | 25,16 => 1280
  | 25,17 => 2560
  | 25,18 => 1025
  | 25,19 => 2050
  | 25,20 => 5
  | 25,21 => 10
  | 25,22 => 20
  | 25,23 => 40
  | 25,24 => 135168
  | 27,0 => 100663296
  | 27,1 => 24576
  | 27,2 => 49152
  | 27,3 => 98304
  | 27,4 => 196608
  | 27,5 => 393216
  | 27,6 => 67371008
  | 27,7 => 1572864
  | 27,8 => 3145728
  | 27,9 => 6291456
  | 27,10 => 12582912
  | 27,11 => 25165824
  | 27,12 => 50331648
  | 27,13 => 80
  | 27,14 => 160
  | 27,15 => 320
  | 27,16 => 640
  | 27,17 => 1280
  | 27,18 => 2560
  | 27,19 => 5120
  | 27,20 => 2049
  | 27,21 => 4098
  | 27,22 => 5
  | 27,23 => 10
  | 27,24 => 20
  | 27,25 => 40
  | 27,26 => 532480
  | 31,0 => 1610612736
  | 31,1 => 98304
  | 31,2 => 196608
  | 31,3 => 393216
  | 31,4 => 786432
  | 31,5 => 1074266112
  | 31,6 => 3145728
  | 31,7 => 6291456
  | 31,8 => 12582912
  | 31,9 => 25165824
  | 31,10 => 50331648
  | 31,11 => 100663296
  | 31,12 => 201326592
  | 31,13 => 402653184
  | 31,14 => 805306368
  | 31,15 => 80
  | 31,16 => 160
  | 31,17 => 320
  | 31,18 => 640
  | 31,19 => 1280
  | 31,20 => 2560
  | 31,21 => 5120
  | 31,22 => 10240
  | 31,23 => 20480
  | 31,24 => 8193
  | 31,25 => 16386
  | 31,26 => 5
  | 31,27 => 10
  | 31,28 => 20
  | 31,29 => 40
  | 31,30 => 1081344
  | _,_ => 0

def fullMask (n s : Nat) : Nat :=
  match n,s with
  | 23,0 => 6291520
  | 23,1 => 6272
  | 23,2 => 12544
  | 23,3 => 25088
  | 23,4 => 50176
  | 23,5 => 4227073
  | 23,6 => 196610
  | 23,7 => 393220
  | 23,8 => 786440
  | 23,9 => 1572880
  | 23,10 => 3145760
  | 23,11 => 32848
  | 23,12 => 262304
  | 23,13 => 131392
  | 23,14 => 262784
  | 23,15 => 525568
  | 23,16 => 1049089
  | 23,17 => 2098178
  | 23,18 => 8197
  | 23,19 => 4106
  | 23,20 => 8212
  | 23,21 => 16424
  | 23,22 => 67585
  | 25,0 => 25165888
  | 25,1 => 12416
  | 25,2 => 24832
  | 25,3 => 49664
  | 25,4 => 99328
  | 25,5 => 16844800
  | 25,6 => 393217
  | 25,7 => 786434
  | 25,8 => 1572868
  | 25,9 => 3145736
  | 25,10 => 6291472
  | 25,11 => 12582944
  | 25,12 => 65616
  | 25,13 => 1184
  | 25,14 => 262464
  | 25,15 => 524928
  | 25,16 => 1049856
  | 25,17 => 2099712
  | 25,18 => 4195329
  | 25,19 => 8390658
  | 25,20 => 4101
  | 25,21 => 8202
  | 25,22 => 16404
  | 25,23 => 32808
  | 25,24 => 135172
  | 27,0 => 100663360
  | 27,1 => 24704
  | 27,2 => 49408
  | 27,3 => 98816
  | 27,4 => 197632
  | 27,5 => 395264
  | 27,6 => 67375104
  | 27,7 => 1572865
  | 27,8 => 3145730
  | 27,9 => 6291460
  | 27,10 => 12582920
  | 27,11 => 25165840
  | 27,12 => 50331680
  | 27,13 => 131152
  | 27,14 => 262304
  | 27,15 => 4416
  | 27,16 => 1049216
  | 27,17 => 2098432
  | 27,18 => 4196864
  | 27,19 => 8393728
  | 27,20 => 16779265
  | 27,21 => 33558530
  | 27,22 => 8197
  | 27,23 => 16394
  | 27,24 => 32788
  | 27,25 => 65576
  | 27,26 => 532484
  | 31,0 => 1610612800
  | 31,1 => 98432
  | 31,2 => 196864
  | 31,3 => 393728
  | 31,4 => 787456
  | 31,5 => 1074268160
  | 31,6 => 3149824
  | 31,7 => 6299648
  | 31,8 => 12599296
  | 31,9 => 25165825
  | 31,10 => 50331650
  | 31,11 => 100663300
  | 31,12 => 201326600
  | 31,13 => 402653200
  | 31,14 => 805306400
  | 31,15 => 524368
  | 31,16 => 1184
  | 31,17 => 2097472
  | 31,18 => 4194944
  | 31,19 => 8389888
  | 31,20 => 16779776
  | 31,21 => 33559552
  | 31,22 => 67119104
  | 31,23 => 134238208
  | 31,24 => 268443649
  | 31,25 => 536887298
  | 31,26 => 32773
  | 31,27 => 65546
  | 31,28 => 131092
  | 31,29 => 262184
  | 31,30 => 1081345
  | _,_ => 0

def lower (n : Nat) (s t : Fin n) : Prop :=
  s ≠ t ∧ (fullMask n s.val).testBit t.val = false
def upper (n : Nat) (s t : Fin n) : Prop :=
  s ≠ t ∧ (baseMask n s.val).testBit t.val = false
instance (n : Nat) (s t : Fin n) : Decidable (lower n s t) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (n : Nat) (s t : Fin n) : Decidable (upper n s t) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem witnesses23 : Witnesses (lower 23) (upper 23) := by
  unfold Witnesses
  decide +kernel

private theorem inclusion23 : Subgraph (lower 23) (upper 23) := by
  unfold Subgraph
  decide +kernel

private theorem counts23 : arcCount (lower 23) = 23*(23-1)-3*23 ∧
    arcCount (upper 23) = 23*(23-1)-2*23 := by
  simp only [arcCount_eq]
  decide +kernel

private theorem witnesses25 : Witnesses (lower 25) (upper 25) := by
  unfold Witnesses
  decide +kernel

private theorem inclusion25 : Subgraph (lower 25) (upper 25) := by
  unfold Subgraph
  decide +kernel

private theorem counts25 : arcCount (lower 25) = 25*(25-1)-3*25 ∧
    arcCount (upper 25) = 25*(25-1)-2*25 := by
  simp only [arcCount_eq]
  decide +kernel

private theorem witnesses27 : Witnesses (lower 27) (upper 27) := by
  unfold Witnesses
  decide +kernel

private theorem inclusion27 : Subgraph (lower 27) (upper 27) := by
  unfold Subgraph
  decide +kernel

private theorem counts27 : arcCount (lower 27) = 27*(27-1)-3*27 ∧
    arcCount (upper 27) = 27*(27-1)-2*27 := by
  simp only [arcCount_eq]
  decide +kernel

private theorem witnesses31 : Witnesses (lower 31) (upper 31) := by
  unfold Witnesses
  decide +kernel

private theorem inclusion31 : Subgraph (lower 31) (upper 31) := by
  unfold Subgraph
  decide +kernel

private theorem counts31 : arcCount (lower 31) = 31*(31-1)-3*31 ∧
    arcCount (upper 31) = 31*(31-1)-2*31 := by
  simp only [arcCount_eq]
  decide +kernel

theorem maximum (n m : Nat) (order : n = 23 ∨ n = 25 ∨ n = 27 ∨ n = 31)
    (low : n*(n-1)-3*n ≤ m) (high : m ≤ n*(n-1)-2*n) :
    IsMaximum n m (n*(n-1)-m) := by
  rcases order with rfl | rfl | rfl | rfl
  · exact PrefixEnvelope.maximum_at _ _ inclusion23 (fun s edge => edge.1 rfl)
      witnesses23 (counts23.1 ▸ low) (counts23.2 ▸ high)
  · exact PrefixEnvelope.maximum_at _ _ inclusion25 (fun s edge => edge.1 rfl)
      witnesses25 (counts25.1 ▸ low) (counts25.2 ▸ high)
  · exact PrefixEnvelope.maximum_at _ _ inclusion27 (fun s edge => edge.1 rfl)
      witnesses27 (counts27.1 ▸ low) (counts27.2 ▸ high)
  · exact PrefixEnvelope.maximum_at _ _ inclusion31 (fun s edge => edge.1 rfl)
      witnesses31 (counts31.1 ▸ low) (counts31.2 ▸ high)

#print axioms maximum
end Delivery.FiniteDenseEnvelopes
