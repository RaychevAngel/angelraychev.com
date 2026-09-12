import FourCubePotentialData
namespace Princess.FourCubeCompression
open Princess.FiniteIdealCertificates

def charge (p : Nat) : Nat := if p≤3 then 0 else if p=4 then 1 else 2
def transitionCheck (a r : Nat) : Bool := decide
  (r &&& a=r → sizeTable a-sizeTable r≤8 →
    potential a≤charge (sizeTable a-sizeTable r)+potential (hoodTable r))
def sourceCheck (p : Bool) (a : Nat) : Bool :=
  check down (transitionCheck a) ((colorRooms p).map Fin.val) 0

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-- 9 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_0 : check down (sourceCheck false) [5, 17, 8, 20, 32, 0] 0=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_1 : check down (sourceCheck false) [5, 17, 8, 20, 32, 0] 4503603922337792=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_2 : check down (sourceCheck false) [52, 5, 17, 8, 20, 32, 0] 4296147237=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_3 : check down (sourceCheck false) [2, 52, 5, 17, 8, 20, 32, 0] 4504703435014145=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_4 : check down (sourceCheck false) [2, 52, 5, 17, 8, 20, 32, 0] 5066553875759104=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_5 : check down (sourceCheck false) [2, 52, 5, 17, 8, 20, 32, 0] 5067653388435457=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_6 : check down (sourceCheck false) [49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 4504703703449857=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_7 : check down (sourceCheck false) [28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067790827520001=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_8 : check down (sourceCheck false) [37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067791129510177=true := by decide +kernel

/-- 9 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_9 : check down (sourceCheck false) [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067808007389185=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_10 : check down (sourceCheck false) [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067791129518369=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_11 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067808313573669=true := by decide +kernel

/-- 12 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_12 : check down (sourceCheck false) [49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_13 : check down (sourceCheck false) [49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208310296833=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_14 : check down (sourceCheck false) [28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157989295434366977=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_15 : check down (sourceCheck false) [37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157989295736357153=true := by decide +kernel

/-- 9 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_16 : check down (sourceCheck false) [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157989312614236161=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_17 : check down (sourceCheck false) [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157989295736365345=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_18 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157989312920420645=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_19 : check down (sourceCheck false) [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067808313582885=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_20 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067808314097957=true := by decide +kernel

/-- 9 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_21 : check down (sourceCheck false) [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849=true := by decide +kernel

/-- 9 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_22 : check down (sourceCheck false) [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104500690092033=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_23 : check down (sourceCheck false) [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483812221217=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_24 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104500996276517=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_25 : check down (sourceCheck false) [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104500996285733=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_26 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104500996800805=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_27 : check down (sourceCheck false) [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5067808314107301=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_28 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139668184301857=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_29 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139685368889637=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_30 : check down (sourceCheck false) [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139685368898981=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_31 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_32 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899505758501=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_33 : check down (sourceCheck false) [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899505767717=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_34 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899506282789=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_35 : check down (sourceCheck false) [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899506292133=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_36 : check down (sourceCheck false) [7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320154083873653025=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_37 : check down (sourceCheck false) [54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320158481924358437=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_38 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_39 : check down (sourceCheck false) [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699319443749=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_40 : check down (sourceCheck false) [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699319452965=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_41 : check down (sourceCheck false) [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699319968037=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_42 : check down (sourceCheck false) [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699319977381=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_43 : check down (sourceCheck false) [7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322405883687338273=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_44 : check down (sourceCheck false) [54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322410281738043685=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_45 : check down (sourceCheck false) [51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320158482998109477=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_46 : check down (sourceCheck false) [30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322410831494381861=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_47 : check down (sourceCheck false) [39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322410832702350757=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_48 : check down (sourceCheck false) [27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322410832702383525=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_49 : check down (sourceCheck false) [42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_50 : check down (sourceCheck false) [42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5934096300165431589=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_51 : check down (sourceCheck false) [51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844501425497381=true := by decide +kernel

/-- 6 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_52 : check down (sourceCheck false) [30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5934096849921769765=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_53 : check down (sourceCheck false) [39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5934096851129738661=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_54 : check down (sourceCheck false) [27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5934096851129771429=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_55 : check down (sourceCheck false) [62, 15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 6510557602225193253=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_even_batch_56 : check down (sourceCheck false) [59, 62, 15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 6510698340921517477=true := by decide +kernel

theorem transitions_even_checked : check down (sourceCheck false) ((colorRooms false).map Fin.val) 0=true := by
  exact (check_branch down (sourceCheck false) 47 [59, 62, 15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 59 [62, 15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 62 [15, 27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 15 [27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 27 [39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 39 [30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 30 [51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 51 [42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 42 [54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 54 [45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 45 [7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 7 [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 57 [19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 19 [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 10 [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 60 [22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 22 [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 13 [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 34 [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 25 [37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 37 [28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 28 [49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 49 [40, 2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 40 [2, 52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 2 [52, 5, 17, 8, 20, 32, 0] 0 (by decide) (check_branch down (sourceCheck false) 52 [5, 17, 8, 20, 32, 0] 0 (by decide) transitions_even_batch_0 transitions_even_batch_1) transitions_even_batch_2) transitions_even_batch_3) (check_branch down (sourceCheck false) 40 [2, 52, 5, 17, 8, 20, 32, 0] 5066553875759104 (by decide) transitions_even_batch_4 transitions_even_batch_5)) transitions_even_batch_6) transitions_even_batch_7) transitions_even_batch_8) transitions_even_batch_9) transitions_even_batch_10) transitions_even_batch_11) (check_branch down (sourceCheck false) 22 [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) (check_branch down (sourceCheck false) 13 [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) (check_branch down (sourceCheck false) 34 [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) (check_branch down (sourceCheck false) 25 [37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) (check_branch down (sourceCheck false) 37 [28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) (check_branch down (sourceCheck false) 28 [49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1157426208041861121 (by decide) transitions_even_batch_12 transitions_even_batch_13) transitions_even_batch_14) transitions_even_batch_15) transitions_even_batch_16) transitions_even_batch_17) transitions_even_batch_18)) transitions_even_batch_19) transitions_even_batch_20) (check_branch down (sourceCheck false) 19 [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) (check_branch down (sourceCheck false) 10 [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) (check_forced down (sourceCheck false) 60 [22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) (check_branch down (sourceCheck false) 22 [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) (check_branch down (sourceCheck false) 13 [34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) (check_branch down (sourceCheck false) 34 [25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302104483510222849 (by decide) transitions_even_batch_21 transitions_even_batch_22) transitions_even_batch_23) transitions_even_batch_24)) transitions_even_batch_25) transitions_even_batch_26)) transitions_even_batch_27) (check_branch down (sourceCheck false) 7 [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139668184301857 (by decide) (check_forced down (sourceCheck false) 57 [19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139668184301857 (by decide) (check_branch down (sourceCheck false) 19 [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1302139668184301857 (by decide) transitions_even_batch_28 transitions_even_batch_29)) transitions_even_batch_30)) (check_branch down (sourceCheck false) 45 [7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_branch down (sourceCheck false) 7 [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_forced down (sourceCheck false) 57 [19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_branch down (sourceCheck false) 19 [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_branch down (sourceCheck false) 10 [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_forced down (sourceCheck false) 60 [22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) (check_branch down (sourceCheck false) 22 [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1320118899199574017 (by decide) transitions_even_batch_31 transitions_even_batch_32)) transitions_even_batch_33) transitions_even_batch_34)) transitions_even_batch_35) transitions_even_batch_36)) transitions_even_batch_37) (check_branch down (sourceCheck false) 42 [54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_forced down (sourceCheck false) 54 [45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_branch down (sourceCheck false) 45 [7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_branch down (sourceCheck false) 7 [57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_forced down (sourceCheck false) 57 [19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_branch down (sourceCheck false) 19 [10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_branch down (sourceCheck false) 10 [60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_forced down (sourceCheck false) 60 [22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) (check_branch down (sourceCheck false) 22 [13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 1322370699013259265 (by decide) transitions_even_batch_38 transitions_even_batch_39)) transitions_even_batch_40) transitions_even_batch_41)) transitions_even_batch_42) transitions_even_batch_43)) transitions_even_batch_44)) transitions_even_batch_45) transitions_even_batch_46) transitions_even_batch_47) transitions_even_batch_48) (check_branch down (sourceCheck false) 15 [27, 39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341 (by decide) (check_branch down (sourceCheck false) 27 [39, 30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341 (by decide) (check_branch down (sourceCheck false) 39 [30, 51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341 (by decide) (check_branch down (sourceCheck false) 30 [51, 42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341 (by decide) (check_branch down (sourceCheck false) 51 [42, 54, 45, 7, 57, 19, 10, 60, 22, 13, 34, 25, 37, 28, 49, 40, 2, 52, 5, 17, 8, 20, 32, 0] 5931844500351746341 (by decide) transitions_even_batch_49 transitions_even_batch_50) transitions_even_batch_51) transitions_even_batch_52) transitions_even_batch_53) transitions_even_batch_54)) transitions_even_batch_55) transitions_even_batch_56)

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_0 : check down (sourceCheck true) [36, 48, 1, 4, 16] 0=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_1 : check down (sourceCheck true) [36, 48, 1, 4, 16] 281543713030160=true := by decide +kernel

/-- 5 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_2 : check down (sourceCheck true) [24, 36, 48, 1, 4, 16] 281552286187520=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_3 : check down (sourceCheck true) [33, 24, 36, 48, 1, 4, 16] 281543713034256=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_4 : check down (sourceCheck true) [12, 33, 24, 36, 48, 1, 4, 16] 281552305061906=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_5 : check down (sourceCheck true) [21, 12, 33, 24, 36, 48, 1, 4, 16] 281552305066514=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_6 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 281552305324050=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_7 : check down (sourceCheck true) [33, 24, 36, 48, 1, 4, 16] 72339137734180864=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_8 : check down (sourceCheck true) [33, 24, 36, 48, 1, 4, 16] 72339137750962192=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_9 : check down (sourceCheck true) [12, 33, 24, 36, 48, 1, 4, 16] 72339146342989842=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_10 : check down (sourceCheck true) [21, 12, 33, 24, 36, 48, 1, 4, 16] 72339146342994450=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_11 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72339146343251986=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_12 : check down (sourceCheck true) [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 281552305328722=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_13 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356729937002512=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_14 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356738529296402=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_15 : check down (sourceCheck true) [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356738529301074=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_16 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345578856448=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_17 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345597992978=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_18 : check down (sourceCheck true) [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345597997650=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_19 : check down (sourceCheck true) [6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81363937781678096=true := by decide +kernel

/-- 5 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_20 : check down (sourceCheck true) [53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 281552305328730=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_21 : check down (sourceCheck true) [3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81366136807030802=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_22 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_23 : check down (sourceCheck true) [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245504835602=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_24 : check down (sourceCheck true) [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245504840274=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_25 : check down (sourceCheck true) [6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82489837688520720=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_26 : check down (sourceCheck true) [53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245504840282=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_27 : check down (sourceCheck true) [3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492036713873426=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_28 : check down (sourceCheck true) [50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81366137343906322=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_29 : check down (sourceCheck true) [29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492311592042514=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_30 : check down (sourceCheck true) [38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492312196026962=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_31 : check down (sourceCheck true) [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492345951780882=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_32 : check down (sourceCheck true) [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492312196043346=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_33 : check down (sourceCheck true) [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492346564153946=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_34 : check down (sourceCheck true) [41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_35 : check down (sourceCheck true) [41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335045927567378=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_36 : check down (sourceCheck true) [50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146557600274=true := by decide +kernel

/-- 8 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_37 : check down (sourceCheck true) [29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335320805736466=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_38 : check down (sourceCheck true) [38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335321409720914=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_39 : check down (sourceCheck true) [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335355165474834=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_40 : check down (sourceCheck true) [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335321409737298=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_41 : check down (sourceCheck true) [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2388335355777847898=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_42 : check down (sourceCheck true) [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82492346564172378=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_43 : check down (sourceCheck true) [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210=true := by decide +kernel

/-- 10 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_44 : check down (sourceCheck true) [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565731317186578=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_45 : check down (sourceCheck true) [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565697561449042=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_46 : check down (sourceCheck true) [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565731929559642=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_47 : check down (sourceCheck true) [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565731929578074=true := by decide +kernel

/-- 11 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_48 : check down (sourceCheck true) [58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676636066305610322=true := by decide +kernel

/-- 12 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_49 : check down (sourceCheck true) [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546=true := by decide +kernel

/-- 2 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_50 : check down (sourceCheck true) [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528948523610=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_51 : check down (sourceCheck true) [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528948542042=true := by decide +kernel

/-- 7 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_52 : check down (sourceCheck true) [58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712664897684312658=true := by decide +kernel

/-- 3 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_53 : check down (sourceCheck true) [55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712673693785723482=true := by decide +kernel

/-- 1 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_54 : check down (sourceCheck true) [43, 55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712673695933225562=true := by decide +kernel

/-- 4 source states; all292 residual states per source are retained. -/
theorem transitions_odd_batch_55 : check down (sourceCheck true) [31, 43, 55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 11936045730640499290=true := by decide +kernel

theorem transitions_odd_checked : check down (sourceCheck true) ((colorRooms true).map Fin.val) 0=true := by
  exact (check_branch down (sourceCheck true) 63 [31, 43, 55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 31 [43, 55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 43 [55, 46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 55 [46, 58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 46 [58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 58 [11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 11 [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 61 [23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 23 [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 14 [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 35 [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 26 [38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 38 [29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 29 [50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 50 [41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 41 [3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 3 [53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 53 [44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 44 [6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 6 [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 56 [18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 18 [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 9 [21, 12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 21 [12, 33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 12 [33, 24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 33 [24, 36, 48, 1, 4, 16] 0 (by decide) (check_branch down (sourceCheck true) 24 [36, 48, 1, 4, 16] 0 (by decide) transitions_odd_batch_0 transitions_odd_batch_1) transitions_odd_batch_2) transitions_odd_batch_3) transitions_odd_batch_4) transitions_odd_batch_5) transitions_odd_batch_6) (check_branch down (sourceCheck true) 18 [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72339137734180864 (by decide) (check_branch down (sourceCheck true) 9 [21, 12, 33, 24, 36, 48, 1, 4, 16] 72339137734180864 (by decide) (check_branch down (sourceCheck true) 21 [12, 33, 24, 36, 48, 1, 4, 16] 72339137734180864 (by decide) (check_branch down (sourceCheck true) 12 [33, 24, 36, 48, 1, 4, 16] 72339137734180864 (by decide) transitions_odd_batch_7 transitions_odd_batch_8) transitions_odd_batch_9) transitions_odd_batch_10) transitions_odd_batch_11)) transitions_odd_batch_12) (check_branch down (sourceCheck true) 6 [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356729937002512 (by decide) (check_forced down (sourceCheck true) 56 [18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356729937002512 (by decide) (check_branch down (sourceCheck true) 18 [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 72356729937002512 (by decide) transitions_odd_batch_13 transitions_odd_batch_14)) transitions_odd_batch_15)) (check_branch down (sourceCheck true) 44 [6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345578856448 (by decide) (check_branch down (sourceCheck true) 6 [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345578856448 (by decide) (check_forced down (sourceCheck true) 56 [18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345578856448 (by decide) (check_branch down (sourceCheck true) 18 [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 81346345578856448 (by decide) transitions_odd_batch_16 transitions_odd_batch_17)) transitions_odd_batch_18) transitions_odd_batch_19)) transitions_odd_batch_20) transitions_odd_batch_21) (check_branch down (sourceCheck true) 41 [3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_branch down (sourceCheck true) 3 [53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_forced down (sourceCheck true) 53 [44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_branch down (sourceCheck true) 44 [6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_branch down (sourceCheck true) 6 [56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_forced down (sourceCheck true) 56 [18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) (check_branch down (sourceCheck true) 18 [9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 82472245485699072 (by decide) transitions_odd_batch_22 transitions_odd_batch_23)) transitions_odd_batch_24) transitions_odd_batch_25)) transitions_odd_batch_26) transitions_odd_batch_27)) transitions_odd_batch_28) transitions_odd_batch_29) transitions_odd_batch_30) transitions_odd_batch_31) transitions_odd_batch_32) transitions_odd_batch_33) (check_branch down (sourceCheck true) 23 [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 14 [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 35 [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 26 [38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 38 [29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 29 [50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) (check_branch down (sourceCheck true) 50 [41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2387209146020724754 (by decide) transitions_odd_batch_34 transitions_odd_batch_35) transitions_odd_batch_36) transitions_odd_batch_37) transitions_odd_batch_38) transitions_odd_batch_39) transitions_odd_batch_40) transitions_odd_batch_41)) transitions_odd_batch_42) (check_branch down (sourceCheck true) 11 [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210 (by decide) (check_forced down (sourceCheck true) 61 [23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210 (by decide) (check_branch down (sourceCheck true) 23 [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210 (by decide) (check_branch down (sourceCheck true) 14 [35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210 (by decide) (check_branch down (sourceCheck true) 35 [26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2676565696957448210 (by decide) transitions_odd_batch_43 transitions_odd_batch_44) transitions_odd_batch_45) transitions_odd_batch_46)) transitions_odd_batch_47)) transitions_odd_batch_48) (check_branch down (sourceCheck true) 46 [58, 11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546 (by decide) (check_forced down (sourceCheck true) 58 [11, 61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546 (by decide) (check_branch down (sourceCheck true) 11 [61, 23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546 (by decide) (check_forced down (sourceCheck true) 61 [23, 14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546 (by decide) (check_branch down (sourceCheck true) 23 [14, 35, 26, 38, 29, 50, 41, 3, 53, 44, 6, 56, 18, 9, 21, 12, 33, 24, 36, 48, 1, 4, 16] 2712594528336150546 (by decide) transitions_odd_batch_49 transitions_odd_batch_50)) transitions_odd_batch_51)) transitions_odd_batch_52)) transitions_odd_batch_53) transitions_odd_batch_54) transitions_odd_batch_55)

theorem charge_budget_checked : ∀ p q : Fin 9, p.val+q.val≤8 → charge p.val+charge q.val≤2 := by decide
theorem charge_budget (p q : Nat) (h : p+q≤8) : charge p+charge q≤2 :=
  charge_budget_checked ⟨p,by omega⟩ ⟨q,by omega⟩ h
theorem potential_empty : potential 0=0 := by decide
theorem potential_even_full : potential 6510698340921550245=40 := by decide
theorem potential_odd_full : potential 11936045732788001370=40 := by decide
end Princess.FourCubeCompression
#print axioms Princess.FourCubeCompression.transitions_even_checked
#print axioms Princess.FourCubeCompression.transitions_odd_checked
