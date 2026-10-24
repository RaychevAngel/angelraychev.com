import DenseSmall11Offset01
import DenseSmall11Offset02
import DenseSmall11Offset03
import DenseSmall11Offset04
import DenseSmall11Offset05
import DenseSmall11Offset06
import DenseSmall11Offset07
import DenseSmall11Offset08
import DenseSmall11Offset09
import DenseSmall11Offset10
import DenseSmall11Offset11
import DenseSmall12Offset01
import DenseSmall12Offset02
import DenseSmall12Offset03
import DenseSmall12Offset04
import DenseSmall12Offset05
import DenseSmall12Offset06
import DenseSmall12Offset07
import DenseSmall12Offset08
import DenseSmall12Offset09
import DenseSmall12Offset10
import DenseSmall12Offset11
import DenseSmall12Offset12
import DenseSmall13Offset01
import DenseSmall13Offset02
import DenseSmall13Offset03
import DenseSmall13Offset04
import DenseSmall13Offset05
import DenseSmall13Offset06
import DenseSmall13Offset07
import DenseSmall13Offset08
import DenseSmall13Offset09
import DenseSmall13Offset10
import DenseSmall13Offset11
import DenseSmall13Offset12
import DenseSmall13Offset13
import DenseSmall14Offset01
import DenseSmall14Offset02
import DenseSmall14Offset03
import DenseSmall14Offset04
import DenseSmall14Offset05
import DenseSmall14Offset06
import DenseSmall14Offset07
import DenseSmall14Offset08
import DenseSmall14Offset09
import DenseSmall14Offset10
import DenseSmall14Offset11
import DenseSmall14Offset12
import DenseSmall14Offset13
import DenseSmall14Offset14
import DenseSmall15Offset01
import DenseSmall15Offset02
import DenseSmall15Offset03
import DenseSmall15Offset04
import DenseSmall15Offset05
import DenseSmall15Offset06
import DenseSmall15Offset07
import DenseSmall15Offset08
import DenseSmall15Offset09
import DenseSmall15Offset10
import DenseSmall15Offset11
import DenseSmall15Offset12
import DenseSmall15Offset13
import DenseSmall15Offset14
import DenseSmall15Offset15
import DenseSmall16Offset01
import DenseSmall16Offset02
import DenseSmall16Offset03
import DenseSmall16Offset04
import DenseSmall16Offset05
import DenseSmall16Offset06
import DenseSmall16Offset07
import DenseSmall16Offset08
import DenseSmall16Offset09
import DenseSmall16Offset10
import DenseSmall16Offset11
import DenseSmall16Offset12
import DenseSmall16Offset13
import DenseSmall16Offset14
import DenseSmall16Offset15
import DenseSmall16Offset16
import DenseSmall17Offset01
import DenseSmall17Offset02
import DenseSmall17Offset03
import DenseSmall17Offset04
import DenseSmall17Offset05
import DenseSmall17Offset06
import DenseSmall17Offset07
import DenseSmall17Offset08
import DenseSmall17Offset09
import DenseSmall17Offset10
import DenseSmall17Offset11
import DenseSmall17Offset12
import DenseSmall17Offset13
import DenseSmall17Offset14
import DenseSmall17Offset15
import DenseSmall17Offset16
import DenseSmall17Offset17
import DenseSmall18Offset01
import DenseSmall18Offset02
import DenseSmall18Offset03
import DenseSmall18Offset04
import DenseSmall18Offset05
import DenseSmall18Offset06
import DenseSmall18Offset07
import DenseSmall18Offset08
import DenseSmall18Offset09
import DenseSmall18Offset10
import DenseSmall18Offset11
import DenseSmall18Offset12
import DenseSmall18Offset13
import DenseSmall18Offset14
import DenseSmall18Offset15
import DenseSmall18Offset16
import DenseSmall18Offset17
import DenseSmall18Offset18
import DenseSmall19Offset01
import DenseSmall19Offset02
import DenseSmall19Offset03
import DenseSmall19Offset04
import DenseSmall19Offset05
import DenseSmall19Offset06
import DenseSmall19Offset07
import DenseSmall19Offset08
import DenseSmall19Offset09
import DenseSmall19Offset10
import DenseSmall19Offset11
import DenseSmall19Offset12
import DenseSmall19Offset13
import DenseSmall19Offset14
import DenseSmall19Offset15
import DenseSmall19Offset16
import DenseSmall19Offset17
import DenseSmall19Offset18
import DenseSmall19Offset19

/- Finite staircase bridge with explicitly selected adjacency tables. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.DenseSmallStaircase
open FiniteGame Extremal DenseClassification
def attainer (n r : Nat) (low : 11≤n) (high : n≤19) (positive : 1≤r) (limit : r≤n) :
    Attainer n (n*(n-3)+r) (staircase n r) := by
  by_cases hn : n=11
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall11Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall11Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall11Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall11Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall11Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall11Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall11Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall11Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall11Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall11Offset10.attainer
    have hr : r=11 := by omega
    subst r
    exact DenseSmall11Offset11.attainer
  by_cases hn : n=12
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall12Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall12Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall12Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall12Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall12Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall12Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall12Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall12Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall12Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall12Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall12Offset11.attainer
    have hr : r=12 := by omega
    subst r
    exact DenseSmall12Offset12.attainer
  by_cases hn : n=13
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall13Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall13Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall13Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall13Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall13Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall13Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall13Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall13Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall13Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall13Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall13Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall13Offset12.attainer
    have hr : r=13 := by omega
    subst r
    exact DenseSmall13Offset13.attainer
  by_cases hn : n=14
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall14Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall14Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall14Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall14Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall14Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall14Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall14Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall14Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall14Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall14Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall14Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall14Offset12.attainer
    by_cases hr : r=13
    · subst r; exact DenseSmall14Offset13.attainer
    have hr : r=14 := by omega
    subst r
    exact DenseSmall14Offset14.attainer
  by_cases hn : n=15
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall15Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall15Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall15Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall15Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall15Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall15Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall15Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall15Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall15Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall15Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall15Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall15Offset12.attainer
    by_cases hr : r=13
    · subst r; exact DenseSmall15Offset13.attainer
    by_cases hr : r=14
    · subst r; exact DenseSmall15Offset14.attainer
    have hr : r=15 := by omega
    subst r
    exact DenseSmall15Offset15.attainer
  by_cases hn : n=16
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall16Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall16Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall16Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall16Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall16Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall16Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall16Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall16Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall16Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall16Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall16Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall16Offset12.attainer
    by_cases hr : r=13
    · subst r; exact DenseSmall16Offset13.attainer
    by_cases hr : r=14
    · subst r; exact DenseSmall16Offset14.attainer
    by_cases hr : r=15
    · subst r; exact DenseSmall16Offset15.attainer
    have hr : r=16 := by omega
    subst r
    exact DenseSmall16Offset16.attainer
  by_cases hn : n=17
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall17Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall17Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall17Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall17Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall17Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall17Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall17Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall17Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall17Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall17Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall17Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall17Offset12.attainer
    by_cases hr : r=13
    · subst r; exact DenseSmall17Offset13.attainer
    by_cases hr : r=14
    · subst r; exact DenseSmall17Offset14.attainer
    by_cases hr : r=15
    · subst r; exact DenseSmall17Offset15.attainer
    by_cases hr : r=16
    · subst r; exact DenseSmall17Offset16.attainer
    have hr : r=17 := by omega
    subst r
    exact DenseSmall17Offset17.attainer
  by_cases hn : n=18
  · subst n
    by_cases hr : r=1
    · subst r; exact DenseSmall18Offset01.attainer
    by_cases hr : r=2
    · subst r; exact DenseSmall18Offset02.attainer
    by_cases hr : r=3
    · subst r; exact DenseSmall18Offset03.attainer
    by_cases hr : r=4
    · subst r; exact DenseSmall18Offset04.attainer
    by_cases hr : r=5
    · subst r; exact DenseSmall18Offset05.attainer
    by_cases hr : r=6
    · subst r; exact DenseSmall18Offset06.attainer
    by_cases hr : r=7
    · subst r; exact DenseSmall18Offset07.attainer
    by_cases hr : r=8
    · subst r; exact DenseSmall18Offset08.attainer
    by_cases hr : r=9
    · subst r; exact DenseSmall18Offset09.attainer
    by_cases hr : r=10
    · subst r; exact DenseSmall18Offset10.attainer
    by_cases hr : r=11
    · subst r; exact DenseSmall18Offset11.attainer
    by_cases hr : r=12
    · subst r; exact DenseSmall18Offset12.attainer
    by_cases hr : r=13
    · subst r; exact DenseSmall18Offset13.attainer
    by_cases hr : r=14
    · subst r; exact DenseSmall18Offset14.attainer
    by_cases hr : r=15
    · subst r; exact DenseSmall18Offset15.attainer
    by_cases hr : r=16
    · subst r; exact DenseSmall18Offset16.attainer
    by_cases hr : r=17
    · subst r; exact DenseSmall18Offset17.attainer
    have hr : r=18 := by omega
    subst r
    exact DenseSmall18Offset18.attainer
  have hn : n=19 := by omega
  subst n
  by_cases hr : r=1
  · subst r; exact DenseSmall19Offset01.attainer
  by_cases hr : r=2
  · subst r; exact DenseSmall19Offset02.attainer
  by_cases hr : r=3
  · subst r; exact DenseSmall19Offset03.attainer
  by_cases hr : r=4
  · subst r; exact DenseSmall19Offset04.attainer
  by_cases hr : r=5
  · subst r; exact DenseSmall19Offset05.attainer
  by_cases hr : r=6
  · subst r; exact DenseSmall19Offset06.attainer
  by_cases hr : r=7
  · subst r; exact DenseSmall19Offset07.attainer
  by_cases hr : r=8
  · subst r; exact DenseSmall19Offset08.attainer
  by_cases hr : r=9
  · subst r; exact DenseSmall19Offset09.attainer
  by_cases hr : r=10
  · subst r; exact DenseSmall19Offset10.attainer
  by_cases hr : r=11
  · subst r; exact DenseSmall19Offset11.attainer
  by_cases hr : r=12
  · subst r; exact DenseSmall19Offset12.attainer
  by_cases hr : r=13
  · subst r; exact DenseSmall19Offset13.attainer
  by_cases hr : r=14
  · subst r; exact DenseSmall19Offset14.attainer
  by_cases hr : r=15
  · subst r; exact DenseSmall19Offset15.attainer
  by_cases hr : r=16
  · subst r; exact DenseSmall19Offset16.attainer
  by_cases hr : r=17
  · subst r; exact DenseSmall19Offset17.attainer
  by_cases hr : r=18
  · subst r; exact DenseSmall19Offset18.attainer
  have hr : r=19 := by omega
  subst r
  exact DenseSmall19Offset19.attainer

#print axioms attainer
end Delivery.DenseSmallStaircase
