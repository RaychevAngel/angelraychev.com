import SixTypeObjective37Transfer
import SixTypeObjective37Delivery0
import SixTypeObjective37Delivery1
import SixTypeObjective37Delivery2
import SixTypeObjective37Delivery3
import SixTypeObjective37Delivery4
import SixTypeObjective37Delivery5
/- Literal translation of frozen six-type records. Source SHA256:
53daceac01e67909c70c9a06d6390e0858950212d29d66bae70b70d15342fd65. The ordinary producer is untrusted; all obligations are
checked by Lean's kernel. Removed vertices are padded with empty regions. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.SixTypeCertificate37
open LocalArena LocalArenaRows SixTypeLocal
theorem checked : Certificates SixTypePattern37.pattern := by
  constructor
  · exact ⟨SixTypeObjective37Transfer.data, SixTypeObjective37Transfer.checked, SixTypeObjective37Transfer.initial_states⟩
  · intro t present
    rcases t with ⟨t,ht⟩
    have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by omega
    rcases cases with h | h | h | h | h | h <;> subst t
    · exact ⟨SixTypeObjective37Delivery0.data, SixTypeObjective37Delivery0.checked, SixTypeObjective37Delivery0.initial_states⟩
    · exact ⟨SixTypeObjective37Delivery1.data, SixTypeObjective37Delivery1.checked, SixTypeObjective37Delivery1.initial_states⟩
    · exact ⟨SixTypeObjective37Delivery2.data, SixTypeObjective37Delivery2.checked, SixTypeObjective37Delivery2.initial_states⟩
    · exact ⟨SixTypeObjective37Delivery3.data, SixTypeObjective37Delivery3.checked, SixTypeObjective37Delivery3.initial_states⟩
    · exact ⟨SixTypeObjective37Delivery4.data, SixTypeObjective37Delivery4.checked, SixTypeObjective37Delivery4.initial_states⟩
    · exact ⟨SixTypeObjective37Delivery5.data, SixTypeObjective37Delivery5.checked, SixTypeObjective37Delivery5.initial_states⟩
#print axioms checked
end Delivery.SixTypeCertificate37
