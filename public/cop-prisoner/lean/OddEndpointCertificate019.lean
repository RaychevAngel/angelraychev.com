import OddEndpointObjective019Transfer
import OddEndpointObjective019Delivery0
import OddEndpointObjective019Delivery1
import OddEndpointObjective019Delivery2
import OddEndpointObjective019Delivery3
import OddEndpointObjective019Delivery4
import OddEndpointObjective019Delivery5
/- Translation of immutable odd-endpoint local strategies; see the export
manifest for exact archive and record pins. The exporter is untrusted.
All finite game and entry obligations below are checked by the Lean kernel. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Delivery.OddEndpointCertificate019
open LocalArena OddEndpointLocal OddEndpointCertificatesSpec GroupedArena
open OddEndpointPattern019
noncomputable def certificates : Certificates residue patchAnchor where
  transfer := OddEndpointObjective019Transfer.certificate
  delivery := by
    intro j allowed
    apply Classical.choice
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by
      have finite : ∀ j : Fin 6, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by decide +kernel
      exact finite j
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨OddEndpointObjective019Delivery0.certificate⟩
    · exact ⟨OddEndpointObjective019Delivery1.certificate⟩
    · exact ⟨OddEndpointObjective019Delivery2.certificate⟩
    · exact ⟨OddEndpointObjective019Delivery3.certificate⟩
    · exact ⟨OddEndpointObjective019Delivery4.certificate⟩
    · exact ⟨OddEndpointObjective019Delivery5.certificate⟩
#print axioms certificates
end Delivery.OddEndpointCertificate019
