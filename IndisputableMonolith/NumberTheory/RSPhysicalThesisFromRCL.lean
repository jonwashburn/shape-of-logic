import IndisputableMonolith.NumberTheory.RSPhysicalThesisDecomposition

/-!
# RSPhysicalThesis From RCL Data

Assembly layer: the old thesis follows from the decomposed RCL ledger data.
-/

namespace IndisputableMonolith
namespace NumberTheory

/-- Boundary transport plus the proved RCL/RH infrastructure implies the old
`RSPhysicalThesis`. -/
theorem rsPhysicalThesis_from_boundaryTransport (boundary : BoundaryTransportCert) :
    RSPhysicalThesis :=
  rsPhysicalThesis_of_data (rsPhysicalThesisData_of_boundaryTransport boundary)

end NumberTheory
end IndisputableMonolith
