import IndisputableMonolith.Measurement.KernelMatch

namespace IndisputableMonolith
namespace Verification
namespace KernelMatch

/-- Certificate packaging the pointwise kernel identity `J(r(ϑ)) = 2 cot ϑ` from
`Measurement/KernelMatch.lean`. This is a foundational ingredient for the `C = 2A`
bridge proof. -/
structure KernelMatchCert where
  deriving Repr

@[simp] def KernelMatchCert.verified (_c : KernelMatchCert) : Prop :=
  ∀ ϑ : ℝ,
    (0 ≤ ϑ ∧ ϑ ≤ Real.pi / 2) →
      IndisputableMonolith.Cost.Jcost (Measurement.recognitionProfile ϑ) = 2 * Real.cot ϑ

@[simp] theorem KernelMatchCert.verified_any (c : KernelMatchCert) :
    KernelMatchCert.verified c := by
  intro ϑ hϑ
  exact Measurement.kernel_match_pointwise ϑ hϑ

end KernelMatch
end Verification
end IndisputableMonolith
