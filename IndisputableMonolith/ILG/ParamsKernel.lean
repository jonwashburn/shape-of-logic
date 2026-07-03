import Mathlib
import IndisputableMonolith.ILG.Params

namespace IndisputableMonolith
namespace ILG

/-- Verification predicate for the parameter kernel: parameters must be well-formed. -/
def ParamsKernelVerified (P : Params) : Prop :=
  ParamProps P

@[simp] lemma paramsKernel_verified_any (P : Params) (h : ParamProps P) : ParamsKernelVerified P := h


end ILG
end IndisputableMonolith
