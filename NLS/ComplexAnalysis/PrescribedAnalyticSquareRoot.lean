import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.NormNum

/-!
# Analytic square roots with a prescribed nonzero value

Normalize a holomorphic radicand by the square of the desired value.
The principal root of the normalized radicand is analytic near one,
even if the original radicand lies on the principal branch cut.
Continuous square roots agreeing at a nonzero base value agree locally.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis
variable {E : Type*}

/-- A root with normalization `w` over the normalized principal slit. -/
def prescribedSquareRoot (f : E → ℂ) (w : ℂ) (x : E) : ℂ :=
  w * Complex.sqrt (f x / w ^ 2)

def prescribedSquareRootDomain (f : E → ℂ) (w : ℂ) : Set E :=
  {x | f x / w ^ 2 ∈ Complex.slitPlane}

theorem prescribedSquareRoot_sq (f : E → ℂ) (w : ℂ) (hw : w ≠ 0) (x : E) :
    prescribedSquareRoot f w x ^ 2 = f x := by
  have hs : Complex.sqrt (f x / w ^ 2) ^ 2 = f x / w ^ 2 := by
    have h := Complex.cpow_nat_inv_pow (f x / w ^ 2) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  rw [prescribedSquareRoot, mul_pow, hs]
  exact mul_div_cancel₀ (f x) (pow_ne_zero 2 hw)

theorem prescribedSquareRoot_base (f : E → ℂ) (w : ℂ) (hw : w ≠ 0)
    (x : E) (hx : f x = w ^ 2) : prescribedSquareRoot f w x = w := by
  simp [prescribedSquareRoot, hx, pow_ne_zero 2 hw]

theorem mem_prescribedSquareRootDomain (f : E → ℂ) (w : ℂ) (hw : w ≠ 0)
    (x : E) (hx : f x = w ^ 2) : x ∈ prescribedSquareRootDomain f w := by
  simp [prescribedSquareRootDomain, hx, pow_ne_zero 2 hw,
    Complex.mem_slitPlane_iff]

variable [NormedAddCommGroup E]

theorem isOpen_prescribedSquareRootDomain (f : E → ℂ) (w : ℂ)
    (hf : Continuous f) : IsOpen (prescribedSquareRootDomain f w) :=
  Complex.isOpen_slitPlane.preimage (hf.div_const _)

variable [NormedSpace ℂ E]

theorem analyticOnNhd_prescribedSquareRoot (f : E → ℂ) (w : ℂ)
    (hf : AnalyticOnNhd ℂ f univ) :
    AnalyticOnNhd ℂ (prescribedSquareRoot f w) (prescribedSquareRootDomain f w) := by
  intro x hx
  have hrad : AnalyticAt ℂ (fun y => f y / w ^ 2) x :=
    (hf x (mem_univ _)).div analyticAt_const (by
      intro hw
      have hzero : f x / w ^ 2 = 0 := by rw [hw]; simp
      exact Complex.zero_notMem_slitPlane (hzero ▸ hx))
  have hs : AnalyticAt ℂ Complex.sqrt (f x / w ^ 2) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hx)
  exact analyticAt_const.mul (hs.comp (f := fun y => f y / w ^ 2) hrad)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem prescribedSquareRoot_ne_zero (f : E → ℂ) (w : ℂ) (hw : w ≠ 0)
    (x : E) (hx : x ∈ prescribedSquareRootDomain f w) :
    prescribedSquareRoot f w x ≠ 0 := by
  intro hzero
  have hfzero : f x = 0 := by
    rw [← prescribedSquareRoot_sq f w hw x, hzero]
    simp
  have hradzero : f x / w ^ 2 = 0 := by rw [hfzero]; simp
  exact Complex.zero_notMem_slitPlane (hradzero ▸ hx)

/-- The sign cannot change near a common nonzero value. Only continuity
of the two roots is needed, so moving eigenvalue labels can be continuous. -/
theorem eventuallyEq_of_sq_eq_of_continuousAt
    {X : Type*} [TopologicalSpace X] (f g : X → ℂ) (x : X)
    (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hbase : f x = g x) (hne : g x ≠ 0)
    (hsq : ∀ᶠ y in 𝓝 x, f y ^ 2 = g y ^ 2) : f =ᶠ[𝓝 x] g := by
  have hsum : f x + g x ≠ 0 := by
    rw [hbase, ← two_mul]
    exact mul_ne_zero (by norm_num) hne
  filter_upwards [hsq, (hf.add hg).eventually_ne hsum] with y hy hsumy
  rcases eq_or_eq_neg_of_sq_eq_sq (f y) (g y) hy with h | h
  · exact h
  · exfalso
    exact hsumy (by change f y + g y = 0; rw [h]; simp)

end NLS.ComplexAnalysis
