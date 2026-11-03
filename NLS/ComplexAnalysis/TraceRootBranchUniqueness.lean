import NLS.ComplexAnalysis.TracePrimitiveContinuation
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.ComplexAnalysis.TracePrimitiveFamily



theorem root_eq_continuous_radial_branch
    {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (f : TracePrimitiveFamily A) (z : ℂ) (q : A) (ht : (z,q) ∈ f.continuationDomain)
    (R : ℝ → ℂ) (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hRsq : ∀ s ∈ Icc (0 : ℝ) 1, R s^2 = f.radicand (z,(s : ℂ) • q))
    (hR0 : R 0 = f.freeRoot z) : f.root (z,q) = R 1 := by
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : (z,(s : ℂ) • q) ∈ f.continuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using f.continuationDomain_segment (z,q) ht s hs
  have hc : ContinuousOn (fun s : ℝ => f.root (z,(s : ℂ) • q)) (Icc (0 : ℝ) 1) :=
    f.analytic_root.continuousOn.comp (by fun_prop) hpath
  have he := isPreconnected_Icc.eq_of_sq_eq hR hc
    (fun s hs => (hRsq s hs).trans (f.root_sq _ (hpath s hs)).symm)
    (fun {s} hs => f.root_ne_zero _ (hpath s hs))
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) (by
      simpa only [ofReal_zero,zero_smul,f.root_base] using hR0)
  have h := he (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa only [ofReal_one,one_smul] using h.symm

end NLS.ComplexAnalysis.TracePrimitiveFamily
