import NLS.KdV.HillFiniteAbelianPhase

/-! # Differentiability of finite independent phases through terminal divisors

The local complex analytic phase extension differentiates along any
actual differentiable rough Hill family. Other gaps may be closed, and
no contributing Dirichlet sheet is required to be nonzero.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

theorem differentiableAt_hillFiniteAbelianPhase_family
    (C : ℝ → RealPeriodOneHillPotential) (t : ℝ) (hC : ContinuousAt C t)
    (hQ : DifferentiableAt ℝ (fun r => SpectralWeight.one.toCoeff (C r).val) t)
    (n : ℕ) (hn : 1 ≤ n)
    (hgap : hillRealGapHalfLength (C t).val (C t).property.1 (C t).property.2 n ≠ 0)
    (F : Finset ℕ) : DifferentiableAt ℝ (fun r => hillFiniteAbelianPhase (C r) n hn F) t := by
  obtain ⟨P,hP,_,hmatch⟩ := exists_hillFiniteAbelianPhase_analytic_extension (C t) n hn hgap F
  have hd := (hP.differentiableAt.restrictScalars ℝ).comp t hQ
  have he : (fun r => hillFiniteAbelianPhase (C r) n hn F) =ᶠ[𝓝 t]
      (fun r => P (SpectralWeight.one.toCoeff (C r).val)) := by
    filter_upwards [hC.tendsto.eventually hmatch] with r hr
    exact hr.symm
  exact hd.congr_of_eventuallyEq he

end NLS.KdV
