import NLS.KdV.HillProductFixedPeriods
import NLS.ZakharovShabat.SourceLemma12_3
import NLS.ZakharovShabat.SourceCanonicalRootRealBand

/-! The exact real mean-value formula for a filled Hill product period
column on a genuine original circle. The canonical-root factorization
retains the physical one-over-two-pi normalization. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillProductColumnGapNumerator (n r : ℕ+) (c : ℂ) (ψ : CoeffPair 2) (k : ℤ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) : ℂ :=
  z*hillEnergyProductCoordinateDerivative n r (z^2-c,d)/
    sourceStandardRootOmittedProduct (by norm_num) (by norm_num) k ψ z

theorem analytic_hillProductColumnGapNumerator (n r : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hψ : IsRealType (CoeffPair.toMax 2 ψ)) (k : ℤ)
    (d : lp (fun _ : ℕ+ => ℂ) 2)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k) :
    AnalyticOnNhd ℂ (hillProductColumnGapNumerator n r c ψ k d)
      (closedBall (D.center:ℂ) D.radius) := by
  obtain ⟨W,_,_,hreal,hdata⟩ := exists_global_source_analytic_omittedJointProduct
    (p := 2) (by norm_num) (by norm_num)
  have hP := sourceStandardRootOmittedProduct_analyticOnNhd_spectral
    (by norm_num) (by norm_num) k W (hdata k).2.1 ψ (hreal hψ)
  intro z hz
  have he : AnalyticAt ℂ (fun w : ℂ => (w^2-c,d)) z :=
    ((analyticAt_id.pow 2).sub analyticAt_const).prod analyticAt_const
  exact (analyticAt_id.mul ((analyticAt_hillEnergyProductCoordinateDerivative n r _).comp he)).div
    (hP z (D.closedBall_subset_omittedDomain hz))
    (sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) ψ z k
      (D.closedBall_subset_omittedDomain hz))

theorem hillEnergyProductPeriodColumn_real_mean_value (n r : ℕ+) (c : ℂ) (ψ : CoeffPair 2)
    (hψ : IsRealType (CoeffPair.toMax 2 ψ)) (k : ℤ)
    (d : lp (fun _ : ℕ+ => ℂ) 2)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) ψ k)
    (hreal : ∀ z ∈ sourcePeriodicSegment (by norm_num) (by norm_num) ψ k,
      (hillProductColumnGapNumerator n r c ψ k d z).im = 0) :
    ∃ μ ∈ sourcePeriodicSegment (by norm_num) (by norm_num) ψ k,
      hillEnergyProductPeriodColumn n r c ψ D d = -hillProductColumnGapNumerator n r c ψ k d μ := by
  let g := hillProductColumnGapNumerator n r c ψ k d
  obtain ⟨_,_,_,_,hm⟩ := D.lemma12_3_circle g
    (analytic_hillProductColumnGapNumerator n r c ψ hψ k d D)
  obtain ⟨μ,hμ,he⟩ := hm hreal
  refine ⟨μ,hμ,?_⟩
  have hi : (∮ z in C((D.center:ℂ),D.radius),
      (2*z*hillEnergyProductCoordinateDerivative n r (z^2-c,d))/
        sourceCanonicalRoot (by norm_num) (by norm_num) ψ z) =
      (-Complex.I)*(∮ z in C((D.center:ℂ),D.radius),
        g z/sourceStandardRoot (by norm_num) (by norm_num) ψ k z) := by
    rw [← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr D.radius_pos.le
    intro z hz
    have hs := sourceStandardRoot_ne_zero_off_segment (by norm_num) (by norm_num) ψ k z
      (D.sphere_subset_rootDomain hz k)
    have ho := sourceStandardRootOmittedProduct_ne_zero (by norm_num) (by norm_num) ψ z k
      (D.closedBall_subset_omittedDomain (sphere_subset_closedBall hz))
    dsimp only
    rw [sourceCanonicalRoot_eq_omitted (by norm_num) (by norm_num) k]
    dsimp only [g,hillProductColumnGapNumerator]
    field_simp [hs,ho]
    simp only [Complex.I_sq]
    ring
  rw [hillEnergyProductPeriodColumn,hi]
  rw [PiecewiseC1Loop.normalizedIntegral,PiecewiseC1Loop.integral_circle] at he
  have hn : (2*Real.pi:ℂ)⁻¹*(-Complex.I) = (2*Real.pi*Complex.I:ℂ)⁻¹ := by
    field_simp
    simp only [Complex.I_sq]
    ring
  rw [← mul_assoc,hn]
  exact he

end NLS.KdV
