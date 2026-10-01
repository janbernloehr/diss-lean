import NLS.ZakharovShabat.SourceAngularThetaDifferential
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Local exactness and closedness of the actual theta cotangent

The actual common-domain data construct an analytic local angle whose
Fréchet derivative is the single theta cotangent on a neighborhood.
Symmetry of its analytic Hessian makes this cotangent closed.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual theta cotangent has a constructed analytic local
primitive at every point of its complex open-gap domain. -/
theorem exists_local_thetaDifferential_fderiv
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0) :
    ∃ θ : CoeffPair p → ℂ, AnalyticAt ℂ θ φ ∧
      sourceAngularThetaDifferential hp hp1 n s =ᶠ[𝓝 φ] (fun ψ => fderiv ℂ θ ψ) := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E⟩ := D.local_charts n φ hφ hgap
  have hbeta := (D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)
  refine ⟨sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε,
    E.theta_representative_analytic hbeta φ hφU,?_⟩
  filter_upwards [E.angle.source_open.mem_nhds hφU] with ψ hψ
  exact E.thetaDifferential_eq_fderiv_representative hbeta ψ hψ

/-- The derivative of the actual theta cotangent is symmetric in
its two source directions, for every finite `p > 1`. -/
theorem fderiv_thetaDifferential_symmetric
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : CoeffPair p) (hφ : φ ∈ W)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0)
    (v w : CoeffPair p) :
    (fderiv ℂ (sourceAngularThetaDifferential hp hp1 n s) φ) v w =
      (fderiv ℂ (sourceAngularThetaDifferential hp hp1 n s) φ) w v := by
  obtain ⟨θ,hθ,hnear⟩ := D.exists_local_thetaDifferential_fderiv n φ hφ hgap
  rw [hnear.fderiv_eq]
  exact ((hθ.contDiffAt (n := 2)).isSymmSndFDerivAt (by norm_num)).eq v w

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
