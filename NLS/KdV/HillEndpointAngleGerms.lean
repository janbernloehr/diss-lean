import NLS.KdV.HillEndpointAngleCotangent
import NLS.KdV.HillEndpointBaseAngles
import NLS.KdV.HillPhysicalGermDerivativeUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every analytic angle germ with the actual physical sine has its endpoint
cotangent in the genuine norming span, independently of its choice of lift. -/
theorem hillDirichletAngleGerm_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (hamatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Complex.sin (a (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 k hk) :
    ∃ c : ℂ, c≠0 ∧ ∀ h : WeightedCoeff SpectralWeight.one.toWeight 2,
      SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0 →
      (fderiv ℂ a (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=
        c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk) := by
  obtain ⟨e,he,hpoint,hsin⟩ := exists_hillDirichlet_endpoint_base_angle q k hk hlog
  have hS0 : hillDirichletGapSine q.val q.property.1 q.property.2 k hk=0 := by
    rcases he with he | he
    · rw [he,Complex.sin_zero] at hsin
      exact hsin.symm
    · rw [he,Complex.sin_pi] at hsin
      exact hsin.symm
  obtain ⟨d,μ,S,ε,hd,hμ,_,hε,hd0,hμ0,_,hε0,_,_,hcomplex,hphysical⟩ :=
    exists_hillDirichlet_analytic_characteristic_angle_at q.val q.property.1 q.property.2 k hk hgap e hpoint hsin
  have hroot := hcomplex.mono (fun _ hp => hp.2.2.1)
  have htrig := hcomplex.mono (fun _ hp => hp.2.2.2.2.1.trans hp.2.2.2.2.2)
  obtain ⟨c,hcn,hD⟩ := hillCharacteristicAngle_endpoint_norming_cotangent q k hk hgap hlog
    d μ ε hd hμ hε hd0 hμ0 hroot htrig
  have hcosA : Complex.cos (a (SpectralWeight.one.toCoeff q.val))≠0 := by
    intro hz
    have h := Complex.sin_sq_add_cos_sq (a (SpectralWeight.one.toCoeff q.val))
    rw [hamatch.self_of_nhds,hS0,hz] at h
    norm_num at h
  have hcosE : Complex.cos (ε (SpectralWeight.one.toCoeff q.val))≠0 := by
    rw [hε0]
    rcases he with he | he
    · rw [he,Complex.cos_zero];norm_num
    · rw [he,Complex.cos_pi];norm_num
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Complex.sin (a (SpectralWeight.one.toCoeff p.val))=Complex.sin (ε (SpectralWeight.one.toCoeff p.val)) := by
    filter_upwards [hamatch,hphysical] with p hp hεp
    exact hp.trans hεp.2.2.2.symm
  refine ⟨(Complex.cos (ε (SpectralWeight.one.toCoeff q.val))/Complex.cos (a (SpectralWeight.one.toCoeff q.val)))*c,
    mul_ne_zero (div_ne_zero hcosE hcosA) hcn,?_⟩
  intro h heven
  have hsame := hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    (fun p => Complex.sin (a p)) (fun p => Complex.sin (ε p))
    (Complex.analyticAt_sin.comp ha) (Complex.analyticAt_sin.comp hε) heq h heven
  rw [ha.differentiableAt.hasFDerivAt.csin.fderiv,hε.differentiableAt.hasFDerivAt.csin.fderiv] at hsame
  simp only [smul_apply,smul_eq_mul] at hsame
  rw [hD] at hsame
  calc
    _ = (Complex.cos (ε (SpectralWeight.one.toCoeff q.val))*
        (c*hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff h) (hillLogNormingGradientCurve q k hk)))/
        Complex.cos (a (SpectralWeight.one.toCoeff q.val)) :=
      (eq_div_iff hcosA).mpr (by simpa only [mul_comm] using hsame)
    _ = _ := by ring

end NLS.KdV
