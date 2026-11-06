import NLS.KdV.HillCharacteristicLogSheet
import NLS.KdV.HillLogNormingCotangent
import NLS.KdV.HillCharacteristicAngle
import NLS.ComplexAnalysis.SineNormingEndpoint

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- At a periodic Dirichlet terminal in an open gap, the actual characteristic
angle has its full physical cotangent in the genuine log-norming span. -/
theorem hillCharacteristicAngle_endpoint_norming_cotangent
    (q : RealPeriodOneHillPotential) (k : ℕ) (hk : 1≤k)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 k≠0)
    (hlog : hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk=0)
    (d μ ε : Coeff 2 → ℂ)
    (hd : AnalyticAt ℂ d (SpectralWeight.one.toCoeff q.val))
    (hμ : AnalyticAt ℂ μ (SpectralWeight.one.toCoeff q.val))
    (hε : AnalyticAt ℂ ε (SpectralWeight.one.toCoeff q.val))
    (hd0 : d (SpectralWeight.one.toCoeff q.val)=(hillRealGapHalfLength q.val q.property.1 q.property.2 k : ℂ))
    (hμ0 : μ (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ))
    (hroot : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (μ p)=0)
    (htrig : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),
      Complex.sin (ε p)=I*hillDirichletSheetRoot p (μ p)/
        (d p*hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k (μ p,p))) :
    ∃ c : ℂ, c≠0 ∧ ∀ h : Coeff 2,
      (fderiv ℂ ε (SpectralWeight.one.toCoeff q.val)) h=
        c*hillPhysicalDirectionPairing h (hillLogNormingGradientCurve q k hk) := by
  let p0 := SpectralWeight.one.toCoeff q.val
  let R : Coeff 2 → ℂ := fun p => hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k (μ p,p)
  have hμbase : (hillDirichletEnergy q.val q.property.1 q.property.2 k hk : ℂ)∈
      segment ℝ (hillRealLabels q.val q.property.1 q.property.2 (2*k-1) : ℂ)
        (hillRealLabels q.val q.property.1 q.property.2 (2*k) : ℂ) :=
    ofReal_mem_ordered_segment _ _ _ (monotone_hillRealLabels q.val q.property.1 q.property.2 (by omega))
      (hillDirichletEnergy_mem_gap q.val q.property.1 q.property.2 k hk)
  have hdom : (μ p0,p0)∈hillLocalDeflatedRootDomain q.val q.property.1 q.property.2 k := by
    rw [hμ0]
    exact mem_hillLocalDeflatedRootDomain_base q.val q.property.1 q.property.2 k hk _
      (hillRealGapSegment_subset_intrinsic_contour_ball q.val q.property.1 q.property.2 k hk hμbase)
  have hR : AnalyticAt ℂ R p0 :=
    (analyticOnNhd_hillLocalDeflatedComplexRoot q.val q.property.1 q.property.2 k hk _ hdom).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id)
  have hRn : R p0≠0 := hillLocalDeflatedComplexRoot_ne_zero q.val q.property.1 q.property.2 k hk _ hdom
  have hdn : d p0≠0 := hd0 ▸ ofReal_ne_zero.mpr hgap
  let M : Coeff 2 → ℂ := fun p => (-1 : ℂ)^k*hillL2DirichletSlope p (μ p)
  let G : Coeff 2 → ℂ := fun p => Complex.log (M p)
  obtain ⟨hG,hGbase⟩ := hillDirichletLogBranch_analytic_base q k hk μ hμ hμ0
  have hG0 : G p0=0 := by
    dsimp only [G,M,p0]
    rw [hGbase,hlog,ofReal_zero]
  have hM : AnalyticAt ℂ M p0 :=
    analyticAt_const.mul ((analyticOnNhd_hillL2DirichletSlope_joint (μ p0,p0) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (μ p,p)) (hμ.prod analyticAt_id))
  have hMn : M p0≠0 := by
    dsimp only [M,p0]
    rw [hμ0,←hillDirichletMultiplier_ofReal]
    exact ofReal_ne_zero.mpr (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 k hk).ne'
  let A : Coeff 2 → ℂ := fun p => I*(-1 : ℂ)^k*2/(d p*R p)
  have hA : AnalyticAt ℂ A p0 := analyticAt_const.div (hd.mul hR) (mul_ne_zero hdn hRn)
  have hrel : (fun p => Complex.sin (ε p))=ᶠ[𝓝 p0] (fun p => A p*Complex.sinh (G p)) := by
    filter_upwards [hroot,htrig,hM.continuousAt.eventually_ne hMn] with p hp ht hm
    rw [ht,hillDirichletSheetRoot_eq_signed_sinh_of_exp p (μ p) (G p) k hp (Complex.exp_log hm)]
    dsimp only [A]
    ring
  have hsin0 : Complex.sin (ε p0)=0 := by
    calc
      _ = A p0*Complex.sinh (G p0) := hrel.self_of_nhds
      _ = 0 := by rw [hG0,Complex.sinh_zero,mul_zero]
  have hcos : Complex.cos (ε p0)≠0 := by
    intro hz
    have h := Complex.sin_sq_add_cos_sq (ε p0)
    rw [hsin0,hz] at h
    norm_num at h
  have hder := sineTerminal_fderiv_eq_norming_of_zero ε A G p0 hε hA hG hG0 hcos hrel
  refine ⟨A p0/Complex.cos (ε p0),div_ne_zero ?_ hcos,?_⟩
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero I_ne_zero (pow_ne_zero k (by norm_num))) (by norm_num))
      (mul_ne_zero hdn hRn)
  · intro h
    rw [hder]
    simp only [smul_apply,smul_eq_mul]
    congr 1
    rw [hillLogNormingGradient_represents_branch q k hk μ hμ hμ0 hroot h,
      hillPhysicalDirectionPairing_apply]

end NLS.KdV
