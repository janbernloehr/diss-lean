import NLS.KdV.HillAnalyticQuadraticDirichletValue
import NLS.KdV.HillZeroNormingSheetFactors
import NLS.KdV.HillFilledRootIndexInverseBound
import NLS.KdV.HillUniformDirichletPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- The actual quadratic Dirichlet correction has a summably decaying norming
coefficient at a periodic terminal. The cutoff is uniform in the primitive
and its bound; the cotangent formula holds on every complex source direction. -/
theorem exists_hillQuadraticDirichletValue_endpoint_cotangent_bound :
    ∃ A : ℝ, 0<A ∧ ∀ B : ℝ, ∃ N : ℕ, ∃ hN : 1≤N,
      ∀ U : Set (Coeff 2), IsOpen U → U⊆ball (0 : Coeff 2) B →
      ∀ q : RealPeriodOneHillPotential, SpectralWeight.one.toCoeff q.val∈U →
      ∀ k : ℕ, ∀ hk : N≤k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k (hN.trans hk)=0 →
      ∀ H : ℂ × Coeff 2 → ℂ,
      AnalyticOnNhd ℂ H (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ U) →
      ∀ M : ℝ, 0≤M →
      (∀ p∈U, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4),
        ‖H (E,p)‖≤M/(k : ℝ)^3) →
      AnalyticAt ℂ (hillComplexQuadraticDirichletValue h0q h0r H k) (SpectralWeight.one.toCoeff q.val) ∧
      ∃ c : ℂ, ‖c‖≤A*M/(k : ℝ)^2 ∧ ∀ h : Coeff 2,
        (fderiv ℂ (hillComplexQuadraticDirichletValue h0q h0r H k) (SpectralWeight.one.toCoeff q.val)) h=
          c*hillPhysicalDirectionPairing h (hillLogNormingGradientCurve q k (hN.trans hk)) := by
  obtain ⟨Cf,hCf,hinverse⟩ := exists_hillFilledFreeGapRoot_index_inverse_bound h0q h0r
  refine ⟨2*Cf,by positivity,?_⟩
  intro B
  obtain ⟨Ni,hNi,hinv⟩ := hinverse B
  obtain ⟨Nm,hNm,hmu⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  obtain ⟨Np,hNp,hphysical⟩ := exists_hillScaledDirichletRoot_bounded_real_physical_matching
    h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Ni+Nm+Nr+Np,hNi.trans (by omega),?_⟩
  intro U _hU hUB q hqU k hk hlog H hH M hM hbound
  have hki : Ni≤k := by omega
  have hkm : Nm≤k := by omega
  have hkr : Nr≤k := by omega
  have hkp : Np≤k := by omega
  have hk1 : 1≤k := by omega
  have hkpos : 0<(k : ℝ) := by exact_mod_cast (show 0<k by omega)
  let p0 := SpectralWeight.one.toCoeff q.val
  let μ := hillScaledDirichletRoot h0q h0r (1/16) k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let a : ℂ := hillRealGapCenter 0 h0q h0r k
  have hp0 : p0∈ball (0 : Coeff 2) B := hUB hqU
  have hpB : ‖p0‖≤B := (show ‖p0‖<B by simpa only [mem_ball,dist_zero_right] using hp0).le
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hμsmall : μ p0∈ball a ((1/16)*R) := ((hmu k hkm).2 p0 hpB).1
  have hμK : μ p0∈closedBall a (R/4) :=
    closedBall_subset_closedBall (by linarith : (1/16)*R≤R/4) (ball_subset_closedBall hμsmall)
  have hμB : μ p0∈ball a (3*R/4) := ball_subset_ball (by linarith : (1/16)*R≤3*R/4) hμsmall
  have hμR : μ p0∈closedBall a R := closedBall_subset_closedBall (by linarith : R/4≤R) hμK
  have hμa : AnalyticAt ℂ μ p0 := (hmu k hkm).1 p0 hp0
  have hpair : AnalyticAt ℂ (fun p : Coeff 2 => (μ p,p)) p0 := hμa.prod analyticAt_id
  let V : Coeff 2 → ℂ := fun p => hillFilledFreeGapRoot h0q h0r k (μ p,p)
  have hV : AnalyticAt ℂ V p0 := ((hroot k hkr).1 (μ p0,p0) ⟨hμR,hp0⟩).comp (f := fun p : Coeff 2 => (μ p,p)) hpair
  have hVn : V p0≠0 := ((hroot k hkr).2 p0 hp0 (μ p0) hμR).2.1
  have hHV : AnalyticAt ℂ (fun p : Coeff 2 => H (μ p,p)) p0 :=
    (hH (μ p0,p0) ⟨hμB,hqU⟩).comp (f := fun p : Coeff 2 => (μ p,p)) hpair
  let F : Coeff 2 → ℂ := fun p => I/V p*H (μ p,p)
  have hF : AnalyticAt ℂ F p0 := (analyticAt_const.div hV hVn).mul hHV
  have hμ0 : μ p0=(hillDirichletEnergy q.val q.property.1 q.property.2 k hk1 : ℂ) :=
    hphysical q.val q.property.1 q.property.2 hpB k hkp
  have hchar : ∀ᶠ p in 𝓝 p0,hillL2DirichletCharacteristic p (μ p)=0 := by
    filter_upwards [isOpen_ball.mem_nhds hp0] with p hp
    have hp' : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hp).le
    exact ((hmu k hkm).2 p hp').2.1
  have hfactor : hillComplexQuadraticDirichletValue h0q h0r H k=
      (fun p => F p*hillDirichletSheetRoot p (μ p)) := by
    funext p
    dsimp only [hillComplexQuadraticDirichletValue,hillComplexDirichletGapTerminal,F,V,μ]
    ring
  have hsheet : AnalyticAt ℂ (fun p : Coeff 2 => hillDirichletSheetRoot p (μ p)) p0 :=
    (analyticOnNhd_hillDirichletSheetRoot_joint (μ p0,p0) (mem_univ _)).comp (f := fun p : Coeff 2 => (μ p,p)) hpair
  refine ⟨by rw [hfactor];exact hF.mul hsheet,
    F p0*((-1 : ℂ)^k*2),?_,?_⟩
  · have hi : ‖(V p0)⁻¹‖≤Cf*(k : ℝ) := hinv p0 hpB k hki (μ p0) hμR
    have hh := hbound p0 hqU (μ p0) hμK
    have hn : ‖F p0*((-1 : ℂ)^k*2)‖=2*(‖(V p0)⁻¹‖*‖H (μ p0,p0)‖) := by
      simp only [F,div_eq_mul_inv,norm_mul,norm_I,one_mul,norm_pow,norm_neg,norm_one,one_pow]
      norm_num; ring
    rw [hn]
    calc
      _ ≤ 2*((Cf*(k : ℝ))*(M/(k : ℝ)^3)) := by gcongr
      _ = (2*Cf)*M/(k : ℝ)^2 := by field_simp
  · intro h
    rw [hfactor]
    exact hillDirichletSheetFactor_zero_norming_fderiv q k hk1 hlog μ F hμa hF hμ0 hchar h

end NLS.KdV
