import NLS.Articles.KdVConvexity.GlobalLogNormingCoordinates
import NLS.Articles.KdVConvexity.FreeDirichletLinearization
import NLS.KdV.HillHminusOneFreeLogNormingDifferential

/-! # The full bounded free Fourier derivative of the actual norming sequence

The bounded ratio (1+n)/n converts the H^-1 coefficient weight to the
original logarithmic norming normalization. The actual global analytic
ell2 map has this entire bounded derivative, at every Fourier index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.KdV

def dirichletNormingRatioSymbol : Coeff ⊤ :=
  ⟨fun k => (1+(actionIndexEquiv k : ℕ) : ℂ)/(actionIndexEquiv k : ℕ),memℓp_infty ⟨2,by
    rintro _ ⟨k,rfl⟩
    simp only [norm_div,Complex.norm_natCast]
    have he : ‖(1+(actionIndexEquiv k : ℕ) : ℂ)‖ = (1+(actionIndexEquiv k : ℕ) : ℝ) := by
      have hc : (1+(actionIndexEquiv k : ℕ) : ℂ) = ((1+(actionIndexEquiv k : ℕ) : ℝ) : ℂ) := by push_cast; rfl
      rw [hc,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    rw [he]
    have hn : (1 : ℝ) ≤ (actionIndexEquiv k : ℕ) := by exact_mod_cast (actionIndexEquiv k).property
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < (actionIndexEquiv k : ℕ))).mpr
    linarith⟩⟩

def freeDirichletLogNormingLinearization : PeriodOneHminusOne →L[ℂ] Coeff 2 :=
  let W := (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2).toContinuousLinearEquiv.toContinuousLinearMap
  let S := Coeff.hilbertSampleCLM positiveDirichletIndex
  let R := (Coeff.reflection (p := 2)).toContinuousLinearEquiv.toContinuousLinearMap
  (1/(4*I*(Real.pi : ℂ))) • (Coeff.multiplierCLM dirichletNormingRatioSymbol).comp
    (S.comp (R.comp W)-S.comp W)

theorem freeDirichletLogNormingLinearization_apply (h : PeriodOneHminusOne) (k : ℤ) :
    freeDirichletLogNormingLinearization h k =
      (h.val (-(actionIndexEquiv k : ℤ))-h.val (actionIndexEquiv k : ℤ))/
        (4*I*((actionIndexEquiv k : ℂ)*(Real.pi : ℂ))) := by
  have hw : (Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ) =
      (1+(actionIndexEquiv k : ℕ) : ℂ)⁻¹ := by
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_natCast,
      abs_of_nonneg (show (0 : ℝ) ≤ ((actionIndexEquiv k : ℕ) : ℝ) from Nat.cast_nonneg _),
      Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
  have hn : (actionIndexEquiv k : ℂ) ≠ 0 := by exact_mod_cast (actionIndexEquiv k).ne_zero
  have h1 : (1+(actionIndexEquiv k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (1+(actionIndexEquiv k : ℕ) : ℝ) ≠ 0)
  change (1/(4*I*(Real.pi : ℂ)))*(((1+(actionIndexEquiv k : ℕ) : ℂ)/(actionIndexEquiv k : ℕ))*
    ((Weight.sobolev (-1) (-(actionIndexEquiv k : ℤ)) : ℂ)*h.val (-(actionIndexEquiv k : ℤ))-
      (Weight.sobolev (-1) (actionIndexEquiv k : ℤ) : ℂ)*h.val (actionIndexEquiv k : ℤ))) = _
  rw [Weight.sobolev_neg,hw]
  field_simp

theorem DirichletLogNormingMap_hasFDerivAt_zero
    (Ω : Set PeriodOneHminusOne) (K : PeriodOneHminusOne → Coeff 2)
    (hreal : {q | IsRealPeriodOneHminusOne q} ⊆ Ω) (hK : AnalyticOnNhd ℂ K Ω)
    (hrec : ∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
      K p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ)) :
    HasFDerivAt K freeDirichletLogNormingLinearization 0 := by
  have hr : IsRealPeriodOneHminusOne 0 := by intro k; simp
  have h0 := hreal hr
  have hd : fderiv ℂ K 0 = freeDirichletLogNormingLinearization := by
    apply ContinuousLinearMap.ext
    intro h
    ext k
    let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k
    have hscalar : AnalyticAt ℂ (fun p => K p k) (0 : PeriodOneHminusOne) :=
      (ev.analyticAt _).comp (hK 0 h0)
    have he := ev.hasFDerivAt.comp 0 (hK 0 h0).differentiableAt.hasFDerivAt
    have he' : fderiv ℂ (fun p => K p k) 0 h = (fderiv ℂ K 0 h) k := by
      have hh := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) he.fderiv
      simpa only [Function.comp_def,ContinuousLinearMap.comp_apply] using! hh
    have hm : ∀ᶠ p : PeriodOneRealHminusOne in 𝓝 (⟨0,by intro j; simp⟩ : PeriodOneRealHminusOne),
        K p.val k = (hillHminusDirichletLogNorming p.val p.property (actionIndexEquiv k) : ℂ) :=
      Filter.Eventually.of_forall (fun p => by simpa only [Equiv.symm_apply_apply] using hrec p.val p.property (actionIndexEquiv k))
    rw [freeDirichletLogNormingLinearization_apply,← he']
    exact hillHminusDirichletLogNorming_extension_fderiv_zero (fun p => K p k) hscalar (actionIndexEquiv k) hm h
  rw [← hd]
  exact (hK 0 h0).differentiableAt.hasFDerivAt

theorem exists_global_analytic_Dirichlet_log_norming_with_free_linearization :
    ∃ Ω : Set PeriodOneHminusOne, ∃ K : PeriodOneHminusOne → Coeff 2,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ K Ω ∧
      (∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
        K p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ)) ∧
      K 0 = 0 ∧ HasFDerivAt K freeDirichletLogNormingLinearization 0 := by
  obtain ⟨Ω,K,hΩ,hreal,hK,hrec,hzero⟩ := exists_global_analytic_Dirichlet_log_norming
  exact ⟨Ω,K,hΩ,hreal,hK,hrec,hzero,DirichletLogNormingMap_hasFDerivAt_zero Ω K hreal hK hrec⟩

end NLS.Articles.KdVConvexity
