import NLS.FunctionalAnalysis.RealSheetEndpoint
import NLS.ZakharovShabat.RealOpenGapEndpointSimple
import NLS.ZakharovShabat.SourceDirichletSpectralGlobalSheet
import NLS.ZakharovShabat.SourceBoundaryEndpointCotangents

/-! # Actual spectral flow reaches a periodic terminal

The selected Dirichlet root moves in its fixed real periodic interval.
Its velocity is minus half the actual terminal anti-discriminant. The
two-coordinate equation and actual sheet identity give a bounded real
sheet trajectory. At an open-gap endpoint the acceleration is nonzero,
so this complete trajectory reaches an endpoint in finite real time.
Collapsed gaps are already at their periodic terminal.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology NLS.Poisson NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- For every real Hilbert source and every selected index, the
constructed complete actual flow reaches one of that index's original
periodic endpoints, with zero full terminal anti-discriminant. No
reachability, nonzero source norm, or open-gap premise is supplied. -/
theorem exists_sourceDirichletSpectralFlow_periodicTerminal
    (k : ℤ) (φ : realTypeSourceLocus 2) :
    ∃ t : ℝ,
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k
        (sourceDirichletSpectralFlow k φ t).val = 0 ∧
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (sourceDirichletSpectralFlow k φ t).val k =
        canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ∨
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (sourceDirichletSpectralFlow k φ t).val k =
        canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k) := by
  let γ := sourceDirichletSpectralGlobalCurve k φ
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  let μ : ℝ → ℂ := fun t => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet (γ t) k
  let S : ℝ → ℂ := fun t => sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k (γ t)
  let Δ : ℂ → ℂ := canonicalDiscriminant (by simp) (periodOnePotential φ.val)
  let L := canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k
  let R := canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k
  let a : ℝ := L.re
  let b : ℝ := R.re
  let x : ℝ → ℝ := fun t => (μ t).re
  let v : ℝ → ℝ := fun t => -(S t).re/2
  let F : ℝ → ℝ := fun y => (Δ (y:ℂ)*deriv Δ (y:ℂ)).re/4
  let G : ℝ → ℝ := fun y => ((Δ (y:ℂ)).re^2-4)/4
  have hreal := isRealType_periodOnePotential φ.val φ.property
  have hΔreal (y : ℝ) : (Δ (y:ℂ)).im = 0 :=
    canonicalDiscriminant_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem φ.val) hreal y
  have hΔderreal (y : ℝ) : (deriv Δ (y:ℂ)).im = 0 :=
    discriminant_derivative_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem φ.val) hreal y
  have hLRim : L.im = 0 ∧ R.im = 0 :=
    canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem φ.val) hreal k
  have hμim (t : ℝ) : (μ t).im = 0 :=
    canonicalPeriodOneBoundaryRoots_im_eq_zero (by simp) (by norm_num) .dirichlet
      (γ t) (sourceDirichletSpectralGlobalCurve_realType k φ t) k
  have hμcast (t : ℝ) : (x t : ℂ) = μ t :=
    Complex.ext rfl (by simpa only [ofReal_im] using (hμim t).symm)
  have hder (t : ℝ) : HasDerivAt μ (-S t/2) t ∧
      HasDerivAt S (-Δ (μ t)*deriv Δ (μ t)/2) t :=
    hasDerivAt_dirichletTerminal_sourceDirichletSpectralGlobalCurve k φ t
  have hSim (t : ℝ) : (S t).im = 0 := by
    have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hder t).1
    have he : (fun u => (μ u).im) = fun _ => (0 : ℝ) := funext hμim
    have hz : (-S t/2).im = 0 := by
      apply hd.unique
      simpa only [Function.comp_def,Complex.imCLM_apply,he] using hasDerivAt_const t (0 : ℝ)
    simp only [div_ofNat_im,neg_im] at hz
    linarith
  have hx : ∀ t, x t ∈ Icc a b := by
    intro t
    have hb := canonicalPeriodOneBoundaryRoots_mem_gap (by simp) (by norm_num) .dirichlet
      (γ t) (sourceDirichletSpectralGlobalCurve_realType k φ t) k
    have he := canonicalPeriodicEndpoints_sourceDirichletSpectralGlobalCurve k k φ t
    rw [he.1,he.2] at hb
    exact hb
  have hxder (t : ℝ) : HasDerivAt x (v t) t := by
    simpa only [Function.comp_def,Complex.reCLM_apply,div_ofNat_re,neg_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).1
  have hvder (t : ℝ) : HasDerivAt v (F (x t)) t := by
    have hd := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hder t).2).neg.div_const 2
    apply hd.congr_deriv
    change -((-Δ (μ t)*deriv Δ (μ t)/2).re)/2 = F (x t)
    dsimp only [F]
    rw [hμcast t]
    simp only [div_ofNat_re,neg_mul,neg_re,neg_div,neg_neg]
    ring
  have hsheet (t : ℝ) : (v t)^2 = G (x t) := by
    have hs := (dirichletTerminal_mem_sourceDirichletSpectralGlobalCurve_fixedSheet k φ t).2
    change (S t)^2 = (Δ (μ t))^2-4 at hs
    rw [← hμcast t] at hs
    have hr := congrArg Complex.re hs
    simp only [pow_two,mul_re,sub_re,hSim t,hΔreal (x t),mul_zero,sub_zero,
      show (4 : ℂ).re = 4 from rfl] at hr
    dsimp only [v,G]
    nlinarith
  have hGend (y : ℝ) (hy : y ∈ Icc a b) (hzero : G y = 0) : y = a ∨ y = b := by
    by_contra hn
    push Not at hn
    have hi : y ∈ Ioo a b := ⟨lt_of_le_of_ne hy.1 hn.1.symm,lt_of_le_of_ne hy.2 hn.2⟩
    have ht := two_lt_norm_discriminant_of_mem_canonicalGap_interior (by simp) (by norm_num) _
      (periodOnePotential_mem φ.val) hreal k y hi
    have hs := norm_canonicalDiscriminant_sq_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem φ.val) hreal y
    change ((Δ (y:ℂ)).re^2-4)/4 = 0 at hzero
    change ‖Δ (y:ℂ)‖^2 = (Δ (y:ℂ)).re^2 at hs
    nlinarith
  have hSzero : ∃ t : ℝ, S t = 0 := by
    have hab : a ≤ b := (hx 0).1.trans (hx 0).2
    rcases lt_or_eq_of_le hab with hopen | hcollapse
    · have hΔC : Continuous Δ :=
        (analyticOnNhd_canonicalDiscriminant (by simp) (by norm_num) _ (periodOnePotential_mem φ.val)).continuous
      have hΔ'C : Continuous (deriv Δ) :=
        (analyticOnNhd_discriminant_derivative (by simp) (by norm_num) _ (periodOnePotential_mem φ.val)).continuous
      have hF : Continuous F :=
        (continuous_re.comp ((hΔC.comp continuous_ofReal).mul (hΔ'C.comp continuous_ofReal))).div_const 4
      have hG : Continuous G :=
        ((continuous_re.comp (hΔC.comp continuous_ofReal)).pow 2 |>.sub continuous_const).div_const 4
      have hnonzero := deriv_discriminant_ne_zero_at_open_gap_endpoints
        (by simp) (by norm_num) _ (periodOnePotential_mem φ.val) hreal k hopen
      have hzeros (y : ℝ) (hy : y ∈ Icc a b) (hy0 : G y = 0) : F y ≠ 0 := by
        have hdy : deriv Δ (y:ℂ) ≠ 0 := by
          rcases hGend y hy hy0 with he | he
          · have hec : (y:ℂ) = L := Complex.ext he (by simpa using hLRim.1.symm)
            rw [hec]
            exact hnonzero.1
          · have hec : (y:ℂ) = R := Complex.ext he (by simpa using hLRim.2.symm)
            rw [hec]
            exact hnonzero.2
        have hdyre : (deriv Δ (y:ℂ)).re ≠ 0 :=
          fun he => hdy (Complex.ext he (hΔderreal y))
        have hval : (Δ (y:ℂ)).re ≠ 0 := by
          intro he
          change ((Δ (y:ℂ)).re^2-4)/4 = 0 at hy0
          rw [he] at hy0
          norm_num at hy0
        dsimp only [F]
        rw [mul_re,hΔreal y,hΔderreal y,mul_zero,sub_zero]
        exact div_ne_zero (mul_ne_zero hval hdyre) (by norm_num)
      obtain ⟨t,ht⟩ := exists_zero_velocity_of_bounded_sheetODE x v F G a b
        hxder hvder hx hsheet hF hG hzeros
      refine ⟨t,Complex.ext ?_ (hSim t)⟩
      change -(S t).re/2 = 0 at ht
      change (S t).re = 0
      linarith
    · have he : L = R := Complex.ext hcollapse (hLRim.1.trans hLRim.2.symm)
      have hμ0 : μ 0 = L := by
        dsimp only [μ,γ]
        rw [sourceDirichletSpectralGlobalCurve_zero]
        exact canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap (by simp) (by norm_num)
          .dirichlet φ.val φ.property k he
      refine ⟨0,?_⟩
      have h := sourceBoundaryTerminalAntiDiscriminant_eq_zero_of_endpoint
        (by simp) (by norm_num) .dirichlet k (γ 0) (Or.inl ?_)
      · exact h
      · change μ 0 = _
        rw [hzero]
        exact hμ0
  obtain ⟨t,ht⟩ := hSzero
  have hG0 : G (x t) = 0 := by rw [← hsheet t]; simp [v,ht]
  refine ⟨t,ht,?_⟩
  rcases hGend (x t) (hx t) hG0 with he | he
  · exact Or.inl (Complex.ext he ((hμim t).trans hLRim.1.symm))
  · exact Or.inr (Complex.ext he ((hμim t).trans hLRim.2.symm))

end NLS.ZakharovShabat
