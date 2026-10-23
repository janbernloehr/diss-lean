import NLS.FunctionalAnalysis.RealSheetTraversal
import NLS.ZakharovShabat.SourceDirichletSpectralReachability
import NLS.ZakharovShabat.SourceDirichletRealSpectralSheet

/-! # Complete traversal of the actual Dirichlet spectral sheet

For every real Hilbert source, each indexed complete spectral flow reaches
every point of its original compact algebraic sheet. Both terminal signs
and both endpoints are covered; a collapsed sheet is attained at time zero.
-/
noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology NLS.Poisson NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceDirichletSpectralTraversal_factTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual complete source flow realizes any prescribed point of the
selected fixed spectral sheet, with no reachability premise. -/
theorem exists_sourceDirichletSpectralFlow_terminal_eq
    (k : ℤ) (φ : realTypeSourceLocus 2) (z : ℂ × ℂ)
    (hz : z ∈ sourceDirichletSpectralSheet (by simp) (by norm_num) k φ.val) :
    ∃ t : ℝ,
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (sourceDirichletSpectralFlow k φ t).val k,
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k
        (sourceDirichletSpectralFlow k φ t).val) = z := by
  let γ := sourceDirichletSpectralGlobalCurve k φ
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
  have hlevels := canonicalPeriodicEndpoints_discriminant_of_realType
    (by simp) (by norm_num) _ (periodOnePotential_mem φ.val) hreal k
  change Δ L = (if k % 2 = 0 then 2 else -2) ∧
    Δ R = (if k % 2 = 0 then 2 else -2) at hlevels
  have haCast : (a : ℂ) = L := Complex.ext rfl (by simpa only [ofReal_im] using hLRim.1.symm)
  have hbCast : (b : ℂ) = R := Complex.ext rfl (by simpa only [ofReal_im] using hLRim.2.symm)
  have hGa : G a = 0 := by
    dsimp only [G]
    rw [haCast,hlevels.1]
    split_ifs <;> norm_num
  have hGb : G b = 0 := by
    dsimp only [G]
    rw [hbCast,hlevels.2]
    split_ifs <;> norm_num
  have hzreal := sourceDirichletSpectralSheet_im_eq_zero (by simp) (by norm_num)
    (⟨φ.val,φ.property⟩ : realTypeSourceSubmodule 2) k z hz
  have hzI : z.1.re ∈ Icc a b := sourcePeriodicSegment_re_mem_Icc
    (by simp) (by norm_num) φ.val k z.1 hz.1
  have hzcast : (z.1.re : ℂ) = z.1 := Complex.ext rfl (by simpa only [ofReal_im] using hzreal.1.symm)
  have hzsheet : (-z.2.re/2)^2 = G z.1.re := by
    have hs : z.2^2 = (Δ z.1)^2-4 := hz.2
    rw [← hzcast] at hs
    have hr := congrArg Complex.re hs
    simp only [pow_two,mul_re,sub_re,hzreal.2,hΔreal z.1.re,mul_zero,sub_zero,
      show (4 : ℂ).re = 4 from rfl] at hr
    dsimp only [G]
    nlinarith
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
    obtain ⟨t,htx,htv⟩ := exists_point_of_complete_bounded_sheetODE x v F G a b
      hxder hvder hx hsheet hF hG hzeros hGend hGa hGb z.1.re (-z.2.re/2) hzI hzsheet
    refine ⟨t,Prod.ext (Complex.ext htx ((hμim t).trans hzreal.1.symm)) ?_⟩
    apply Complex.ext
    · change -(S t).re/2 = -z.2.re/2 at htv
      change (S t).re = z.2.re
      linarith
    · exact (hSim t).trans hzreal.2.symm
  · have hza : z.1.re = a := le_antisymm (hzI.2.trans hcollapse.symm.le) hzI.1
    have hx0a : x 0 = a := le_antisymm ((hx 0).2.trans hcollapse.symm.le) (hx 0).1
    have hz20 : z.2.re = 0 := by
      rw [hza,hGa] at hzsheet
      nlinarith
    have hv0 : v 0 = 0 := by
      have hs := hsheet 0
      rw [hx0a,hGa] at hs
      exact (sq_eq_zero_iff).mp hs
    refine ⟨0,Prod.ext (Complex.ext (hx0a.trans hza.symm) ((hμim 0).trans hzreal.1.symm)) ?_⟩
    apply Complex.ext
    · change -(S 0).re/2 = 0 at hv0
      change (S 0).re = z.2.re
      linarith
    · exact (hSim 0).trans hzreal.2.symm

/-- The terminal-pair range of the constructed global flow is exactly its
original algebraic spectral sheet, including collapsed sheets. -/
theorem range_dirichletTerminal_sourceDirichletSpectralFlow
    (k : ℤ) (φ : realTypeSourceLocus 2) :
    range (fun t : ℝ =>
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet
        (sourceDirichletSpectralFlow k φ t).val k,
      sourceBoundaryTerminalAntiDiscriminant (by simp) (by norm_num) .dirichlet k
        (sourceDirichletSpectralFlow k φ t).val)) =
      sourceDirichletSpectralSheet (by simp) (by norm_num) k φ.val := by
  apply Subset.antisymm
  · rintro z ⟨t,rfl⟩
    exact dirichletTerminal_mem_sourceDirichletSpectralGlobalCurve_fixedSheet k φ t
  · intro z hz
    exact exists_sourceDirichletSpectralFlow_terminal_eq k φ z hz

end NLS.ZakharovShabat
