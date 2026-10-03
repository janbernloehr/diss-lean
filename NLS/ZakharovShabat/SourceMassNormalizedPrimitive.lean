import NLS.ZakharovShabat.SourceFloquetMassCoefficient
import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePrimitive
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Mass normalization of an actual upper-half-plane primitive

Every primitive of the critical-root quotient differs from the Floquet
logarithm by a constant along the sufficiently high imaginary ray. Removing
that constant produces a primitive on the whole upper half-plane with the
actual source mass as its first inverse-height coefficient.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- A global upper-half-plane primitive agrees with the Floquet logarithm
up to one constant along a terminal imaginary ray. -/
theorem exists_sourceUpperPrimitive_eq_log_add_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1)
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F
      (deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z /
        sourceCanonicalRoot (by simp) (by norm_num) φ z) z) :
    ∃ c : ℂ, ∀ᶠ y : ℝ in atTop,
      F ((y : ℂ)*I) = log (sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I)) + c := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (eventually_sourceFloquetMultiplier_mem_slitPlane_of_absolute φ hφ ha hb)
  let R := max T 0
  let q := fun z => deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z /
    sourceCanonicalRoot (by simp) (by norm_num) φ z
  have hpos (y : ℝ) (hy : y ∈ Ioi R) : 0 < y := lt_of_le_of_lt (le_max_right T 0) hy
  have hf (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => F ((y : ℂ)*I)) (q ((y : ℂ)*I)*I) y := by
    simpa only [one_mul, Function.comp_def] using!
      ((hF ((y : ℂ)*I) (by simpa using hpos y hy)).comp (y : ℂ)
        ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  have hg (y : ℝ) (hy : y ∈ Ioi R) :
      HasDerivAt (fun y : ℝ => log (sourceFloquetMultiplier (by simp) (by norm_num) φ ((y : ℂ)*I)))
        (q ((y : ℂ)*I)*I) y := by
    have hz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) φ hφ
      ((y : ℂ)*I) (by simpa using ne_of_gt (hpos y hy))
    have hl := hasDerivAt_log_sourceFloquetMultiplier (by simp) (by norm_num) φ hφ _ hz
      (hT y ((le_max_left T 0).trans hy.le))
    simpa only [one_mul, Function.comp_def] using!
      (hl.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).mul_const I)).comp_ofReal
  obtain ⟨c,hc⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq (convex_Ioi R).isPreconnected
    (fun y hy => (hf y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hg y hy).differentiableAt.differentiableWithinAt)
    (fun y hy => (hf y hy).deriv.trans (hg y hy).deriv.symm)
  exact ⟨c, (eventually_gt_atTop R).mono (fun y hy => hc hy)⟩

/-- An actual primitive on the entire upper half-plane can be normalized
so that its first inverse-height coefficient is the original source mass. -/
theorem exists_sourceUpperPrimitive_mass_normalized_of_absolute
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ))
    (ha : Memℓp (fun n : ℤ => φ.fst n) 1) (hb : Memℓp (fun n : ℤ => φ.snd n) 1) :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.im → HasDerivAt F
        (deriv (canonicalDiscriminant (by simp) (periodOnePotential φ)) z /
          sourceCanonicalRoot (by simp) (by norm_num) φ z) z) ∧
      Tendsto (fun y : ℝ => (2*y : ℂ)*(F ((y : ℂ)*I) - y)) atTop (𝓝 (sourceHilbertMass φ)) := by
  obtain ⟨G,hG⟩ := exists_sourceCriticalRootRatio_upperHalfPlane_primitive (by simp) (by norm_num) φ hφ
  obtain ⟨c,hc⟩ := exists_sourceUpperPrimitive_eq_log_add_of_absolute φ hφ ha hb G hG
  refine ⟨fun z => G z - c, fun z hz => (hG z hz).sub_const c, ?_⟩
  apply (tendsto_sourceFloquetMultiplier_log_sub_height_of_absolute φ hφ ha hb).congr'
  filter_upwards [hc] with y hy
  rw [hy, add_sub_cancel_right]

/-- Every real finite-gap Hilbert source has a global upper primitive with
coefficient exactly half its original source norm squared. -/
theorem exists_sourceUpperPrimitive_norm_normalized_finiteGap
    (φ : realTypeSourceSubmodule 2)
    (hfinite : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.im → HasDerivAt F
        (deriv (canonicalDiscriminant (by simp) (periodOnePotential φ.val)) z /
          sourceCanonicalRoot (by simp) (by norm_num) φ.val z) z) ∧
      Tendsto (fun y : ℝ => (2*y : ℂ)*(F ((y : ℂ)*I) - y)) atTop
        (𝓝 ((‖φ.val‖^2/2 : ℝ) : ℂ)) := by
  have h := sourceFiniteGap_memlp_one (by simp) (by norm_num) φ hfinite
  simpa only [sourceHilbertMass_eq_half_norm_sq_of_realType φ.val φ.property] using
    exists_sourceUpperPrimitive_mass_normalized_of_absolute φ.val φ.property h.1 h.2

end NLS.ZakharovShabat
