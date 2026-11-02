import NLS.KdV.ClassicalHillPrimitiveReflection
import NLS.KdV.ClassicalHighContourMoments
import NLS.ComplexAnalysis.RealCircleIntegralReflection

/-! # Reality of actual Hill cubic contour moments

The primitive reflects with a minus conjugate, including the exact shift
i*n*pi. Reflection reverses the contour orientation, so the literal cubic
moments are real. This applies to the actual squared-frequency contours
with their exact Jacobian, and retains their common analytic neighborhoods.
Nonpositivity and action descent remain separate spectral obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

theorem classicalHillShiftedPrimitive_conj (n : ℕ+) (q : Curve ℂ)
    (hq : ∀ t, (q t).im = 0) (lambda : ℂ)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) :
    classicalHillContinuedPrimitive (conj lambda,q)+I*(n : ℂ)*Real.pi =
      -conj (classicalHillContinuedPrimitive (lambda,q)+I*(n : ℂ)*Real.pi) := by
  have hshift : conj (I*(n : ℂ)*Real.pi) = -(I*(n : ℂ)*Real.pi) := by simp
  rw [classicalHillContinuedPrimitive_conj q hq lambda ht,map_add,hshift]
  ring

/-- Actual cubic moments on admissible real-centered energy circles are
real, with the physical factor 1/pi retained. -/
theorem classicalHillContinuedMoment_im_eq_zero
    (n : ℕ+) (x r : ℝ) (hr : 0 < r) (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (hcircle : ∀ z ∈ sphere (x : ℂ) r, (z,q) ∈ classicalHillContinuationDomain) :
    (classicalHillContinuedMoment n x r q).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => (classicalHillContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3) x r hr (by
      intro z hz
      rw [classicalHillShiftedPrimitive_conj n q hq z (hcircle z hz),map_pow]
      ring)
  change ((Real.pi : ℂ)⁻¹ * ∮ z in C((x : ℂ),r),
    (classicalHillContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3).im = 0
  simp only [← ofReal_inv,mul_im,ofReal_re,ofReal_im,hi,mul_zero,zero_mul,add_zero]

/-- The exact squared-frequency contour moment is real whenever its
constructed primitive is defined on the contour. -/
theorem classicalHillHighContourMoment_im_eq_zero_of_coverage
    (n : ℕ+) (q : Curve ℂ) (hq : ∀ t, (q t).im = 0)
    (hcircle : ∀ z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4),
      (z^2,q) ∈ classicalHillContinuationDomain) :
    (classicalHillHighContourMoment n q).im = 0 := by
  let f : ℂ → ℂ := fun z =>
    (classicalHillContinuedPrimitive (z^2,q)+I*(n : ℂ)*Real.pi)^3*(2*z)
  have hi := circleIntegral_im_eq_zero_of_anti_conj f (Real.pi*(n : ℕ)) (Real.pi/4)
    (by positivity) (by
      intro z hz
      have hz' : z ∈ sphere ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) := by
        simpa only [ofReal_mul,ofReal_natCast] using hz
      dsimp only [f]
      rw [← map_pow, classicalHillShiftedPrimitive_conj n q hq (z^2) (hcircle z hz')]
      simp only [map_mul,map_pow,map_ofNat]
      ring)
  change ((Real.pi : ℂ)⁻¹ * ∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), f z).im = 0
  have hi' : (∮ z in C((Real.pi : ℂ)*(n : ℕ),Real.pi/4), f z).im = 0 := by
    simpa only [ofReal_mul,ofReal_natCast] using hi
  simp only [← ofReal_inv,mul_im,ofReal_re,ofReal_im,hi',mul_zero,zero_mul,add_zero]

/-- For every continuous potential there is one complex open neighborhood
and cutoff supporting all analytic high moments, real at every real
potential in the neighborhood. No separate avoidance input is required. -/
theorem exists_analytic_real_classicalHillHighContourMoments (q : Curve ℂ) :
    ∃ N : ℕ, ∃ V : Set (Curve ℂ), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N < (n : ℕ) → AnalyticOnNhd ℂ (classicalHillHighContourMoment n) V ∧
        ∀ a ∈ V, (∀ t, (a t).im = 0) → (classicalHillHighContourMoment n a).im = 0 := by
  obtain ⟨Nc,Vc,hNc,hVc,hqc,hcover⟩ := exists_classicalHill_high_contour_neighborhood q
  obtain ⟨Na,Va,_,hVa,hqa,hana⟩ := exists_analytic_classicalHillHighContourMoments q
  refine ⟨max Nc Na,Vc ∩ Va,hNc.trans_le (le_max_left _ _),hVc.inter hVa,⟨hqc,hqa⟩,?_⟩
  intro n hn
  refine ⟨(hana n ((le_max_right Nc Na).trans_lt hn)).mono inter_subset_right,?_⟩
  intro a ha hreal
  exact classicalHillHighContourMoment_im_eq_zero_of_coverage n a hreal
    (hcover a ha.1 n ((le_max_left Nc Na).trans_lt hn))

end NLS.KdV
