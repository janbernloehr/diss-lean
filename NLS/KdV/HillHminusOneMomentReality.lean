import NLS.KdV.HillHminusOneReflection
import NLS.KdV.HillHminusOneHighMoments
import NLS.ComplexAnalysis.RealCircleIntegralReflection

/-! # Reality of the actual H^-1 Arnold and cubic periods

The exact minus-conjugate primitive reflection and reversal of circle
orientation prove reality of the literal periods with their original
normalizations. One complex H^-1 neighborhood supports the whole high
family, with reality at each real potential in that neighborhood.
Nonpositivity remains a separate spectral assertion.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- Every integer-level Arnold period on an admissible real-centered
circle is real, without a high-energy assumption. -/
theorem hillHminusCircleMoment_im_eq_zero (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x r : ℝ) (hr : 0 < r)
    (hc : ∀ z ∈ sphere (x : ℂ) r, (z,q) ∈ hillHminusContinuationDomain) (m : ℕ) :
    (hillHminusSourceFamily.contourMoment x r m q).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => z^m*hillHminusContinuedPrimitive (z,q)) x r hr (by
      intro z hz
      rw [hillHminusContinuedPrimitive_conj q hq z (hc z hz),map_mul,map_pow]
      ring)
  change (-(Real.pi : ℂ)⁻¹ * ∮ z in C((x : ℂ),r), z^m*hillHminusContinuedPrimitive (z,q)).im = 0
  simp only [← ofReal_inv,← ofReal_neg,mul_im,ofReal_re,ofReal_im,hi,mul_zero,zero_mul,add_zero]

theorem hillHminusShiftedPrimitive_conj (n : ℕ) (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (z : ℂ) (ht : (z,q) ∈ hillHminusContinuationDomain) :
    hillHminusContinuedPrimitive (conj z,q)+I*(n : ℂ)*Real.pi =
      -conj (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi) := by
  have hshift : conj (I*(n : ℂ)*Real.pi) = -(I*(n : ℂ)*Real.pi) := by simp
  rw [hillHminusContinuedPrimitive_conj q hq z ht,map_add,hshift]
  ring

/-- The cubic moment uses precisely 1/pi and the indexed shift i*n*pi. -/
theorem hillHminusCubicCircleMoment_im_eq_zero (n : ℕ) (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) (x r : ℝ) (hr : 0 < r)
    (hc : ∀ z ∈ sphere (x : ℂ) r, (z,q) ∈ hillHminusContinuationDomain) :
    ((Real.pi : ℂ)⁻¹*∮ z in C((x : ℂ),r),
      (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3).im = 0 := by
  have hi := circleIntegral_im_eq_zero_of_anti_conj
    (fun z => (hillHminusContinuedPrimitive (z,q)+I*(n : ℂ)*Real.pi)^3) x r hr (by
      intro z hz
      rw [hillHminusShiftedPrimitive_conj n q hq z (hc z hz),map_pow]
      ring)
  simp only [← ofReal_inv,mul_im,ofReal_re,ofReal_im,hi,mul_zero,zero_mul,add_zero]

/-- All actual high Arnold and cubic periods are analytic on one complex
H^-1-open neighborhood and real at each real potential there. -/
theorem exists_analytic_real_hillHminusHighContourMomentFamilies (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) →
        (∀ m : ℕ, AnalyticOnNhd ℂ (hillHminusHighContourMoment (n : ℕ) m) V) ∧
        AnalyticOnNhd ℂ (hillHminusHighCubicContourMoment (n : ℕ)) V ∧
        ∀ a ∈ V, IsRealPeriodOneHminusOne a →
          (∀ m : ℕ, (hillHminusHighContourMoment (n : ℕ) m a).im = 0) ∧
            (hillHminusHighCubicContourMoment (n : ℕ) a).im = 0 := by
  obtain ⟨Na,Va,hNa,hVa,hqa,hana⟩ := exists_analytic_hillHminusHighContourMomentFamilies q
  obtain ⟨Nc,Vc,_,hVc,hqc,hcover⟩ := exists_hillHminus_high_energy_annulus_neighborhood q 1 (by norm_num)
  refine ⟨max Na Nc,Va ∩ Vc,hNa.trans_le (le_max_left _ _),hVa.inter hVc,⟨hqa,hqc⟩,?_⟩
  intro n hn
  have hna := (le_max_left Na Nc).trans hn
  have hnc := (le_max_right Na Nc).trans hn
  refine ⟨fun m => ((hana n hna).1 m).mono inter_subset_left,
    ((hana n hna).2).mono inter_subset_left,?_⟩
  intro a ha hreal
  have hc (z : ℂ) (hz : z ∈ sphere (freeHillValue (n : ℕ) : ℂ) (n : ℝ)) :
      (z,a) ∈ hillHminusContinuationDomain := by
    apply hcover a ha.2 n hnc z (sphere_subset_closedBall hz)
    simpa only [one_mul] using (mem_sphere_iff_norm.mp hz).ge
  exact ⟨fun m => hillHminusCircleMoment_im_eq_zero a hreal _ _ (by positivity) hc m,
    hillHminusCubicCircleMoment_im_eq_zero (n : ℕ) a hreal _ _ (by positivity) hc⟩

end NLS.KdV
