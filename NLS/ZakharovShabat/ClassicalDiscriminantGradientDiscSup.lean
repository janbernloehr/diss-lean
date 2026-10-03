import NLS.ZakharovShabat.ClassicalGradientSpectralDiscBounds
import NLS.ZakharovShabat.ClassicalCharacteristicGradientSummability

/-! # Summable disc suprema for the actual discriminant gradient

The supremum is taken before the outer ℓp norm, rather than along a chosen
spectral sequence. The disc contains the circles needed for G.7.
-/

noncomputable section
open Set Metric NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A common majorant controls every spectral point, potential, and observation simultaneously. -/
theorem exists_classicalDiscriminantGradient_disc_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ (n : ℤ) (z : ℂ),
      ‖z-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B →
      ‖classicalDiscriminantGradientFourierCoefficients
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq)
        (classicalSobolevPotential a) z P‖ ≤ b n := by
  let : Fact (1 ≤ q) := ⟨(ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))).trans hq.le⟩
  obtain ⟨b,hb,h⟩ := exists_classicalEndpointGradient_disc_uniform_memlp p hp q hq M hM B hB
  refine ⟨fun n => b n+b n,hb.add hb,?_⟩
  intro a ha P hP n z hz
  exact (norm_add_le _ _).trans (add_le_add
    (h a ha (1,0) (by simp) _ (ContinuousLinearMap.norm_fst_le ..) P hP n z hz)
    (h a ha (0,1) (by simp) _ (ContinuousLinearMap.norm_snd_le ..) P hP n z hz))

/-- The actual Fourier norm supremum over an entire spectral disc. -/
def classicalDiscriminantGradientFourierDiscSup {q : ℝ≥0∞} (hq : 1 < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (B : ℝ) (P : (ℂ × ℂ) →L[ℝ] ℂ) (n : ℤ) : ℝ :=
  sSup ((fun z => ‖classicalDiscriminantGradientFourierCoefficients hq (classicalSobolevPotential a) z P‖) ''
    closedBall ((Real.pi : ℂ)*(n : ℂ)) B)

/-- Uniform pointwise bounds control the genuine disc supremum, which is nonnegative. -/
theorem classicalDiscriminantGradientFourierDiscSup_bounds {q : ℝ≥0∞} (hq : 1 < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (B : ℝ) (hB : 0 ≤ B)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (n : ℤ) (b : ℝ)
    (h : ∀ z : ℂ, ‖z-(Real.pi : ℂ)*(n : ℂ)‖ ≤ B →
      ‖classicalDiscriminantGradientFourierCoefficients hq (classicalSobolevPotential a) z P‖ ≤ b) :
    0 ≤ classicalDiscriminantGradientFourierDiscSup hq a B P n ∧
      classicalDiscriminantGradientFourierDiscSup hq a B P n ≤ b := by
  let : Fact (1 ≤ q) := ⟨hq.le⟩
  let f := fun z => ‖classicalDiscriminantGradientFourierCoefficients hq (classicalSobolevPotential a) z P‖
  have hcenter : (Real.pi : ℂ)*(n : ℂ) ∈ closedBall ((Real.pi : ℂ)*(n : ℂ)) B := mem_closedBall_self hB
  have hb : BddAbove (f '' closedBall ((Real.pi : ℂ)*(n : ℂ)) B) := by
    refine ⟨b,?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact h z (by simpa only [mem_closedBall,dist_eq_norm] using hz)
  refine ⟨?_,csSup_le (Set.Nonempty.image f ⟨_,hcenter⟩) ?_⟩
  · exact (norm_nonneg _).trans (le_csSup hb (mem_image_of_mem f hcenter))
  · rintro _ ⟨z,hz,rfl⟩
    exact h z (by simpa only [mem_closedBall,dist_eq_norm] using hz)

/-- The actual disc suprema share a majorant over the full physical H¹ ball. -/
theorem exists_classicalDiscriminantGradient_discSup_uniform_memlp
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (M : ℝ) (hM : 0 ≤ M) (B : ℝ) (hB : 0 ≤ B) :
    ∃ b : ℤ → ℝ, Memℓp b (ENNReal.ofReal p) ∧
      ∀ (a : ScalarDomain 2 × ScalarDomain 2), ‖a‖ ≤ M →
      ∀ (P : (ℂ × ℂ) →L[ℝ] ℂ), ‖P‖ ≤ 1 → ∀ n : ℤ,
      0 ≤ classicalDiscriminantGradientFourierDiscSup
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a B P n ∧
      classicalDiscriminantGradientFourierDiscSup
        (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a B P n ≤ b n := by
  obtain ⟨b,hb,h⟩ := exists_classicalDiscriminantGradient_disc_uniform_memlp p hp q hq M hM B hB
  exact ⟨b,hb,fun a ha P hP n => classicalDiscriminantGradientFourierDiscSup_bounds _ a B hB P n (b n)
    (h a ha P hP n)⟩

/-- Taking the spectral-disc supremum preserves outer ℓp summability. -/
theorem memlp_classicalDiscriminantGradient_fourier_discSup
    (p : ℝ) (hp : 1 < p) (q : ℝ≥0∞) (hq : ENNReal.ofReal (1+1/p) < q)
    (a : ScalarDomain 2 × ScalarDomain 2) (B : ℝ) (hB : 0 ≤ B)
    (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (classicalDiscriminantGradientFourierDiscSup
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity))) hq) a B P)
      (ENNReal.ofReal p) := by
  obtain ⟨b,hb,h⟩ := exists_classicalDiscriminantGradient_disc_uniform_memlp p hp q hq
    ‖a‖ (norm_nonneg a) B hB
  apply hb.mono
  intro n
  obtain ⟨h0,hbound⟩ := classicalDiscriminantGradientFourierDiscSup_bounds _ a B hB P n (b n)
    (h a le_rfl P hP n)
  rw [Real.norm_eq_abs,abs_of_nonneg h0]
  exact hbound

/-- In particular, G.7's disc supremum is summable at the printed conjugate exponent. -/
theorem memlp_classicalDiscriminantGradient_conjugate_fourier_discSup
    (p : ℝ) (hp : 1 < p) (a : ScalarDomain 2 × ScalarDomain 2)
    (B : ℝ) (hB : 0 ≤ B) (P : (ℂ × ℂ) →L[ℝ] ℂ) (hP : ‖P‖ ≤ 1) :
    Memℓp (classicalDiscriminantGradientFourierDiscSup (q := ENNReal.ofReal (p/(p-1)))
      (lt_of_le_of_lt (ENNReal.one_le_ofReal.mpr (le_add_of_nonneg_right (by positivity)))
        (conjugate_exponent_ennreal_gt_gradient_threshold p hp)) a B P) (ENNReal.ofReal p) :=
  memlp_classicalDiscriminantGradient_fourier_discSup p hp _
    (conjugate_exponent_ennreal_gt_gradient_threshold p hp) a B hB P hP

end NLS.ZakharovShabat
