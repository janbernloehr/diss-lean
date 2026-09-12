import NLS.Fourier.SchwartzTranslateProduct

/-!
# The kernel of periodization for arbitrary periodic distributions

Two convergent Schwartz translate-product series are interchanged by periodicity.
This proves that a periodic tempered distribution acts only on periodization,
using a normalized Schwartz window and retaining the period-two factor.
-/

noncomputable section
open scoped SchwartzMap ContDiff
namespace NLS.Fourier

/-- Actual invariance of a tempered distribution under translation of tests by two. -/
def IsPeriodTwoDistribution (T : 𝓢'(ℝ, ℂ)) : Prop :=
  ∀ g : 𝓢(ℝ, ℂ), T (SchwartzMap.compSubConstCLM ℂ 2 g) = T g

/-- Invariance by two implies invariance by every positive or negative integer multiple. -/
theorem IsPeriodTwoDistribution.translate_int {T : 𝓢'(ℝ, ℂ)} (hT : IsPeriodTwoDistribution T)
    (m : ℤ) (g : 𝓢(ℝ, ℂ)) :
    T (SchwartzMap.compSubConstCLM ℂ (2 * (m : ℝ)) g) = T g := by
  have hp : Function.Periodic (fun t : ℝ => T (SchwartzMap.compSubConstCLM ℂ t g)) 2 := by
    intro t
    simpa only [SchwartzMap.compSubConstCLM_comp] using hT (SchwartzMap.compSubConstCLM ℂ t g)
  simpa only [mul_comm (m : ℝ) 2, SchwartzMap.compSubConstCLM_zero, ContinuousLinearMap.id_apply] using
    hp.int_mul_eq m

private theorem translate_translatedSchwartzProduct (g w : 𝓢(ℝ, ℂ)) (m : ℤ) :
    SchwartzMap.compSubConstCLM ℂ (2 * (m : ℝ)) (translatedSchwartzProduct g w m) =
      translatedSchwartzProduct w g ((-m : ℤ) : ℝ) := by
  ext x
  simp only [SchwartzMap.compSubConstCLM_apply, translatedSchwartzProduct_apply, Int.cast_neg]
  have h₁ : x - 2 * (m : ℝ) + 2 * m = x := by ring
  have h₂ : x + 2 * -(m : ℝ) = x - 2 * m := by ring
  rw [h₁, h₂, mul_comm]

/-- Periodicity interchanges the two Schwartz factors in the periodized product action. -/
theorem IsPeriodTwoDistribution.periodization_exchange {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (g w : 𝓢(ℝ, ℂ)) :
    T (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w) =
    T (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => periodizationCLM w (x : AddCircle (2 : ℝ))) g) := by
  have ha := (hasSum_translatedSchwartzProduct g w).map T T.continuous
  have hb := (hasSum_translatedSchwartzProduct w g).map T T.continuous
  simp only [Function.comp_def] at ha hb
  have he (m : ℤ) : T (translatedSchwartzProduct g w m) = T (translatedSchwartzProduct w g ((-m : ℤ) : ℝ)) := by
    have h := hT.translate_int m (translatedSchwartzProduct g w m)
    rw [translate_translatedSchwartzProduct] at h
    exact h.symm
  have hb' := (Equiv.neg ℤ).hasSum_iff.mpr hb
  change HasSum (fun m : ℤ => T (translatedSchwartzProduct w g ((-m : ℤ) : ℝ))) _ at hb'
  simp_rw [← he] at hb'
  exact ha.unique hb'

/-- Every periodic distribution can be tested on the normalized windowed periodization. -/
theorem IsPeriodTwoDistribution.window_reconstruction {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) (g : 𝓢(ℝ, ℂ)) :
    T g = 2 * T (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) (coefficientTest 0)) := by
  have h := hT.periodization_exchange g (coefficientTest 0)
  have he : (fun x : ℝ => periodizationCLM (coefficientTest 0) (x : AddCircle (2 : ℝ))) =
      fun _ => (1 / 2 : ℂ) := by
    funext x
    simp
  rw [he, SchwartzMap.smulLeftCLM_const] at h
  change _ = T ((1 / 2 : ℂ) • g) at h
  rw [map_smul] at h
  change _ = (1 / 2 : ℂ) * T g at h
  rw [h]
  ring

/-- Arbitrary periodic distributions annihilate the entire kernel of periodization. -/
theorem IsPeriodTwoDistribution.eq_zero_of_periodization_eq_zero {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) {g : 𝓢(ℝ, ℂ)} (hg : periodizationCLM g = 0) : T g = 0 := by
  rw [hT.window_reconstruction g, hg]
  simp

/-- Any two Schwartz tests with equal periodization have the same periodic distributional action. -/
theorem IsPeriodTwoDistribution.eq_of_periodization_eq {T : 𝓢'(ℝ, ℂ)}
    (hT : IsPeriodTwoDistribution T) {g h : 𝓢(ℝ, ℂ)} (he : periodizationCLM g = periodizationCLM h) :
    T g = T h := by
  rw [hT.window_reconstruction g, hT.window_reconstruction h, he]

/-- Annihilating the periodization kernel is also sufficient for actual period-two invariance. -/
theorem isPeriodTwoDistribution_iff_annihilates_kernel (T : 𝓢'(ℝ, ℂ)) :
    IsPeriodTwoDistribution T ↔ ∀ g : 𝓢(ℝ, ℂ), periodizationCLM g = 0 → T g = 0 := by
  constructor
  · intro h g hg
    exact h.eq_zero_of_periodization_eq_zero hg
  · intro h g
    have hz := h (SchwartzMap.compSubConstCLM ℂ 2 g - g)
      (by rw [map_sub, periodization_translate_two, sub_self])
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz

end NLS.Fourier
