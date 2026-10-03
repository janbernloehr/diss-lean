import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Recovering a displacement in a stronger Banach space

If the derivative of a curve is represented by a continuous vector in a
second Banach space, integrating that vector recovers the displacement
through the bounded linear inclusion. The construction works on the
entire half-line before a positive terminal time, including negative times.
-/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.FunctionalAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Integration in `F` gives a continuous lift of the displacement of an
`E`-valued curve whenever its derivative has a continuous `F`-valued lift. -/
theorem exists_continuous_displacement_of_hasDerivAt
    (i : F →L[ℝ] E) (f : ℝ → E) (v : ℝ → F) {a : ℝ} (ha : 0 < a)
    (hv : ContinuousOn v (Iio a))
    (hf : ∀ t < a, HasDerivAt f (i (v t)) t) :
    ∃ d : ℝ → F, d 0 = 0 ∧ ContinuousOn d (Iio a) ∧
      (∀ t < a, HasDerivAt d (v t) t) ∧ ∀ t < a, i (d t) = f t-f 0 := by
  let d : ℝ → F := fun t => ∫ r in (0 : ℝ)..t, v r
  have hseg {t : ℝ} (ht : t < a) : uIcc (0 : ℝ) t ⊆ Iio a := by
    intro r hr
    exact lt_of_le_of_lt hr.2 (max_lt ha ht)
  have hint {t : ℝ} (ht : t < a) : IntervalIntegrable v volume 0 t :=
    (hv.mono (hseg ht)).intervalIntegrable
  have hd {t : ℝ} (ht : t < a) : HasDerivAt d (v t) t :=
    integral_hasDerivAt_right (hint ht) (hv.stronglyMeasurableAtFilter isOpen_Iio t ht)
      (hv.continuousAt (isOpen_Iio.mem_nhds ht))
  refine ⟨d,by simp [d],fun t ht => (hd ht).continuousAt.continuousWithinAt,
    fun t ht => hd ht,?_⟩
  intro t ht
  rw [← i.intervalIntegral_comp_comm (hint ht)]
  apply integral_eq_sub_of_hasDerivAt (fun r hr => hf r (hseg ht hr))
  exact (i.continuous.comp_continuousOn (hv.mono (hseg ht))).intervalIntegrable

end NLS.FunctionalAnalysis
