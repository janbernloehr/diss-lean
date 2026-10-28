import NLS.ZakharovShabat.ResonantCubicSupport
import NLS.ZakharovShabat.SourceCubicTailFamily

/-! # Normalized infinite cubic perturbation tails and the original three-mode family

These estimates support the unresolved final weighted gap sum on dissertation
p.44. They do not prove the actual counted-root gap asymptotics.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

open Filter Topology in
/-- At every fixed strip, the normalized fourth-power cubic error tends to zero. -/
theorem resonantCubicPerturbationSup_normalized_tendsto (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (m : ℤ) (i j : Fin 2) :
    Tendsto (fun s : ℝ => (resonantCubicPerturbationSup hp w A B m (s : ℂ) i j)^4/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hupper : Tendsto (fun s : ℝ => (w (2*m)*resonantCubicPerturbationBound hp w A B m j)^4*s^8)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => (w (2*m)*resonantCubicPerturbationBound hp w A B m j)^4*s^8)
        (𝓝 0) (𝓝 ((w (2*m)*resonantCubicPerturbationBound hp w A B m j)^4*(0 : ℝ)^8)) :=
      tendsto_const_nhds.mul (tendsto_id.pow 8)
    simpa using h.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun s => div_nonneg
    ((show Even (4 : ℕ) by decide).pow_nonneg _) (by positivity))) ?_ hupper
  have hs1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs1,self_mem_nhdsWithin] with s hs1 hs
  exact resonantCubicPerturbationSup_fourth_normalized hp w A B m s hs hs1.le i j

open Filter Topology in
/-- Finite support upgrades the stripwise limit to the actual infinite normalized sum. -/
theorem resonantCubicPerturbationSup_sum_normalized_tendsto (hp : p ≠ ⊤) (w : SpectralWeight)
    (A B : WeightedCoeffPair w.toWeight p) (n : ℤ) (i j : Fin 2)
    (hA : CubicFourierSupport w n A) (hB : CubicFourierSupport w n B)
    (hi : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) (N : ℕ) :
    Tendsto (fun s : ℝ => (∑' m : ℤ, if N ≤ m.natAbs then
      (resonantCubicPerturbationSup hp w A B m (s : ℂ) i j)^4 else 0)/s^12)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he (s : ℝ) : (∑' m : ℤ, if N ≤ m.natAbs then
      (resonantCubicPerturbationSup hp w A B m (s : ℂ) i j)^4 else 0)/s^12 =
      ∑ m ∈ Finset.Icc (-n) (2*n), if N ≤ m.natAbs then
        (resonantCubicPerturbationSup hp w A B m (s : ℂ) i j)^4/s^12 else 0 := by
    rw [tsum_eq_sum (s := Finset.Icc (-n) (2*n)) (fun m hm => by
      have hz := resonantCubicPerturbationSup_outside hp w A B n m (s : ℂ) i j hA hB hi (by
        simp only [Finset.mem_Icc] at hm
        omega)
      simp [hz]),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp
  simp_rw [he]
  have ht := tendsto_finsetSum (Finset.Icc (-n) (2*n))
    (f := fun m (s : ℝ) => if N ≤ m.natAbs then
      (resonantCubicPerturbationSup hp w A B m (s : ℂ) i j)^4/s^12 else 0)
    (a := fun _ => (0 : ℝ)) (by
    intro m hm
    by_cases hNm : N ≤ m.natAbs
    · simpa only [if_pos hNm] using resonantCubicPerturbationSup_normalized_tendsto hp w A B m i j
    · simpa only [if_neg hNm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0)))
  simpa using ht

section Four
local instance sourceCubicPerturbationFact : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

open Filter Topology in
/-- Both original-family cubic directions have a vanishing normalized infinite perturbation tail. -/
theorem sourceCubicTailFamily_cubic_perturbation_tail (n : ℤ) (hn : 0 < n) (N : ℕ) (i j : Fin 2)
    (hi : (i=0 ∧ j=1) ∨ (i=1 ∧ j=0)) :
    Tendsto (fun s : ℝ => (∑' m : ℤ, if N ≤ m.natAbs then
      (resonantCubicPerturbationSup (by simp) SpectralWeight.one
        (twoModeResonantPotential (p := 4) SpectralWeight.one n 1)
        (singleResonantPotential SpectralWeight.one n (sourceCubicTailScale n) (sourceCubicTailScale n))
        m (s : ℂ) i j)^4 else 0)/s^12) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  resonantCubicPerturbationSup_sum_normalized_tendsto (by simp) SpectralWeight.one _ _ n i j
    (twoModeResonantPotential_cubicSupport SpectralWeight.one n hn 1)
    (singleResonantPotential_cubicSupport SpectralWeight.one n hn.le (sourceCubicTailScale n) (sourceCubicTailScale n)) hi N

end Four
end NLS.ZakharovShabat
