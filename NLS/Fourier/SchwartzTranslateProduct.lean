import NLS.Fourier.SchwartzSeries

/-!
# Summing products of translated Schwartz functions

Products of two Schwartz functions decay rapidly as their centers separate.
The weighted seminorms of the period-two translates have a summable inverse-
square bound. Consequently the translated products sum in Schwartz topology.
-/

noncomputable section
open scoped SchwartzMap ContDiff
namespace NLS.Fourier

private def bracketBound (k n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  2 ^ k * (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ ℝ ℂ) g

private theorem bracketBound_nonneg (k n : ℕ) (g : 𝓢(ℝ, ℂ)) : 0 ≤ bracketBound k n g := by
  unfold bracketBound
  positivity

private theorem bracket_derivative_le (k n : ℕ) (g : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (1 + |x|) ^ k * ‖iteratedDeriv n (g : ℝ → ℂ) x‖ ≤ bracketBound k n g := by
  simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, bracketBound, schwartzSeminormFamily] using!
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, n)) le_rfl le_rfl g x

private theorem separated_bracket_le (t x : ℝ) :
    1 + |t| ≤ (1 + |x|) * (1 + |x + 2 * t|) := by
  have h := abs_add_le (-x) (x + 2 * t)
  have he : -x + (x + 2 * t) = 2 * t := by ring
  rw [he, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  nlinarith [abs_nonneg t, abs_nonneg x, abs_nonneg (x + 2 * t),
    mul_nonneg (abs_nonneg x) (abs_nonneg (x + 2 * t))]

private theorem weighted_product_derivative_le (g w : 𝓢(ℝ, ℂ)) (k i j : ℕ) (t x : ℝ) :
    |x| ^ k * ‖iteratedDeriv i (g : ℝ → ℂ) (x + 2 * t)‖ *
        ‖iteratedDeriv j (w : ℝ → ℂ) x‖ ≤
      (bracketBound 2 i g * bracketBound (k + 2) j w) / (1 + |t|) ^ 2 := by
  have hb : (1 + |t|) ^ 2 * |x| ^ k ≤
      (1 + |x + 2 * t|) ^ 2 * (1 + |x|) ^ (k + 2) := by
    calc
      _ ≤ ((1 + |x|) * (1 + |x + 2 * t|)) ^ 2 * (1 + |x|) ^ k := by
        gcongr
        · exact separated_bracket_le t x
        · linarith
      _ = _ := by rw [pow_add, mul_pow]; ring
  have hg := bracket_derivative_le 2 i g (x + 2 * t)
  have hw := bracket_derivative_le (k + 2) j w x
  rw [le_div_iff₀ (by positivity)]
  calc
    _ = ((1 + |t|) ^ 2 * |x| ^ k) *
        (‖iteratedDeriv i (g : ℝ → ℂ) (x + 2 * t)‖ * ‖iteratedDeriv j (w : ℝ → ℂ) x‖) := by ring
    _ ≤ ((1 + |x + 2 * t|) ^ 2 * (1 + |x|) ^ (k + 2)) *
        (‖iteratedDeriv i (g : ℝ → ℂ) (x + 2 * t)‖ * ‖iteratedDeriv j (w : ℝ → ℂ) x‖) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ((1 + |x + 2 * t|) ^ 2 * ‖iteratedDeriv i (g : ℝ → ℂ) (x + 2 * t)‖) *
        ((1 + |x|) ^ (k + 2) * ‖iteratedDeriv j (w : ℝ → ℂ) x‖) := by ring
    _ ≤ _ := mul_le_mul hg hw (by positivity) (bracketBound_nonneg 2 i g)

/-- A translated Schwartz function multiplied by a fixed Schwartz window. -/
def translatedSchwartzProduct (g w : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (SchwartzMap.compSubConstCLM ℂ (-2 * t) g) w

@[simp] theorem translatedSchwartzProduct_apply (g w : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    translatedSchwartzProduct g w t x = g (x + 2 * t) * w x := by
  unfold translatedSchwartzProduct
  rw [SchwartzMap.smulLeftCLM_apply_apply (SchwartzMap.compSubConstCLM ℂ (-2 * t) g).hasTemperateGrowth]
  simp [sub_eq_add_neg]

private def translatedProductBound (g w : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * bracketBound 2 j g * bracketBound (k + 2) (n - j) w

private theorem translatedProductBound_nonneg (g w : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    0 ≤ translatedProductBound g w k n := by
  unfold translatedProductBound
  exact Finset.sum_nonneg (fun j _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (bracketBound_nonneg 2 j g))
    (bracketBound_nonneg (k + 2) (n - j) w))

/-- Every weighted seminorm decays at least quadratically in the translation index. -/
theorem seminorm_translatedSchwartzProduct_le (g w : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℂ k n (translatedSchwartzProduct g w t) ≤ C / (1 + |t|) ^ 2 := by
  refine ⟨translatedProductBound g w k n, translatedProductBound_nonneg g w k n, fun t => ?_⟩
  apply SchwartzMap.seminorm_le_bound' ℂ k n _ (div_nonneg (translatedProductBound_nonneg g w k n) (by positivity))
  intro x
  have he : (translatedSchwartzProduct g w t : ℝ → ℂ) = fun y => g (y + 2 * t) * w y :=
    funext (translatedSchwartzProduct_apply g w t)
  have hgshift : ContDiff ℝ n (fun y : ℝ => g (y + 2 * t)) := by
    simpa only [Function.comp_def] using! (g.smooth n).comp
      (contDiff_id.add (contDiff_const (c := 2 * t)))
  rw [he, iteratedDeriv_fun_mul hgshift.contDiffAt (w.contDiffAt n)]
  simp only [iteratedDeriv_comp_add_const]
  calc
    _ ≤ |x| ^ k * ∑ j ∈ Finset.range (n + 1),
        ‖(n.choose j : ℂ) * iteratedDeriv j (g : ℝ → ℂ) (x + 2 * t) * iteratedDeriv (n - j) (w : ℝ → ℂ) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ Finset.range (n + 1), |x| ^ k *
        ‖(n.choose j : ℂ) * iteratedDeriv j (g : ℝ → ℂ) (x + 2 * t) * iteratedDeriv (n - j) (w : ℝ → ℂ) x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), ((n.choose j : ℝ) * bracketBound 2 j g *
        bracketBound (k + 2) (n - j) w) / (1 + |t|) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, Complex.norm_natCast]
      have h := mul_le_mul_of_nonneg_left (weighted_product_derivative_le g w k j (n - j) t x)
        (Nat.cast_nonneg (n.choose j) : (0 : ℝ) ≤ n.choose j)
      convert h using 1 <;> ring
    _ = _ := by rw [← Finset.sum_div]; rfl

/-- The translated products are absolutely summable in every genuine Schwartz seminorm. -/
theorem summable_seminorm_translatedSchwartzProduct (g w : 𝓢(ℝ, ℂ)) (k n : ℕ) :
    Summable (fun m : ℤ => SchwartzMap.seminorm ℂ k n (translatedSchwartzProduct g w m)) := by
  obtain ⟨C, hC, hbound⟩ := seminorm_translatedSchwartzProduct_le g w k n
  apply Summable.of_nonneg_of_le (fun _ => apply_nonneg _ _) (fun m : ℤ => hbound (m : ℝ))
  have h := summable_inverse_bracket (by norm_num : (1 : ℝ) < 2)
  simpa only [Real.rpow_two, mul_one_div] using h.mul_left C

/-- Products of translates sum in the actual Schwartz topology. -/
theorem summable_translatedSchwartzProduct (g w : 𝓢(ℝ, ℂ)) :
    Summable (fun m : ℤ => translatedSchwartzProduct g w m) :=
  summable_schwartz_of_summable_seminorms _ (summable_seminorm_translatedSchwartzProduct g w)

/-- Summing translated products gives the window multiplied by the actual periodization. -/
theorem hasSum_translatedSchwartzProduct (g w : 𝓢(ℝ, ℂ)) :
    HasSum (fun m : ℤ => translatedSchwartzProduct g w m)
      (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w) := by
  have hs := summable_seminorm_translatedSchwartzProduct g w
  have he : schwartzSum (fun m : ℤ => translatedSchwartzProduct g w m) hs =
      SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w := by
    ext x
    rw [schwartzSum_apply, SchwartzMap.smulLeftCLM_apply_apply (periodization_hasTemperateGrowth g)]
    simp only [translatedSchwartzProduct_apply, smul_eq_mul]
    rw [tsum_mul_right, ← periodization_eq_tsum]
  rw [← he]
  exact hasSum_schwartzSum _ hs

end NLS.Fourier
