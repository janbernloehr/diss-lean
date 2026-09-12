import NLS.Fourier.SchwartzPeriodizationSmooth

/-!
# Smooth multiplier convergence in Schwartz space

Uniform convergence of every derivative of smooth temperate multipliers gives
convergence in the genuine Schwartz topology after multiplication by any fixed
Schwartz window. The proof controls every weighted Schwartz seminorm by a finite
Leibniz sum, retaining both the polynomial weight and derivative order.
-/

noncomputable section
open scoped ENNReal SchwartzMap FourierTransform ContDiff
namespace NLS.Fourier

/-- A finite family of window seminorms controls a product at the given weight and order. -/
def windowSeminormBound (k n : ℕ) (w : 𝓢(ℝ, ℂ)) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * SchwartzMap.seminorm ℂ k (n - j) w

theorem windowSeminormBound_nonneg (k n : ℕ) (w : 𝓢(ℝ, ℂ)) :
    0 ≤ windowSeminormBound k n w := by
  unfold windowSeminormBound
  positivity

/-- Uniform bounds on finitely many multiplier derivatives control each weighted product seminorm. -/
theorem seminorm_smulLeftCLM_le_of_deriv_le (w : 𝓢(ℝ, ℂ)) {f : ℝ → ℂ}
    (hf : f.HasTemperateGrowth) (k n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ j ≤ n, ∀ x : ℝ, ‖iteratedDeriv j f x‖ ≤ M) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.smulLeftCLM ℂ f w) ≤
      M * windowSeminormBound k n w := by
  apply SchwartzMap.seminorm_le_bound' ℂ k n _
    (mul_nonneg hM (windowSeminormBound_nonneg k n w))
  intro x
  rw [SchwartzMap.smulLeftCLM_apply hf]
  change |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => f y * w y) x‖ ≤ _
  rw [iteratedDeriv_fun_mul ((contDiff_infty.mp hf.1 n).contDiffAt) (w.smooth n).contDiffAt]
  calc
    _ ≤ |x| ^ k * ∑ j ∈ Finset.range (n + 1),
        ‖(n.choose j : ℂ) * iteratedDeriv j f x * iteratedDeriv (n - j) (w : ℝ → ℂ) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ j ∈ Finset.range (n + 1), |x| ^ k *
        ‖(n.choose j : ℂ) * iteratedDeriv j f x * iteratedDeriv (n - j) (w : ℝ → ℂ) x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), M *
        ((n.choose j : ℝ) * SchwartzMap.seminorm ℂ k (n - j) w) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range_succ_iff] at hj
      simp only [norm_mul, Complex.norm_natCast]
      calc
        _ = ((n.choose j : ℝ) * ‖iteratedDeriv j f x‖) *
            (|x| ^ k * ‖iteratedDeriv (n - j) (w : ℝ → ℂ) x‖) := by ring
        _ ≤ ((n.choose j : ℝ) * M) * SchwartzMap.seminorm ℂ k (n - j) w := by
          gcongr
          · exact hbound j hj x
          · exact w.le_seminorm' ℂ k (n - j) x
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Uniform convergence of all derivatives becomes Schwartz convergence after fixing a window. -/
theorem tendsto_schwartz_mul_of_tendstoUniformly_iteratedDeriv
    {ι : Type*} {l : Filter ι} {f : ι → ℝ → ℂ} {g : ℝ → ℂ}
    (hf : ∀ i, (f i).HasTemperateGrowth) (hg : g.HasTemperateGrowth)
    (h : ∀ n : ℕ, TendstoUniformly (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l)
    (w : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto (fun i => SchwartzMap.smulLeftCLM ℂ (f i) w) l
      (nhds (SchwartzMap.smulLeftCLM ℂ g w)) := by
  apply (schwartz_withSeminorms ℂ ℝ ℂ).tendsto_nhds _ _ |>.mpr
  rintro ⟨k, n⟩ ε hε
  let C := windowSeminormBound k n w
  have hC : 0 ≤ C := windowSeminormBound_nonneg k n w
  let δ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have he (j : ℕ) : ∀ᶠ i in l, ∀ x : ℝ,
      ‖iteratedDeriv j (f i) x - iteratedDeriv j g x‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using (Metric.tendstoUniformly_iff.mp (h j)) δ hδ
  have hall := (Finset.range (n + 1)).eventually_all.mpr (fun j _ => he j)
  filter_upwards [hall] with i hi
  change SchwartzMap.seminorm ℂ k n
    (SchwartzMap.smulLeftCLM ℂ (f i) w - SchwartzMap.smulLeftCLM ℂ g w) < ε
  rw [← sub_apply, ← SchwartzMap.smulLeftCLM_sub (hf i) hg]
  have hb : ∀ j ≤ n, ∀ x : ℝ, ‖iteratedDeriv j (f i - g) x‖ ≤ δ := by
    intro j hj x
    rw [iteratedDeriv_sub ((contDiff_infty.mp (hf i).1 j).contDiffAt)
      ((contDiff_infty.mp hg.1 j).contDiffAt)]
    exact (hi j (Finset.mem_range_succ_iff.mpr hj) x).le
  apply (seminorm_smulLeftCLM_le_of_deriv_le w ((hf i).sub hg) k n hδ.le hb).trans_lt
  change ε / (C + 1) * C < ε
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

/-- Fourier truncations of a periodized test converge after multiplication by any Schwartz window. -/
theorem tendsto_schwartz_mul_fourierPolynomial (g w : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto
      (fun s : Finset ℤ => SchwartzMap.smulLeftCLM ℂ
        (fourierPolynomial s (fourierCoeff (periodizationCLM g))) w)
      Filter.atTop (nhds (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w)) :=
  tendsto_schwartz_mul_of_tendstoUniformly_iteratedDeriv
    (fun s => fourierPolynomial_hasTemperateGrowth s _)
    (periodization_hasTemperateGrowth g) (fun n => tendstoUniformly_iteratedDeriv_periodization n g) w

/-- Every genuine tempered distribution can be passed through these windowed Fourier limits. -/
theorem tendsto_distribution_windowed_fourierPolynomial (T : 𝓢'(ℝ, ℂ)) (g w : 𝓢(ℝ, ℂ)) :
    Filter.Tendsto
      (fun s : Finset ℤ => T (SchwartzMap.smulLeftCLM ℂ
        (fourierPolynomial s (fourierCoeff (periodizationCLM g))) w))
      Filter.atTop (nhds (T (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w))) :=
  T.continuous.tendsto _ |>.comp (tendsto_schwartz_mul_fourierPolynomial g w)

/-- A polynomial multiplier on a Schwartz window is the corresponding finite wave sum. -/
theorem schwartz_mul_fourierPolynomial_eq_sum (w : 𝓢(ℝ, ℂ)) (s : Finset ℤ) (b : ℤ → ℂ) :
    SchwartzMap.smulLeftCLM ℂ (fourierPolynomial s b) w =
      ∑ n ∈ s, b n • SchwartzMap.smulLeftCLM ℂ (wave n) w := by
  unfold fourierPolynomial
  rw [SchwartzMap.smulLeftCLM_sum (F := ℂ)
    (g := fun n x => b n * wave n x)
    (fun n _ => (Function.HasTemperateGrowth.const (b n)).mul (wave_hasTemperateGrowth n))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hf : (fun x => b n * wave n x) = b n • wave n := rfl
  rw [hf, SchwartzMap.smulLeftCLM_smul (wave_hasTemperateGrowth n)]
  rfl

/-- Windowed Fourier reconstruction converges in the full Schwartz topology. -/
theorem hasSum_schwartz_windowed_fourier (g w : 𝓢(ℝ, ℂ)) :
    HasSum
      (fun n : ℤ => fourierCoeff (periodizationCLM g) n •
        SchwartzMap.smulLeftCLM ℂ (wave n) w)
      (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w) := by
  have h := tendsto_schwartz_mul_fourierPolynomial g w
  simp_rw [schwartz_mul_fourierPolynomial_eq_sum] at h
  exact h

/-- Any tempered distribution acts on the windowed Fourier series term by term. -/
theorem hasSum_distribution_windowed_fourier (T : 𝓢'(ℝ, ℂ)) (g w : 𝓢(ℝ, ℂ)) :
    HasSum
      (fun n : ℤ => fourierCoeff (periodizationCLM g) n *
        T (SchwartzMap.smulLeftCLM ℂ (wave n) w))
      (T (SchwartzMap.smulLeftCLM ℂ
        (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w)) := by
  have h := tendsto_distribution_windowed_fourierPolynomial T g w
  simp_rw [schwartz_mul_fourierPolynomial_eq_sum, map_sum, map_smul, smul_eq_mul] at h
  exact h

/-- The scalar coefficient series is absolutely convergent for every tempered distribution. -/
theorem summable_norm_distribution_windowed_fourier (T : 𝓢'(ℝ, ℂ)) (g w : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ => ‖fourierCoeff (periodizationCLM g) n *
      T (SchwartzMap.smulLeftCLM ℂ (wave n) w)‖) :=
  (hasSum_distribution_windowed_fourier T g w).summable.norm

/-- An actual real-line distributional action equals its convergent windowed coefficient series. -/
theorem distribution_windowed_fourier_eq_tsum (T : 𝓢'(ℝ, ℂ)) (g w : 𝓢(ℝ, ℂ)) :
    T (SchwartzMap.smulLeftCLM ℂ
      (fun x : ℝ => periodizationCLM g (x : AddCircle (2 : ℝ))) w) =
      ∑' n : ℤ, fourierCoeff (periodizationCLM g) n *
        T (SchwartzMap.smulLeftCLM ℂ (wave n) w) :=
  (hasSum_distribution_windowed_fourier T g w).tsum_eq.symm

end NLS.Fourier
