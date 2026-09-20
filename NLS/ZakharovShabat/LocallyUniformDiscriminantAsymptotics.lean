import NLS.ZakharovShabat.LocallyUniformExteriorProducts
import NLS.ZakharovShabat.DiscriminantDerivativeRatio

/-!
# Discriminant asymptotics uniform near a potential

For each tolerance, a common open convex neighborhood and spectral threshold
control the additive trace error, additive derivative error, or derivative ratio.
The trace uses exp(abs(Im z)), preserving the free cosine zeros in the domain.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The additive trace asymptotic has a common potential neighborhood and spectral threshold. -/
theorem exists_uniform_discriminant_error_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
          ‖canonicalDiscriminant hp ψ z-freeDiscriminant z‖ ≤ ε*Real.exp |z.im| := by
  obtain ⟨U, ho, hconv, hφ, h0, R, hb⟩ := exists_uniform_exterior_canonicalProducts hp hp1 φ hr hrπ
    (by positivity : 0 < ε/4)
  refine ⟨U, ho, hconv, hφ, h0, R, ?_⟩
  intro ψ hψ heven z hz hsep
  have h := norm_discriminant_error_div_exp_le hp ψ z (notMem_freeLattice_of_separated hr hsep)
  have he := (hb ψ hψ heven z hz hsep).2.1
  have hn : ‖(canonicalDiscriminant hp ψ z-freeDiscriminant z)/(Real.exp |z.im| : ℂ)‖ ≤ ε := by
    linarith
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hn
  exact (div_le_iff₀ (Real.exp_pos _)).mp hn

/-- Cauchy's estimate gives the corresponding common neighborhood for the derivative error. -/
theorem exists_uniform_discriminant_derivative_error_exp (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
          ‖deriv (canonicalDiscriminant hp ψ) z+2*sin z‖ ≤ ε*Real.exp |z.im| := by
  let η := ε*(r/2)/Real.exp (r/2)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨U, ho, hconv, hφ, h0, R, hb⟩ := exists_uniform_discriminant_error_exp hp hp1 φ
    (half_pos hr) (by linarith) hη
  refine ⟨U, ho, hconv, hφ, h0, R+r/2, ?_⟩
  intro ψ hψ heven z hz hsep
  have hf : Differentiable ℂ (fun w => canonicalDiscriminant hp ψ w-freeDiscriminant w) := by
    intro w
    exact (analyticOnNhd_canonicalDiscriminant hp hp1 ψ heven w (mem_univ _)).differentiableAt.sub
      (hasDerivAt_freeDiscriminant w).differentiableAt
  have h := norm_deriv_le_of_exterior_exp_bound hf hr R η hη.le (hb ψ hψ heven) z hz hsep
  rw [deriv_discriminant_error hp hp1 ψ heven] at h
  have he : (η*Real.exp (|z.im|+r/2))/(r/2) = ε*Real.exp |z.im| := by
    rw [Real.exp_add]
    dsimp [η]
    field_simp
  exact h.trans_eq he

/-- The derivative ratio has a common neighborhood for each tolerance, as in Lemma 8.1(iii). -/
theorem exists_uniform_discriminant_derivative_div_free (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
          ‖deriv (canonicalDiscriminant hp ψ) z/(-2*sin z)-1‖ ≤ ε := by
  obtain ⟨C, hC, hc⟩ := exists_bound_exp_im_div_sin_of_separated hr
  obtain ⟨U, ho, hconv, hφ, h0, R, hb⟩ := exists_uniform_discriminant_derivative_error_exp hp hp1 φ
    hr hrπ (div_pos hε hC)
  refine ⟨U, ho, hconv, hφ, h0, R, ?_⟩
  intro ψ hψ heven z hz hsep
  have hnorm : ‖(deriv (canonicalDiscriminant hp ψ) z+2*sin z)/(Real.exp |z.im| : ℂ)‖ ≤ ε/C := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (hb ψ hψ heven z hz hsep)
  apply (norm_div_neg_two_sin_sub_one_le
    (sin_ne_zero_of_notMem_freeLattice (notMem_freeLattice_of_separated hr hsep)) hC.le (hc z hsep)).trans
  exact (mul_le_mul_of_nonneg_left hnorm hC.le).trans_eq (mul_div_cancel₀ ε hC.ne')

/-- The normalized trace error tends to zero when the potential converges and the spectral parameter escapes. -/
theorem tendsto_discriminant_error_of_potential_tendsto {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) {φ : PairSpace p} (ψ : α → PairSpace p)
    (hψ : Tendsto ψ l (𝓝 φ)) (heven : ∀ i, ψ i ∈ pairParitySubspace 0)
    (z : α → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => (canonicalDiscriminant hp (ψ i) (z i)-freeDiscriminant (z i))/
      (Real.exp |(z i).im| : ℂ)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, ho, _, hφ, _, R, hb⟩ := exists_uniform_discriminant_error_exp hp hp1 φ hr hrπ (half_pos hε)
  filter_upwards [hψ.eventually (ho.mem_nhds hφ), hz.eventually_ge_atTop R] with i hi hzi
  rw [dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact ((div_le_iff₀ (Real.exp_pos _)).mpr (hb (ψ i) hi (heven i) (z i) hzi (hsep i))).trans_lt (half_lt_self hε)

/-- The derivative ratio tends to one under simultaneous potential convergence and exterior spectral escape. -/
theorem tendsto_discriminant_derivative_ratio_of_potential_tendsto {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p) {φ : PairSpace p} (ψ : α → PairSpace p)
    (hψ : Tendsto ψ l (𝓝 φ)) (heven : ∀ i, ψ i ∈ pairParitySubspace 0)
    (z : α → ℂ) (hz : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => deriv (canonicalDiscriminant hp (ψ i)) (z i)/(-2*sin (z i))) l (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, ho, _, hφ, _, R, hb⟩ := exists_uniform_discriminant_derivative_div_free hp hp1 φ hr hrπ (half_pos hε)
  filter_upwards [hψ.eventually (ho.mem_nhds hφ), hz.eventually_ge_atTop R] with i hi hzi
  rw [dist_eq_norm]
  exact (hb (ψ i) hi (heven i) (z i) hzi (hsep i)).trans_lt (half_lt_self hε)

end NLS.ZakharovShabat
