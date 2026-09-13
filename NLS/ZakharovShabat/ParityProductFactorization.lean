import NLS.ZakharovShabat.ParityLiteralCutoffs
import NLS.ZakharovShabat.ParitySpectralProducts

/-!
# Multiplying the literal parity products

The asymmetric odd cutoff contributes one extra positive boundary pair. Its
normalized factor tends to one, so multiplication recovers the correctly
normalized full product, without identifying functions merely by their zeros.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Split a symmetric index interval into its even and odd factors. -/
theorem prod_centralParityIndices_mul (f : ℤ → ℂ) (N : ℕ) :
    (∏ n ∈ centralParityIndices N 0, f n) * (∏ n ∈ centralParityIndices N 1, f n) =
      ∏ n ∈ Finset.Icc (-(N : ℤ)) N, f n := by
  have he : centralParityIndices N 1 =
      (Finset.Icc (-(N : ℤ)) N).filter (fun n => ¬ n % 2 = 0) := by
    ext n
    simp only [centralParityIndices, Finset.mem_filter]
    have hmod : n % 2 = 1 ↔ ¬ n % 2 = 0 := by omega
    change (_ ∧ n % 2 = 1) ↔ (_ ∧ ¬ n % 2 = 0)
    exact and_congr_right (fun _ => hmod)
  rw [he]
  exact Finset.prod_filter_mul_prod_filter_not _ (fun n : ℤ => n % 2 = 0) f

/-- The literal parity cutoffs multiply to the doubled full cutoff times one boundary pair. -/
theorem paritySpectralPairCutoffs_mul (ξ η : ℤ → ℂ) (z : ℂ) (M : ℕ) :
    evenSpectralPairCutoff ξ η z M * oddSpectralPairCutoff ξ η z M =
      spectralPairPartialProduct ξ η z (2*M) * spectralPairFactor ξ η z (2*(M : ℤ)+1) := by
  rw [evenSpectralPairCutoff, oddSpectralPairCutoff, prod_even_centralParityIndices,
    prod_odd_centralParityIndices]
  have he := prod_centralParityIndices_mul (spectralPairFactor ξ η z) (2*M)
  unfold spectralPairPartialProduct
  linear_combination -4 * spectralPairFactor ξ η z (2*(M : ℤ)+1) * he

variable {p : ℝ≥0∞}

private theorem tendsto_normalized_displacement (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    Tendsto (fun n : ℕ => (ξ n-(Real.pi : ℂ)*n-z)*((Real.pi : ℂ)*n)⁻¹) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := (hξ.of_exponent_ge le_top).bddAbove
  have hi : Tendsto (fun n : ℕ => ((Real.pi : ℂ)*n)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_inv_rev, zero_mul] using
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).mul_const (Real.pi : ℂ)⁻¹
  have hlim : Tendsto (fun n : ℕ => (C+‖z‖)*‖((Real.pi : ℂ)*n)⁻¹‖) atTop (𝓝 0) :=
    by simpa only [norm_zero, mul_zero] using hi.norm.const_mul (C+‖z‖)
  apply squeeze_zero_norm (fun n => ?_) hlim
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hb : ‖ξ n-(Real.pi : ℂ)*n‖ ≤ C := by simpa using hC (Set.mem_range_self (n : ℤ))
  exact (norm_sub_le _ _).trans (add_le_add hb le_rfl)

/-- A normalized paired factor tends to one along the positive indices. -/
theorem tendsto_spectralPairFactor_nat (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    Tendsto (fun n : ℕ => spectralPairFactor ξ η z n) atTop (𝓝 1) := by
  have h := ((tendsto_normalized_displacement ξ hξ z).const_add 1).mul
    ((tendsto_normalized_displacement η hη z).const_add 1)
  simp only [add_zero, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℤ) ≠ 0 := by omega
  have hd : (Real.pi : ℂ)*(n : ℤ) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Int.cast_ne_zero.mpr hn0)
  simp only [spectralPairFactor, if_neg hn0, Int.cast_natCast] at hd ⊢
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- The retained odd boundary factor tends to one for every fixed spectral parameter. -/
theorem tendsto_spectralPairFactor_oddBoundary (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    Tendsto (fun M : ℕ => spectralPairFactor ξ η z (2*(M : ℤ)+1)) atTop (𝓝 1) := by
  have ht : Tendsto (fun M : ℕ => 2*M+1) atTop atTop :=
    tendsto_atTop_mono (fun M => by dsimp; omega) tendsto_id
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (tendsto_spectralPairFactor_nat ξ η hξ hη z).comp ht

variable [Fact (1 ≤ p)]

/-- The entire even and odd products multiply to the normalized full paired product. -/
theorem paritySpectralPairProducts_mul (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) :
    evenSpectralPairProduct ξ η z * oddSpectralPairProduct ξ η z = entireSpectralPairProduct ξ η z := by
  have hl := ((tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η hξ hη).tendsto_at
    (Set.mem_univ z)).mul ((tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η hξ hη).tendsto_at
      (Set.mem_univ z))
  have ht : Tendsto (fun M : ℕ => 2*M) atTop atTop :=
    tendsto_atTop_mono (fun M => by dsimp; omega) tendsto_id
  have hr := (((tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η hξ hη).tendsto_at
    (Set.mem_univ z)).comp ht).mul (tendsto_spectralPairFactor_oddBoundary ξ η hξ hη z)
  simp only [mul_one] at hr
  exact tendsto_nhds_unique (hl.congr (fun M => paritySpectralPairCutoffs_mul ξ η z M)) hr

end NLS.ZakharovShabat
