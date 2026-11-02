import NLS.KdV.PseudomeasureWideTail
import NLS.KdV.PseudomeasureLocalization
import NLS.KdV.PseudomeasureRealPairs

/-!
# Localization of actual singular eigenvectors on the wide strips

The physical eigenvector starts in the entire original H1 domain. Its
potential term has the proved endpoint regularity. The wide tail inverse
therefore controls the actual two-mode equation and forces it into the
already constructed narrow physical pair.
-/
noncomputable section
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
variable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (hn : 2 ≤ n)
variable (z : ℂ) (hz : z ∈ wideHillStrip n)
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
variable (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)

/-- The actual solved wide potential of the two original resonant amplitudes. -/
def wideEndpointHillEffectivePotential : (ℂ × ℂ) →L[ℂ]
    WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤ :=
  (wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs).comp
    (endpointHillModePotential r hr hr1 n q)

/-- Every physical eigenvector splits on the wide strip in the full original H1 domain. -/
theorem singularHillEigenvector_decompose_wide (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    f = endpointHillH1Modes n (endpointHillH1Coordinates n f) +
      wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz
        (endpointH1Multiplication r hr hr1 q f) := by
  have he := (singularHillOperator_eigen_iff _ z f).mp hf
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro k
  change f.val (mode (-k)) =
    (endpointHillH1Modes n (endpointHillH1Coordinates n f)).val (mode (-k)) +
      (wideEndpointHillResolventH1 SpectralWeight.one r hr1 n hn z hz
        (endpointH1Multiplication r hr hr1 q f)).val (mode (-k))
  rw [endpointHillH1Modes_coefficient,wideEndpointHillResolventH1_coefficient,
    endpointHillH1Coordinates_apply]
  by_cases hp : k = (n:ℤ)
  · subst k
    simp [wideHillSymbol,show (n:ℤ) ≠ -(n:ℤ) by omega]
  by_cases hm : k = -(n:ℤ)
  · subst k
    simp [wideHillSymbol,show -(n:ℤ) ≠ (n:ℤ) by omega]
  have hk : k.natAbs ≠ n := fun h => ((hill_resonance_iff n k).mp h).elim hp hm
  simp only [if_neg hp,if_neg hm,zero_add,wideHillSymbol,if_neg hk]
  have hkq := he k
  simp only [endpointHillHminusOne_coefficient] at hkq
  rw [← endpointH1Multiplication_apply r hr hr1 q f k] at hkq
  rw [← hkq,← mul_assoc,inv_mul_cancel₀ (wideHill_denominator_ne_zero n hn z hz k hk),one_mul]

/-- The physical potential term is uniquely the solved wide endpoint potential. -/
theorem singularHillEigenvector_potential_wide (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    endpointH1Multiplication r hr hr1 q f =
      wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (endpointHillH1Coordinates n f) := by
  apply wideEndpointHillTailInverse_unique SpectralWeight.one r hr hr1 n hn z hz q hs
  have he := congrArg (endpointH1Multiplication r hr hr1 q)
    (singularHillEigenvector_decompose_wide r hr hr1 n hn z hz q f hf)
  rw [map_add] at he
  have hR := congrArg (fun T => T (endpointH1Multiplication r hr hr1 q f))
    (endpointH1Multiplication_wideResolvent r hr hr1 n hn z hz q)
  simp only [ContinuousLinearMap.comp_apply] at hR
  rw [hR] at he
  exact sub_eq_iff_eq_add.mpr he

include hr hn hz hs in
/-- A nonzero actual wide-strip eigenvector has nonzero original resonant coordinates. -/
theorem singularHillEigenvector_wide_coordinates_ne_zero (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf0 : f ≠ 0)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) : endpointHillH1Coordinates n f ≠ 0 := by
  intro hu
  have hp := singularHillEigenvector_potential_wide r hr hr1 n hn z hz q hs f hf
  rw [hu,map_zero] at hp
  have hd := singularHillEigenvector_decompose_wide r hr hr1 n hn z hz q f hf
  rw [hu,hp,map_zero,map_zero,add_zero] at hd
  exact hf0 hd

/-- Every physical wide eigenvector satisfies the actual finite resonant equation. -/
theorem singularHillEigenvector_wide_equation (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    (z-(freeHillValue n:ℂ)) • endpointHillH1Coordinates n f =
      hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (endpointHillH1Coordinates n f)) := by
  have he := (singularHillOperator_eigen_iff _ z f).mp hf
  have hp := singularHillEigenvector_potential_wide r hr hr1 n hn z hz q hs f hf
  rw [← hp,endpointHillH1Coordinates_apply]
  apply Prod.ext
  · change (z-(freeHillValue n:ℂ))*f.val (mode (-(n:ℤ))) =
      (endpointH1Multiplication r hr hr1 q f).val n
    rw [endpointH1Multiplication_apply]
    simpa only [endpointHillHminusOne_coefficient] using he n
  · change (z-(freeHillValue n:ℂ))*f.val (mode (n:ℤ)) =
      (endpointH1Multiplication r hr hr1 q f).val (-(n:ℤ))
    rw [endpointH1Multiplication_apply]
    simpa only [endpointHillHminusOne_coefficient,freeHillValue_neg,neg_neg] using he (-(n:ℤ))

/-- Sharp placement of the opposite shifts on the effective source columns. -/
theorem wideEndpointHillEffectivePotential_basis_shifted :
    SpectralWeight.one.negativeShiftedNorm r hr (-(n:ℤ)) ⊤
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) ≤ 2*‖q‖ ∧
    SpectralWeight.one.negativeShiftedNorm r hr (n:ℤ) ⊤
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) ≤ 2*‖q‖ := by
  constructor
  · change SpectralWeight.one.negativeShiftedNorm r hr (-(n:ℤ)) ⊤
      (wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
        (endpointHillModePotential r hr hr1 n q (1,0))) ≤ 2*‖q‖
    rw [endpointHillModePotential_basis_pos]
    have h := (negativeShiftedNorm_wideEndpointHillTailInverse_le SpectralWeight.one r hr hr1
      n hn z hz q hs (endpointHillModePotential r hr hr1 n q (1,0))).2
    rw [endpointHillModePotential_basis_pos] at h
    simpa only [SpectralWeight.negativeShiftedNorm_negativeModulation] using h
  · change SpectralWeight.one.negativeShiftedNorm r hr (n:ℤ) ⊤
      (wideEndpointHillTailInverse SpectralWeight.one r hr hr1 n hn z hz q hs
        (endpointHillModePotential r hr hr1 n q (0,1))) ≤ 2*‖q‖
    rw [endpointHillModePotential_basis_neg]
    have h := (negativeShiftedNorm_wideEndpointHillTailInverse_le SpectralWeight.one r hr hr1
      n hn z hz q hs (endpointHillModePotential r hr hr1 n q (0,1))).1
    rw [endpointHillModePotential_basis_neg] at h
    have hnorm := SpectralWeight.one.negativeShiftedNorm_negativeModulation r hr (-(n:ℤ)) q
    rw [neg_neg] at hnorm
    simpa only [hnorm] using h

/-- Both effective matrix columns have the exact endpoint-order growth bound. -/
theorem wideEndpointHillEffectiveCorrection_columns_le :
    ‖hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0))‖ ≤
        2*Weight.sobolev r (2*(n:ℤ))*‖q‖ ∧
    ‖hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
      (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1))‖ ≤
        2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  have hS : 1 ≤ Weight.sobolev r (2*(n:ℤ)) :=
    Real.one_le_rpow (le_add_of_nonneg_right (abs_nonneg _)) hr
  obtain ⟨hplus,hminus⟩ := wideEndpointHillEffectivePotential_basis_shifted r hr hr1 n hn z hz q hs
  constructor
  · apply max_le
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (-(n:ℤ))
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) (n:ℤ)
      simp only [add_neg_cancel, Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero,
        Real.one_rpow, mul_one] at h
      exact h.trans (hplus.trans (by nlinarith [norm_nonneg q]))
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (-(n:ℤ))
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (1,0)) (-(n:ℤ))
      rw [show -(n:ℤ)+ -(n:ℤ) = -(2*(n:ℤ)) by omega, Weight.sobolev_neg] at h
      exact h.trans ((mul_le_mul_of_nonneg_right hplus ((Weight.sobolev r).positive _).le).trans_eq (by ring))
  · apply max_le
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (n:ℤ)
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) (n:ℤ)
      rw [show (n:ℤ)+(n:ℤ) = 2*(n:ℤ) by omega] at h
      exact h.trans ((mul_le_mul_of_nonneg_right hminus ((Weight.sobolev r).positive _).le).trans_eq (by ring))
    · have h := norm_apply_le_negativeShiftedNorm_one r hr (n:ℤ)
        (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs (0,1)) (-(n:ℤ))
      simp only [neg_add_cancel, Weight.sobolev_apply, Int.cast_zero, abs_zero, add_zero,
        Real.one_rpow, mul_one] at h
      exact h.trans (hminus.trans (by nlinarith [norm_nonneg q]))


include hr hn hz hs in
/-- The actual wide-strip resonant equation localizes every original H1 eigenvector. -/
theorem singularHillEigenvector_localization_wide_raw (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf0 : f ≠ 0)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) :
    ‖z-(freeHillValue n:ℂ)‖ ≤ 4*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
  let u := endpointHillH1Coordinates n f
  let E := (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n).comp
    (wideEndpointHillEffectivePotential r hr hr1 n hn z hz q hs)
  have hu0 : u ≠ 0 := singularHillEigenvector_wide_coordinates_ne_zero r hr hr1 n hn z hz q hs f hf0 hf
  have he : (z-(freeHillValue n:ℂ)) • u = E u :=
    singularHillEigenvector_wide_equation r hr hr1 n hn z hz q hs f hf
  obtain ⟨h1,h2⟩ := wideEndpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs
  change ‖E (1,0)‖ ≤ 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ at h1
  change ‖E (0,1)‖ ≤ 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ at h2
  have hsplit : E u = u.1 • E (1,0)+u.2 • E (0,1) := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp
  have hb : ‖E u‖ ≤ (4*Weight.sobolev r (2*(n:ℤ))*‖q‖)*‖u‖ := by
    rw [hsplit]
    apply (norm_add_le _ _).trans
    rw [norm_smul,norm_smul]
    have hA := mul_le_mul (norm_fst_le u) h1 (norm_nonneg _) (norm_nonneg _)
    have hB := mul_le_mul (norm_snd_le u) h2 (norm_nonneg _) (norm_nonneg _)
    nlinarith
  rw [← he,norm_smul] at hb
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hu0)).mp hb

/-- The explicit wide cutoff also satisfies the original narrow cutoff. -/
theorem endpointHill_small_of_wide_small (r : ℝ) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2) :
    endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2 := by
  have hC : 0 ≤ endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ :=
    mul_nonneg (mul_nonneg (endpointHillConstant_pos r hr1).le
      (Real.rpow_nonneg (by positivity) _)) (norm_nonneg q)
  nlinarith

include hr hn hz hs in
/-- Every actual wide-strip eigenvalue has the tight original sqrt(n)/4 localization. -/
theorem singularHillEigenvector_localization_wide (f : FourierLebesgueSpace (2:ℝ) 1 2)
    (hf0 : f ≠ 0)
    (hf : singularHillOperator (endpointHillHminusOne SpectralWeight.one r hr1 q) f =
      z • singularHillDomainInclusion f) : ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  have hloc := singularHillEigenvector_localization_wide_raw r hr hr1 n hn z hz q hs f hf0 hf
  have hM := endpoint_effective_column_small r hr hr1 n (by omega) q
    (endpointHill_small_of_wide_small r hr1 n q hs)
  linarith

include hr hn hz hs in
/-- Actual physical spectrum on a wide strip lies in its already checked narrow strip. -/
theorem endpointHillSpectrum_wide_localization (hzsp : z ∈ endpointHillSpectrum r hr1 q) :
    z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  obtain ⟨f,hf0,hf⟩ := (mem_endpointHillSpectrum_iff r hr hr1 q z).mp hzsp
  have hloc := singularHillEigenvector_localization_wide r hr hr1 n hn z hz q hs f hf0 hf
  refine ⟨?_,hloc⟩
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith⟩
  have hRe := Complex.abs_re_le_norm (z-(freeHillValue n:ℂ))
  change |z.re-freeHillValue n| ≤ 6*(n:ℝ)
  simp only [Complex.sub_re,Complex.ofReal_re] at hRe
  linarith

/-- Every sufficiently high actual real-endpoint spectral point lies in a
narrow strip, so none can occur in the gaps between the constructed high strips. -/
theorem endpointHillSpectrum_real_high_cover (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (z : ℂ) (hz : z ∈ endpointHillSpectrum r hr1 q)
    (hhigh : freeHillValue N-12*(N:ℝ) ≤ z.re) :
    ∃ n : ℕ, N ≤ n ∧ z ∈ reducedHillStrip n ∧ ‖z-(freeHillValue n:ℂ)‖ ≤ Real.sqrt (n:ℝ)/4 := by
  have hi := endpointHillSpectrum_im_eq_zero r hr hr1 q hq z hz
  have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [hi]
  obtain ⟨n,hn,hwide⟩ := exists_wideHillStrip_of_ge_lower_edge N hN z.re hhigh
  rw [he] at hwide
  exact ⟨n,hn,endpointHillSpectrum_wide_localization r hr hr1 n (hN.trans hn) z hwide q (hs n hn) hz⟩

/-- Any family of the constructed physical pairs exhausts the actual high
spectrum. The central cluster and its global labeling offset are still separate. -/
theorem endpointHillSpectrum_high_iff_pair (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hq : (endpointHillHminusOne SpectralWeight.one r hr1 q).val =
      (endpointHillHminusOne SpectralWeight.one r hr1 q).val.conjugate)
    (N : ℕ) (hN : 2 ≤ N)
    (hs : ∀ n : ℕ, N ≤ n → 13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (P : (n : ℕ) → N ≤ n → EndpointHillRealPair r hr hr1 q n)
    (z : ℂ) (hhigh : freeHillValue N-12*(N:ℝ) ≤ z.re) :
    z ∈ endpointHillSpectrum r hr1 q ↔
      ∃ (n : ℕ) (hn : N ≤ n), z = ((P n hn).left:ℂ) ∨ z = ((P n hn).right:ℂ) := by
  constructor
  · intro hz
    obtain ⟨n,hn,hnarrow,_⟩ := endpointHillSpectrum_real_high_cover r hr hr1 q hq N hN hs z hz hhigh
    exact ⟨n,hn,((P n hn).spectrum_iff z hnarrow).mp hz⟩
  · rintro ⟨n,hn,he | he⟩
    · rw [he]
      exact (P n hn).left_spectral
    · rw [he]
      exact (P n hn).right_spectral

end NLS.KdV
