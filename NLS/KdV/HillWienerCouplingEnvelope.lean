import NLS.KdV.HillWienerCorrectedModeEnvelope
import NLS.KdV.PseudomeasureWeightedCoefficients

/-! Uniform summable envelopes for BOTH actual physical couplings.
The cutoff precedes the arbitrary spectral weight and every complex potential
in its Wiener norm ball. -/
noncomputable section
open scoped ENNReal
open NLS.WeightedCoeff
namespace NLS.KdV

theorem exists_uniform_hillWienerCoupling_envelope (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ w : SpectralWeight,
      ∀ q : WeightedCoeff (w.negativeSobolev 0) 1, ‖q‖ ≤ R →
        ∃ H : Coeff 1, ‖H‖ ≤ 2*‖q‖ ∧
          ∀ n : ℕ, 1 ≤ n → N ≤ n → ∀ z : ℂ, z ∈ reducedHillStrip n →
            let Q := exponentInclusion (w.negativeSobolev 0) (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q
            w (2*(n:ℤ))*‖endpointUpperCoupling 0 (by norm_num) (by norm_num) n
              (endpointForgetWeight w 0 Q,z)‖ ≤ ‖H (2*(n:ℤ))‖ ∧
            w (2*(n:ℤ))*‖endpointLowerCoupling 0 (by norm_num) (by norm_num) n
              (endpointForgetWeight w 0 Q,z)‖ ≤ ‖H (-(2*(n:ℤ)))‖ := by
  obtain ⟨NC,hNC,hC⟩ := exists_endpointHill_cutoff 0 (by norm_num) R
  obtain ⟨M,hM⟩ := exists_nat_ge (8*R)
  let N := max NC (max M 2)
  have hN : 2 ≤ N := by dsimp [N]; omega
  refine ⟨N,hN,?_⟩
  intro w q hq
  let Q := exponentInclusion (w.negativeSobolev 0) (show 1 ≤ (⊤:ℝ≥0∞) from le_top) q
  have hQ : ‖Q‖ ≤ R := (norm_exponentInclusion_le _ le_top q).trans hq
  have hcut : 8*‖q‖ ≤ (N:ℝ) := by
    calc
      _ ≤ 8*R := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ ≤ (M:ℝ) := hM
      _ ≤ _ := by exact_mod_cast (show M ≤ N by dsimp [N]; omega)
  obtain ⟨H,hH,hmode⟩ := exists_hillWienerCorrectedMode_envelope w q N (by omega) hcut
  refine ⟨H,hH,?_⟩
  intro n hn hNn z hz
  have hs : endpointHillConstant 0*(n:ℝ)^((0:ℝ)-1/2)*‖Q‖ ≤ 1/2 :=
    (mul_le_mul_of_nonneg_left hQ (by positivity [endpointHillConstant_pos 0 (by norm_num)])).trans
      (hC n (by dsimp [N] at hNn; omega))
  obtain ⟨_,hb,hc⟩ := endpointCoefficients_eq_weightedCorrectedModes w 0 (by norm_num) (by norm_num)
    n hn z hz Q hs
  change w (2*(n:ℤ))*‖endpointUpperCoupling 0 (by norm_num) (by norm_num) n
    (endpointForgetWeight w 0 Q,z)‖ ≤ ‖H (2*(n:ℤ))‖ ∧
    w (2*(n:ℤ))*‖endpointLowerCoupling 0 (by norm_num) (by norm_num) n
      (endpointForgetWeight w 0 Q,z)‖ ≤ ‖H (-(2*(n:ℤ)))‖
  constructor
  · apply (congrArg (fun c : ℂ => w (2*(n:ℤ))*‖c‖) hb).le.trans
    simpa only [show (n:ℤ)- -(n:ℤ) = 2*(n:ℤ) by ring] using
      hmode n hn hNn z hz hs (-(n:ℤ)) (Or.inr rfl) (n:ℤ)
  · apply (congrArg (fun c : ℂ => w (2*(n:ℤ))*‖c‖) hc).le.trans
    simpa only [show -(n:ℤ)-(n:ℤ) = -(2*(n:ℤ)) by ring, SpectralWeight.apply_neg] using
      hmode n hn hNn z hz hs (n:ℤ) (Or.inl rfl) (-(n:ℤ))

end NLS.KdV
