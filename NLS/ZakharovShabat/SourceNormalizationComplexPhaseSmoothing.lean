import NLS.ZakharovShabat.SourceNormalizedActionComplexSobolevDecay
import NLS.ZakharovShabat.SourceBetaComplexPhaseSmoothing

/-! # Complex normalization and phase smoothing

The actual normalization-times-beta-phase error gains one derivative on every real sequence order and every Banach exponent, with an explicit exponential bound.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The exact normalization-times-beta-phase error has inverse-bracket decay on one complex Sobolev neighborhood. -/
theorem exists_local_normalizedSobolevNormalizationPhase_decay (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ (n : ℤ) (t : ℝ),
        (1+|(n:ℝ)|)*‖sourceNormalizedActionRoot (by simp) (by norm_num) n
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)*
          exp ((t:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s
            (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))-1‖ ≤
          K*(|t|+1)*Real.exp (|t| *K) := by
  obtain ⟨Vr,hVr,hφr,R,hR,hroot⟩ := exists_local_normalizedSobolevRootDeviation_decay φ
  obtain ⟨Vb,hVb,hφb,B,hB,hbeta⟩ := D.exists_local_normalizedSobolevBetaCorrection_decay φ
  let K := R+B
  have hK : 0 ≤ K := add_nonneg hR hB
  refine ⟨Vr ∩ Vb,hVr.inter hVb,⟨hφr,hφb⟩,K,hK,?_⟩
  intro ψ hψ n t
  let χ := normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ
  let ξ := sourceNormalizedActionRoot (by simp) (by norm_num) n χ
  let β := sourceAngularBetaCorrection (by simp) (by norm_num) n s χ
  let b := 1+|(n:ℝ)|
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hr : b*‖ξ-1‖ ≤ K := (hroot ψ hψ.1 n).trans (le_add_of_nonneg_right hB)
  have hβ : b*‖β‖ ≤ K := (hbeta ψ hψ.2 n).trans (le_add_of_nonneg_left hR)
  have hβ0 : ‖β‖ ≤ K := by
    dsimp only [b] at hβ
    nlinarith [abs_nonneg (n:ℝ),norm_nonneg β]
  let u := (t:ℂ)*I*β
  have hu : ‖u‖ = |t| *‖β‖ := by
    simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  have hexp : ‖exp u‖ ≤ Real.exp (|t| *K) :=
    (Complex.norm_exp_le_exp_norm u).trans (Real.exp_le_exp.mpr (by rw [hu]; gcongr))
  have herr : ‖exp u-1‖ ≤ |t| *‖β‖*Real.exp (|t| *K) := by
    have h := NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp u
    rw [hu] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hβ0 (abs_nonneg t))) (by positivity))
  have heq : ξ*exp u-1 = (ξ-1)*exp u+(exp u-1) := by ring
  have hnorm : ‖ξ*exp u-1‖ ≤ ‖ξ-1‖*Real.exp (|t| *K)+|t| *‖β‖*Real.exp (|t| *K) := by
    rw [heq]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hexp (norm_nonneg _)) herr
  change b*‖ξ*exp u-1‖ ≤ _
  calc
    _ ≤ b*(‖ξ-1‖*Real.exp (|t| *K)+|t| *‖β‖*Real.exp (|t| *K)) := mul_le_mul_of_nonneg_left hnorm hb
    _ = (b*‖ξ-1‖)*Real.exp (|t| *K)+(b*‖β‖)*(|t| *Real.exp (|t| *K)) := by ring
    _ ≤ K*Real.exp (|t| *K)+K*(|t| *Real.exp (|t| *K)) :=
      add_le_add (mul_le_mul_of_nonneg_right hr (by positivity)) (mul_le_mul_of_nonneg_right hβ (by positivity))
    _ = K*(|t|+1)*Real.exp (|t| *K) := by ring

/-- The actual complex normalization and beta-phase factors gain one derivative on every Banach sequence scale. -/
theorem exists_local_normalizedSobolevNormalizationPhase_smoothing (φ : realTypeSourceLocus 2) :
    ∃ U : Set (CoeffPair 2), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r t : ℝ),
          ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
            (∀ c n, (T c).val n = (sourceNormalizedActionRoot (by simp) (by norm_num) n
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)*
              exp ((t:ℂ)*I*sourceAngularBetaCorrection (by simp) (by norm_num) n s
                (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))-1)*c.val n) ∧
            ‖T‖ ≤ K*(|t|+1)*Real.exp (|t| *K) := by
  obtain ⟨U,hU,hφ,K,hK,h⟩ := D.exists_local_normalizedSobolevNormalizationPhase_decay φ
  refine ⟨U,hU,hφ,K,hK,?_⟩
  intro ψ hψ q hq r t
  exact WeightedCoeff.exists_sobolev_gain_multiplier r _ _ (by positivity) (fun n => h ψ hψ n t)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
