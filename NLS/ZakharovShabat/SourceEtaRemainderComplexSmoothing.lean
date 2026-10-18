import NLS.ZakharovShabat.SourceWeightedEtaRemainderAnalytic
import NLS.SequenceSpaces.ComplexPhaseSmoothing

/-! # Complex eta-remainder phase smoothing

The normalized first-order decoder has spectral weight 1+|2n|. Its actual eta remainder has inverse-bracket decay, and the exact phase error gains one derivative.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W₀ B W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
include D

/-- The actual eta remainder has inverse-bracket decay on a complex normalized first-order Sobolev neighborhood. -/
theorem exists_local_normalizedSobolevEtaRemainder_decay (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖sourceAngularEtaRemainder hp hp1 n s
          (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ)‖ ≤ K := by
  let w := SpectralWeight.sobolev 1 (by norm_num)
  obtain ⟨U,hU,hφ,_,M,hM,h⟩ := D.exists_local_normalizedWeightedEtaRemainder_analytic w φ
  refine ⟨U,hU,hφ,M,hM,?_⟩
  intro ψ hψ n
  have hn := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (normalizedWeightedEtaRemainderSequence hp hp1 s w ψ) n).trans (h ψ hψ).1
  rw [(h ψ hψ).2 n,norm_mul,Complex.norm_real,Real.norm_of_nonneg (w.positive _).le] at hn
  apply le_trans _ hn
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [w,SpectralWeight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one,
    Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  linarith [abs_nonneg (n:ℝ)]

/-- Complex eta-remainder phase errors gain one derivative on every sequence scale, locally at weighted real sources. -/
theorem exists_local_normalizedSobolevEtaRemainder_phase_smoothing (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U,
        ∀ (q : ℝ≥0∞) (_ : Fact (1 ≤ q)) (r t : ℝ),
          ∃ T : WeightedCoeff (Weight.sobolev r) q →L[ℂ] WeightedCoeff (Weight.sobolev (r+1)) q,
            (∀ c n, (T c).val n = (exp ((t:ℂ)*I*sourceAngularEtaRemainder hp hp1 n s
              (normalizedWeightedSource (SpectralWeight.sobolev 1 (by norm_num)) ψ))-1)*c.val n) ∧
            ‖T‖ ≤ |t| *K*Real.exp (|t| *K) := by
  obtain ⟨U,hU,hφ,K,hK,h⟩ := D.exists_local_normalizedSobolevEtaRemainder_decay φ
  refine ⟨U,hU,hφ,K,hK,?_⟩
  intro ψ hψ q hq r t
  exact WeightedCoeff.exists_sobolev_complex_phase_gain_multiplier r t _ K hK (h ψ hψ)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
