import NLS.ZakharovShabat.ResonantDiagonalRemainderMajorants
import NLS.ZakharovShabat.SourceResonantDiagonalQuadratic

/-!
# Original-source half-exponent bounds for the diagonal remainder

One source neighborhood and cutoff supply the actual contractions. One
ℓ(p/2) sequence then controls the nonlinear remainder simultaneously on
every distant full strip, with a common norm bound on that neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full-strip nonlinear remainder has one half-exponent majorant per source. -/
theorem exists_sourceDiagonalRemainderMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ D : Coeff (p/2), ‖D‖ ≤ 2*‖φ‖^4*diagonalRemainderRowConstant hp hp1 ∧
      ∀ n : ℤ, ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
        ‖weightedPotentialSquareInShift hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz‖ ≤ 1/2 →
        ‖weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z-
          sourceResonantDiagonalQuadratic φ n z‖ ≤ ‖D n‖ := by
  obtain ⟨D,hD,h⟩ := exists_weightedResonantDiagonalRemainderMajorant hp hp1
    SpectralWeight.one (sourceWeightedPeriodOne φ)
  have hf : ‖SpectralWeight.one.forgetWeight (sourceWeightedPeriodOne φ).fst‖ ≤ ‖φ‖ := by
    rw [← SpectralWeight.norm_toCoeff_eq_norm_forgetWeight]
    exact (SpectralWeight.one.norm_toCoeff_le _).trans
      ((WithLp.norm_fst_le _ (sourceWeightedPeriodOne φ)).trans_eq (norm_sourceWeightedPeriodOne φ))
  have hg : ‖SpectralWeight.one.toCoeff (sourceWeightedPeriodOne φ).snd‖ ≤ ‖φ‖ :=
    (SpectralWeight.one.norm_toCoeff_le _).trans
      ((WithLp.norm_snd_le _ (sourceWeightedPeriodOne φ)).trans_eq (norm_sourceWeightedPeriodOne φ))
  refine ⟨D,hD.trans ?_,?_⟩
  · have hC := diagonalRemainderRowConstant_nonneg hp hp1
    calc
      _ ≤ 2*‖φ‖^2*‖φ‖^2*diagonalRemainderRowConstant hp hp1 := by gcongr
      _ = _ := by ring
  · intro n z hz hh
    have hw := hh.trans_lt (by norm_num : (1/2:ℝ)<1)
    rw [weightedResonantAExtension_eq hp SpectralWeight.one (sourceWeightedPeriodOne φ) n z hz hw,
      sourceResonantA_sub_quadratic]
    apply h n z hz hw
    simpa only [sourceWeightedPeriodOne_forget] using hh

/-- A common original-source neighborhood controls every distant strip in ℓ(p/2). -/
theorem exists_uniform_sourceDiagonalRemainderMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ ψ ∈ V, ∃ D : Coeff (p/2), ‖D‖ ≤ K ∧
        ∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ resonantStrip n,
          ‖weightedResonantAExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n z-
            sourceResonantDiagonalQuadratic ψ n z‖ ≤ ‖D n‖ := by
  obtain ⟨N,hN,V,ho,hφ,h⟩ := exists_uniform_sourceDiagonalContraction hp φ
  let R := ‖φ‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC := diagonalRemainderRowConstant_nonneg hp hp1
  refine ⟨N,hN,V ∩ ball φ 1,ho.inter isOpen_ball,⟨hφ,mem_ball_self (by norm_num)⟩,
    2*R^4*diagonalRemainderRowConstant hp hp1,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨D,hD,hbound⟩ := exists_sourceDiagonalRemainderMajorant hp hp1 ψ
  have hψR : ‖ψ‖ ≤ R := by
    have hb := mem_ball.mp hψ.2
    rw [dist_eq_norm] at hb
    have ht := norm_le_norm_sub_add ψ φ
    dsimp [R]
    linarith
  refine ⟨D,hD.trans (by gcongr),?_⟩
  intro n hn z hz
  exact hbound n z hz (h ψ hψ.1 n hn z hz)

end NLS.ZakharovShabat
