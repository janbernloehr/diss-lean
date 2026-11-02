import NLS.ZakharovShabat.SourceDiagonalLaurentZeroBound
import NLS.ZakharovShabat.SourceWeightedGapBound

/-! # Weighted absolute convergence of the inverse-frequency action level

A compatible weighted Hilbert source realization controls the entire
noncentral Laurent-level-zero sequence in weighted l1. The weight may
include the extra physical frequency supplied by the reciprocal bound.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem exists_local_sourceWeightedZeroLaurent_bound
    (w : SpectralWeight) (q : ℤ → ℝ) (hq : ∀ n, 0 ≤ q n)
    (hqw : ∀ n : ℤ, q n/(1+|(n : ℝ)|) ≤ (w (2*n))^2)
    (L : E →L[ℂ] CoeffPair 2) (S : E →L[ℂ] WeightedCoeffPair w.toWeight 2)
    (hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b))
    (a : E) (ha : L a ∈ realDiagonalSourceLocus 2) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ U ⊆ L ⁻¹' sourceDiagonalLaurentDomain (by simp) (by norm_num) ∧
      ∃ C : ℝ, ∀ b ∈ U, ∃ J : Coeff 1,
        (∀ n : ℤ, J n = if n = 0 then 0 else (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b)) ∧
        ‖J‖ ≤ C := by
  let A := sourceDiagonalLaurentAtlas (p := 2) (by simp) (by norm_num)
  obtain ⟨V,hV,haV,G,hg⟩ := exists_local_sourceWeightedSquaredGap_bound w L S hSL a
  obtain ⟨W,hW,haW,hWA,K,hK,hb⟩ := A.exists_local_zeroLevel_inverse_frequency_bound ⟨L a,ha⟩
  let U := V ∩ L ⁻¹' W
  refine ⟨U,hV.inter (hW.preimage L.continuous),⟨haV,haW⟩,
    fun b hb => hWA hb.2,K*G,?_⟩
  intro b hbU
  obtain ⟨g,hgcoord,hgnorm⟩ := hg b hbU.1
  let f : ℤ → ℂ := fun n => if n = 0 then 0 else (q n : ℂ)*sourceDiagonalLaurentAction (by simp) (by norm_num) n 0 (L b)
  have hbound (n : ℤ) : ‖f n‖ ≤ K*‖g n‖ := by
    have hgabs : ‖g n‖ = (w (2*n))^2*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n‖^2 := by
      rw [hgcoord n]
      change ‖((w (2*n) : ℂ)^2*(sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n)^2)‖ = _
      rw [norm_mul,norm_pow,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.toWeight.positive _)]
    by_cases hn : n = 0
    · simp only [f,if_pos hn,norm_zero]
      positivity
    · simp only [f,if_neg hn,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hq n)]
      calc
        _ ≤ q n*(K/(1+|(n : ℝ)|)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n‖^2) :=
          mul_le_mul_of_nonneg_left (hb (L b) hbU.2 n hn) (hq n)
        _ = K*(q n/(1+|(n : ℝ)|))*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n‖^2 := by ring
        _ ≤ K*(w (2*n))^2*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (L b) n‖^2 := by
          gcongr
          exact hqw n
        _ = K*‖g n‖ := by rw [hgabs]; ring
  have hs := (g.property.norm.summable_of_one).mul_left K
  have hm : Memℓp f 1 := Coeff.memℓp_of_power_dominated _ _ hs (by simpa using hbound)
  let J := Coeff.ofFunctionOrZero 1 f
  refine ⟨J,fun n => Coeff.ofFunctionOrZero_apply_of_mem _ _ hm n,?_⟩
  have hn := Coeff.norm_ofFunctionOrZero_rpow_le (p := 1) (by simp) f (fun n => K*‖g n‖) hs
    (by simpa using hbound)
  have he : (∑' n : ℤ, ‖g n‖) = ‖g‖ := by
    simpa using (lp.norm_rpow_eq_tsum (p := 1) (by simp) g).symm
  have hJ : ‖J‖ ≤ K*‖g‖ := by
    simpa only [J,ENNReal.toReal_one,Real.rpow_one,tsum_mul_left,he] using hn
  exact hJ.trans (mul_le_mul_of_nonneg_left hgnorm hK.le)

end NLS.ZakharovShabat
