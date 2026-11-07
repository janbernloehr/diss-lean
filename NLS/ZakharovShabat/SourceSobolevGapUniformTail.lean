import NLS.ZakharovShabat.SourceSobolevSquaredGapBounds
import NLS.SequenceSpaces.SobolevRatioTail

/-! Positive Sobolev order gives uniform actual gap tails on a fixed
full complex normalized source neighborhood, without dividing by gaps. -/
noncomputable section
open Set
namespace NLS.ZakharovShabat

theorem exists_local_sobolev_gap_uniform_tail
    (t : ℝ) (ht : 0<t) (φ : CoeffPair 2) :
    let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht.le)
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ φ∈T ∧
      ∀ ε > (0:ℝ), ∃ K : ℕ, ∀ ψ∈T, ∀ k : ℤ, K≤k.natAbs →
        ‖sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (L ψ) k‖≤ε := by
  intro L
  obtain ⟨T,hT,hφT,R,hR,hgap⟩ := exists_local_sobolevSquaredGap_bounds t ht.le φ
  refine ⟨T,hT,hφT,?_⟩
  intro ε hε
  obtain ⟨K,hK⟩ := Weight.exists_sobolev_ratio_tail 0 t ht (div_pos hε (by linarith : 0<R+1))
  refine ⟨K,?_⟩
  intro ψ hψ k hk
  have hg := (hgap ψ hψ).choose_spec.2.2 k
  have hr : (Weight.sobolev t k)⁻¹≤ε/(R+1) := by
    simpa only [Weight.sobolev_zero_apply,one_div] using (hK k hk).le
  calc
    _ ≤ (R+1)*(Weight.sobolev t k)⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ ((Weight.sobolev t).positive k)).mpr (by simpa only [mul_comm] using hg)
    _ ≤ (R+1)*(ε/(R+1)) := mul_le_mul_of_nonneg_left hr (by linarith)
    _ = ε := by field_simp

end NLS.ZakharovShabat
