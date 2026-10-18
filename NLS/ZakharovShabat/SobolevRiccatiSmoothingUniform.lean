import NLS.ZakharovShabat.SobolevRiccatiSmoothingRemainder
import NLS.ZakharovShabat.SobolevRiccatiUniformBounds

/-! # Uniform bounds for the nonlinear Riccati remainder

The additional-regularity remainder is uniformly bounded on every original complex Sobolev ball.
-/

noncomputable section
namespace NLS.ZakharovShabat

/-- The nonlinear remainder is uniformly bounded in its additional
Sobolev order on every original source ball. -/
theorem exists_uniform_sobolevRiccatiSmoothingRemainder_bound
    (s n : ℕ) (hn : n ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ‖sobolevRiccatiSmoothingRemainder s ab n hn‖ ≤ C := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · exact ⟨0,le_rfl,by intro ab _; simp [sobolevRiccatiSmoothingRemainder]⟩
    · exact ⟨0,le_rfl,by intro ab _; simp [sobolevRiccatiSmoothingRemainder]⟩
    · obtain ⟨D,hD,hDdata⟩ := ih (n+1) (by omega) (by omega)
      have hprev (k : Fin (n+2)) := exists_uniform_sobolevRiccatiDensity_bound s k.val
        (Nat.le_trans k.isLt.le hn) R hR
      choose C hC hc using hprev
      let T := hierarchySobolevTripleConstant (s-(n+2)+1)
      have hT : 0 ≤ T := hierarchySobolevTripleConstant_nonneg _
      let A (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) : ℝ :=
        T*R*C ⟨ij.val.1,by have he := Finset.mem_antidiagonal.mp ij.property; omega⟩*
          C ⟨ij.val.2,by have he := Finset.mem_antidiagonal.mp ij.property; omega⟩
      let K := ‖hierarchySobolevDerivative (s-(n+1)+1) (s-(n+2)+1) (by omega)‖*D+
        ∑ ij ∈ (Finset.antidiagonal n).attach, A ij
      refine ⟨max K 0,le_max_right _ _,?_⟩
      intro ab hab
      apply le_trans _ (le_max_left K 0)
      rw [sobolevRiccatiSmoothingRemainder]
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact ((hierarchySobolevDerivative (s-(n+1)+1) (s-(n+2)+1) (by omega)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hDdata ab hab) (norm_nonneg _))
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro ij _
        have he := Finset.mem_antidiagonal.mp ij.property
        apply (norm_hierarchySobolevTriple_le _ _ _ _).trans
        have ha := (norm_hierarchySobolevInclusion_le s (s-(n+2)+1+1) (by omega) ab.1).trans
          ((norm_fst_le ab).trans hab)
        have hb := (norm_hierarchySobolevInclusion_le (s-ij.val.1) (s-(n+2)+1+1) (by omega)
          (sobolevRiccatiDensity s ab ij.val.1 (by omega))).trans (hc ⟨ij.val.1,by omega⟩ ab hab)
        have hd := (norm_hierarchySobolevInclusion_le (s-ij.val.2) (s-(n+2)+1+1) (by omega)
          (sobolevRiccatiDensity s ab ij.val.2 (by omega))).trans (hc ⟨ij.val.2,by omega⟩ ab hab)
        dsimp only [A]
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left ha hT) hb (norm_nonneg _) (mul_nonneg hT hR))
          hd (norm_nonneg _) (mul_nonneg (mul_nonneg hT hR) (hC _))

end NLS.ZakharovShabat
