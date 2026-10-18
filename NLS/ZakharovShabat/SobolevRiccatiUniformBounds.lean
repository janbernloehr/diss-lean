import NLS.ZakharovShabat.SobolevRiccatiHierarchy

/-! # Uniform Riccati density bounds on Sobolev balls

Actual Fourier Riccati densities are bounded on every original Sobolev source ball, through the top L2 order. The source need not be smooth.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A finite operator-norm constant controls the actual cubic Fourier product. -/
def hierarchySobolevTripleConstant (t : ℕ) : ℝ :=
  ‖hierarchySobolevFromL1 t‖ * ‖hierarchySobolevToL1 (t+1) t le_rfl‖^3

theorem hierarchySobolevTripleConstant_nonneg (t : ℕ) :
    0 ≤ hierarchySobolevTripleConstant t := by unfold hierarchySobolevTripleConstant; positivity

theorem norm_hierarchySobolevTriple_le (t : ℕ) (a b c : ScalarSobolev (t+1)) :
    ‖hierarchySobolevTriple t a b c‖ ≤ hierarchySobolevTripleConstant t*‖a‖*‖b‖*‖c‖ := by
  let w := SpectralWeight.sobolev (t:ℝ) (Nat.cast_nonneg t)
  let L := hierarchySobolevToL1 (t+1) t le_rfl
  let F := hierarchySobolevFromL1 t
  change ‖F (w.convolution (L a) (w.convolution (L b) (L c)))‖ ≤ _
  calc
    _ ≤ ‖F‖*(‖L a‖*(‖L b‖*‖L c‖)) := by
      apply (F.le_opNorm _).trans
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg F)
      exact (w.norm_convolution_le _ _).trans
        (mul_le_mul_of_nonneg_left (w.norm_convolution_le _ _) (norm_nonneg _))
    _ ≤ ‖F‖*((‖L‖*‖a‖)*((‖L‖*‖b‖)*(‖L‖*‖c‖))) := by
      gcongr
      · exact L.le_opNorm a
      · exact L.le_opNorm b
      · exact L.le_opNorm c
    _ = _ := by dsimp only [F,L,hierarchySobolevTripleConstant]; ring

theorem norm_hierarchySobolevInclusion_le (s t : ℕ) (h : t ≤ s) (a : ScalarSobolev s) :
    ‖hierarchySobolevInclusion s t h a‖ ≤ ‖a‖ :=
  WeightedCoeff.norm_sobolevInclusion_le _ a

/-- Each actual Riccati density is uniformly bounded on every original Hs ball,
including the top H0 density. No smoothness of the source is assumed. -/
theorem exists_uniform_sobolevRiccatiDensity_bound (s n : ℕ) (hn : n ≤ s)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : SobolevSource s, ‖ab‖ ≤ R →
      ‖sobolevRiccatiDensity s ab n hn‖ ≤ C := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | _ | n
    · refine ⟨R,hR,?_⟩
      intro ab hab
      simpa only [sobolevRiccatiDensity_zero,norm_neg] using (norm_snd_le ab).trans hab
    · refine ⟨‖hierarchySobolevDerivative s (s-1) (by omega)‖*R,by positivity,?_⟩
      intro ab hab
      rw [sobolevRiccatiDensity_one,norm_neg]
      exact ((hierarchySobolevDerivative s (s-1) (by omega)).le_opNorm ab.2).trans
        (mul_le_mul_of_nonneg_left ((norm_snd_le ab).trans hab) (norm_nonneg _))
    · have hprev (k : Fin (n+2)) := ih k.val k.isLt (Nat.le_trans k.isLt.le hn)
      choose C hC hc using hprev
      let T := hierarchySobolevTripleConstant (s-(n+2))
      have hT : 0 ≤ T := hierarchySobolevTripleConstant_nonneg _
      let A (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) : ℝ :=
        T*R*C ⟨ij.val.1,by have he := Finset.mem_antidiagonal.mp ij.property; omega⟩*
          C ⟨ij.val.2,by have he := Finset.mem_antidiagonal.mp ij.property; omega⟩
      let K := ‖hierarchySobolevDerivative (s-(n+1)) (s-(n+2)) (by omega)‖*
        C ⟨n+1,by omega⟩ + ∑ ij ∈ (Finset.antidiagonal n).attach, A ij
      refine ⟨max K 0,le_max_right _ _,?_⟩
      intro ab hab
      apply le_trans _ (le_max_left K 0)
      rw [sobolevRiccatiDensity_succ_succ]
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact ((hierarchySobolevDerivative (s-(n+1)) (s-(n+2)) (by omega)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hc ⟨n+1,by omega⟩ ab hab) (norm_nonneg _))
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro ij _
        have he := Finset.mem_antidiagonal.mp ij.property
        apply (norm_hierarchySobolevTriple_le _ _ _ _).trans
        have ha := (norm_hierarchySobolevInclusion_le s (s-(n+2)+1) (by omega) ab.1).trans
          ((norm_fst_le ab).trans hab)
        have hb := (norm_hierarchySobolevInclusion_le (s-ij.val.1) (s-(n+2)+1) (by omega)
          (sobolevRiccatiDensity s ab ij.val.1 (by omega))).trans (hc ⟨ij.val.1,by omega⟩ ab hab)
        have hd := (norm_hierarchySobolevInclusion_le (s-ij.val.2) (s-(n+2)+1) (by omega)
          (sobolevRiccatiDensity s ab ij.val.2 (by omega))).trans (hc ⟨ij.val.2,by omega⟩ ab hab)
        dsimp only [A]
        exact mul_le_mul
          (mul_le_mul (mul_le_mul_of_nonneg_left ha hT) hb (norm_nonneg _) (mul_nonneg hT hR))
          hd (norm_nonneg _) (mul_nonneg (mul_nonneg hT hR) (hC _))

end NLS.ZakharovShabat
