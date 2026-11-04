import NLS.KdV.HillWeightedDirichletDiagonal

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.KdV



/-- A periodic root is close to any energy whose actual Schur defect is
small. The weighted estimate follows from the diagonal Lipschitz bound. -/
theorem hillReduced_root_distance_le_defect (w : SpectralWeight)
    (q : WeightedCoeff w.toWeight 2) (n : ℕ) (hn : 1 ≤ n) (z E : ℂ)
    (hz : z ∈ reducedHillStrip n) (hE : E ∈ reducedHillStrip n)
    (hc : 8*‖q‖ ≤ (n : ℝ)) (hroot : hillReducedDeterminant w n (q,z)=0) :
    w (2*(n : ℤ))*‖z-E‖ ≤ 2*(
      w (2*(n : ℤ))*‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc‖+
      w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+
      w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+16*‖q‖^2/(n : ℝ)) := by
  let W := w (2*(n : ℤ))
  let A := W*‖z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hc‖
  let P := W*‖q.val (2*(n : ℤ))‖
  let M := W*‖q.val (-(2*(n : ℤ)))‖
  let e := 8*‖q‖^2/(n : ℝ)
  have hW : 0 ≤ W := (w.positive _).le
  have hA : 0 ≤ A := mul_nonneg hW (norm_nonneg _)
  have hP : 0 ≤ P := mul_nonneg hW (norm_nonneg _)
  have hM : 0 ≤ M := mul_nonneg hW (norm_nonneg _)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hs : A^2 ≤ (P+e)*(M+e) := hillReduced_root_shift_bound w q n hn z hz hc hroot
  have hlinear : A ≤ P+M+2*e := by
    apply (sq_le_sq₀ hA (by positivity : 0 ≤ P+M+2*e)).mp
    nlinarith [sq_nonneg (P+e),sq_nonneg (M+e),mul_nonneg (by positivity : 0 ≤ P+e) (by positivity : 0 ≤ M+e)]
  have ht : ‖z-E‖ ≤ ‖hillDiagonal w q n hn z hz hc-hillDiagonal w q n hn E hE hc‖+
      (‖z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hc‖+
        ‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc‖) := by
    calc
      _ = ‖(hillDiagonal w q n hn z hz hc-hillDiagonal w q n hn E hE hc)+
          ((z-(freeHillValue n : ℂ)-hillDiagonal w q n hn z hz hc)-
            (E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc))‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_sub_le _ _))
  have hdiag := hillDiagonal_sub_le_quarter w q n hn z E hz hE hc
  have hm := mul_le_mul_of_nonneg_left (ht.trans (add_le_add hdiag le_rfl)) hW
  have hd : 0 ≤ W*‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc‖ := by positivity
  have hm' : W*‖z-E‖ ≤ (1/4 : ℝ)*(W*‖z-E‖)+(A+
      W*‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc‖) := by
    dsimp only [A]
    nlinarith only [hm]
  calc
    _ ≤ 2*(W*‖E-(freeHillValue n : ℂ)-hillDiagonal w q n hn E hE hc‖+P+M+2*e) := by
      nlinarith
    _ = _ := by dsimp only [P,M,e,W]; ring

/-- Every actual high periodic root is weighted-close to the actual complex
Dirichlet root; no complex ordering of the roots is needed. -/
theorem exists_hillDirichlet_periodic_distance_weighted_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ N : ℕ, 1 ≤ N ∧ 8*B ≤ (N : ℝ) ∧
      ∀ w : SpectralWeight, ∀ q : WeightedCoeff w.toWeight 2, ‖q‖ ≤ B →
      w.toCoeff q ∈ Coeff.paritySubspace 0 →
      ∀ n : ℕ, N ≤ n → ∀ E z : ℂ,
      E ∈ reducedHillStrip n → z ∈ reducedHillStrip n →
      hillL2DirichletCharacteristic (w.toCoeff q) E=0 →
      ‖E-(freeHillValue n : ℂ)‖ ≤ 24*(Real.exp (1/2))^2*B →
      hillReducedDeterminant w n (q,z)=0 →
      w (2*(n : ℤ))*‖z-E‖ ≤
        (4*B+10)*(w (2*(n : ℤ))*‖q.val (2*(n : ℤ))‖+
          w (2*(n : ℤ))*‖q.val (-(2*(n : ℤ)))‖+16*‖q‖^2/(n : ℝ)) := by
  obtain ⟨N,hN,hN8,hbound⟩ := exists_hillDirichlet_weighted_diagonal_bound B hB
  refine ⟨N,hN,hN8,?_⟩
  intro w q hq hp n hn E z hE hz hzero hnear hroot
  have hn1 : 1 ≤ n := hN.trans hn
  have hc : 8*‖q‖ ≤ (n : ℝ) := (mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 8)).trans
    (hN8.trans (by exact_mod_cast hn))
  have hdef := hbound w q hq hp n hn hn1 E hE hzero hnear hc
  have hdist := hillReduced_root_distance_le_defect w q n hn1 z E hz hE hc hroot
  nlinarith

end NLS.KdV
