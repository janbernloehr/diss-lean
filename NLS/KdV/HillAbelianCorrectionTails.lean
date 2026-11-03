import NLS.KdV.HillLocalAbelianTermDecay

/-! # Quantitative locally uniform tails of the independent Abelian series -/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat
namespace NLS.KdV

theorem norm_hillDirichletRegularAbelianTerm_tsum_tail_le
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n)
    (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ k : ℕ, N ≤ k →
      ‖hillDirichletRegularAbelianTerm q n hn (k+1) (by omega)‖ ≤ C/((k : ℝ)+1)^2)
    (M : ℕ) (hM : N ≤ M) :
    ‖∑' k : ℕ,hillDirichletRegularAbelianTerm q n hn ((k+M)+1) (by omega)‖ ≤
      2*C/((M : ℝ)+1) := by
  let R : ℕ → ℝ := fun k => 1/((k : ℝ)+(M+1 : ℕ))^2
  have hR : Summable R := NLS.ReciprocalSeries.summable_nat_reciprocal_sq_tail (M+1) (by omega)
  have hs := ((summable_nat_add_iff M).mpr (summable_hillDirichletRegularAbelianTerm q n hn)).norm
  have hp (k : ℕ) : ‖hillDirichletRegularAbelianTerm q n hn ((k+M)+1) (by omega)‖ ≤ C*R k := by
    convert hb (k+M) (by omega) using 1
    dsimp only [R]
    push_cast
    simp only [div_eq_mul_inv,one_mul]
    ring
  calc
    _ ≤ ∑' k : ℕ, ‖hillDirichletRegularAbelianTerm q n hn ((k+M)+1) (by omega)‖ :=
      norm_tsum_le_tsum_norm hs
    _ ≤ ∑' k : ℕ,C*R k := hs.tsum_le_tsum hp (hR.mul_left C)
    _ = C*∑' k : ℕ,R k := tsum_mul_left
    _ ≤ C*(2/((M+1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left
      (NLS.ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le (M+1) (by omega)) hC
    _ = _ := by push_cast;ring

theorem locally_small_hillDirichletRegularAbelianTerm_tails
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      ‖∑' k : ℕ,hillDirichletRegularAbelianTerm p n hn ((k+M)+1) (by omega)‖ ≤ ε := by
  obtain ⟨N,hN,C,hC,hb⟩ := exists_local_hillDirichletRegularAbelianTerm_sq_decay q n hn
  obtain ⟨M,hM⟩ := exists_nat_gt (2*C/ε)
  refine ⟨max N M,?_⟩
  filter_upwards [hb] with p hp
  apply (norm_hillDirichletRegularAbelianTerm_tsum_tail_le p n hn N C hC.le hp (max N M)
    (le_max_left _ _)).trans
  have hM' : 2*C < (M : ℝ)*ε := (div_lt_iff₀ hε).mp hM
  have hcast : (M : ℝ) ≤ (max N M : ℕ) := by exact_mod_cast le_max_right N M
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (max N M : ℕ)+1)).mpr
  nlinarith

end NLS.KdV
