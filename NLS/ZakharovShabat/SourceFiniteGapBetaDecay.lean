import NLS.ZakharovShabat.SourceBirkhoffFiniteGapFactors

/-! # Inverse-index decay of the original beta correction at finite-gap sources -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- The actual beta correction at a real spectral finite-gap source has
the printed O(1/n) decay, for every finite source exponent above one.
The cutoff and constant are chosen before both positive and negative indices. -/
theorem betaCorrection_finiteGap_inverse_index_bound
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ B)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℤ, N < n.natAbs →
      ‖sourceAngularBetaCorrection hp hp1 n s φ.val‖ ≤ K / |(n : ℝ)| := by
  classical
  obtain ⟨U,_,hφU,_,C,hC,hbound⟩ := D.beta_bound φ.val hφ
  let S := hfinite.toFinset
  let R := S.sup Int.natAbs
  let A (m : ℤ) := C*(‖sourcePeriodicGapDisplacement hp hp1 φ.val m‖+
    ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m-
      sourceStandardRootMidpoint hp hp1 φ.val m‖)
  have hA (m : ℤ) : 0 ≤ A m := by dsimp [A]; positivity
  have hzero (n m : ℤ) (hm : m ∉ S) : sourceAngularBetaSeriesTerm hp hp1 n s φ.val m = 0 := by
    have hgap : sourcePeriodicGapDisplacement hp hp1 φ.val m = 0 := by
      by_contra hg
      apply hm
      apply hfinite.mem_toFinset.mpr
      change canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0
      rw [sourcePeriodicGapDisplacement_apply] at hg
      exact hg
    simp [sourceAngularBetaSeriesTerm,
      sourceAngularBeta_eq_zero_of_real_collapsed_gap hp hp1 n m s φ.val φ.property hgap]
  refine ⟨2*R,2*∑ m ∈ S, A m,by positivity,?_⟩
  intro n hn
  have hn0 : 0 < |(n : ℝ)| := by
    have hh : 0 < n.natAbs := by omega
    have hh' : (0 : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'
  have he : sourceAngularBetaCorrection hp hp1 n s φ.val =
      ∑ m ∈ S, sourceAngularBetaSeriesTerm hp hp1 n s φ.val m := tsum_eq_sum (hzero n)
  rw [he]
  calc
    _ ≤ ∑ m ∈ S, ‖sourceAngularBetaSeriesTerm hp hp1 n s φ.val m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, (2*A m/|(n : ℝ)|) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmR : m.natAbs ≤ R := Finset.le_sup hm
      have hmn : m ≠ n := by intro h; subst m; omega
      have hab : 2*|(m : ℝ)| < |(n : ℝ)| := by
        have hh : 2*m.natAbs < n.natAbs := by omega
        have hh' : (2 : ℝ)*(m.natAbs : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast hh
        simpa only [Nat.cast_natAbs,Int.cast_abs] using hh'
      have htri : |(n : ℝ)| ≤ |(n : ℝ)-(m : ℝ)|+|(m : ℝ)| := by
        simpa only [sub_add_cancel] using abs_add_le ((n : ℝ)-(m : ℝ)) (m : ℝ)
      have hden : 0 < |((n-m : ℤ) : ℝ)| := by push_cast; linarith
      have hhalf : |(n : ℝ)| ≤ 2*|((n-m : ℤ) : ℝ)| := by push_cast; linarith
      rw [sourceAngularBetaSeriesTerm,if_neg hmn]
      apply (hbound φ.val hφU n m hmn).trans
      change A m/|((n-m : ℤ) : ℝ)| ≤ 2*A m/|(n : ℝ)|
      apply (div_le_div_iff₀ hden hn0).mpr
      nlinarith [mul_le_mul_of_nonneg_left hhalf (hA m)]
    _ = (2*∑ m ∈ S, A m)/|(n : ℝ)| := by rw [← Finset.sum_div,← Finset.mul_sum]

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
