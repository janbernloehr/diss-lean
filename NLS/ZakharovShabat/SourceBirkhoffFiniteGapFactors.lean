import NLS.ZakharovShabat.SourceGapWeightedEtaLemma16_1
import NLS.ZakharovShabat.SourceNormalizedActionRootSequenceSpace
import NLS.SequenceSpaces.ExponentialSummability

/-! # Summable normalization and phase errors at finite-gap sources

At a real finite-gap source, the beta series has only finitely many
nonzero summands in its gap index. Each summand is controlled by a shifted
reciprocal lattice. The actual beta correction is therefore ℓp, and both
the exponential phase and its product with the normalized-action root
are summably close to one.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual normalized-action root differs from one by an ℓp sequence
at every real source, with no finite-gap hypothesis. -/
theorem memlp_sourceNormalizedActionRoot_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Memℓp (fun n => sourceNormalizedActionRoot hp hp1 n φ-1) p := by
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨V,_,hφV,M,F,hF,_,_,_⟩ :=
    exists_local_sourceNormalizedActionRootDeviation_continuousMap (q := p) hp hp1 hp1 hp hhalf φ hφ
  have he : (fun n => sourceNormalizedActionRoot hp hp1 n φ-1) = F φ := funext (fun n => (hF φ hφV n).symm)
  rw [he]
  exact lp.memℓp _

namespace SourceAngularEtaLocalCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Finite-gap beta corrections form an actual ℓp sequence, including the finite head. -/
theorem memlp_betaCorrection_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ B)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) :
    Memℓp (fun n => sourceAngularBetaCorrection hp hp1 n s φ.val) p := by
  classical
  obtain ⟨U,_,hφU,_,C,_,hbound⟩ := D.beta_bound φ.val hφ
  have hterm (m : ℤ) : Memℓp (fun n => sourceAngularBetaSeriesTerm hp hp1 n s φ.val m) p := by
    apply ((lp.memℓp (Coeff.shift m (Coeff.puncturedLattice p hp1))).norm.const_mul
      (C*(‖sourcePeriodicGapDisplacement hp hp1 φ.val m‖+
        ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m-sourceStandardRootMidpoint hp hp1 φ.val m‖))).mono
    intro n
    rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hnm : n = m
    · subst n
      simp [sourceAngularBetaSeriesTerm]
    · simpa only [sourceAngularBetaSeriesTerm,if_neg (Ne.symm hnm),if_neg hnm,div_eq_mul_inv] using
        hbound φ.val hφU n m (Ne.symm hnm)
  let S := hfinite.toFinset
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
  have he (n : ℤ) : sourceAngularBetaCorrection hp hp1 n s φ.val =
      ∑ m ∈ S, sourceAngularBetaSeriesTerm hp hp1 n s φ.val m :=
    tsum_eq_sum (hzero n)
  simp_rw [he]
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact zero_memℓp
  | @insert m S hm ih =>
    simp only [Finset.sum_insert hm]
    exact (hterm m).add ih

/-- The complete action-root and beta-phase multiplier is summably close to one. -/
theorem memlp_birkhoffFactor_sub_one_finiteGap
    (D : SourceAngularEtaLocalCommonDomainData hp hp1 W₀ B s)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ B)
    (hfinite : φ ∈ sourceFiniteGapLocus hp hp1) (sign : ℂ) :
    Memℓp (fun n => sourceNormalizedActionRoot hp hp1 n φ.val*
      exp (sign*I*sourceAngularBetaCorrection hp hp1 n s φ.val)-1) p := by
  have hroot := memlp_sourceNormalizedActionRoot_sub_one hp hp1 φ.val φ.property
  have hphase := memlp_exp_sub_one ((D.memlp_betaCorrection_finiteGap φ hφ hfinite).const_mul (sign*I))
  obtain ⟨C,_,hC⟩ := exists_norm_bound_of_memlp_sub_one hphase
  have hprod := memlp_smul_of_bounded_scalar _ _ hroot C hC
  convert hprod.add hphase using 1
  funext n
  simp only [Pi.add_apply,smul_eq_mul]
  ring

end SourceAngularEtaLocalCommonDomainData
end NLS.ZakharovShabat
