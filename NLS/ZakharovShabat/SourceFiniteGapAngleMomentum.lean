import NLS.ZakharovShabat.SourceSobolevAngleMomentum
import NLS.ZakharovShabat.SourceFiniteGapAngleSobolev
import NLS.ZakharovShabat.SourceFiniteGapOpenFrequency

/-! # Physical momentum along the actual finite-gap angle flow

The already constructed H¹ angle tangent identifies the full physical
momentum derivative with the original Poisson bracket. The calibration
with Appendix H's second Hamiltonian holds along the entire pre-collapse
action-reduction curve, including negative times.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual H¹ angle lift needs no new regularity assumption in this bracket identity. -/
theorem finiteGap_momentum_bracket
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n u (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      -(fderiv ℂ periodOneSobolevMomentum (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)
        (D.finiteGapThetaSobolevVector E φ hf n hn)) := by
  apply sourceSobolevThetaMomentumBracket_eq_neg_derivative
  rw [sobolevSourceInclusion_sourceFiniteGapSobolevPair]
  exact D.finiteGapThetaSobolevVector_inclusion E φ hf n hn

/-- The physical second Hamiltonian has derivative minus the actual angle–momentum
bracket throughout the full pre-collapse interval. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_two
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0)
    (t : ℝ) (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 2)
      (-sourceSobolevThetaMomentumBracket n u
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) (D.hilbertActionReduction φ n t)
          (D.hilbertActionReduction_mem_finiteGap φ hf n t))) t := by
  have hξ := D.hasDerivAt_hilbertActionReduction_sobolev E φ hf n hn t ht
  have hd := ((analyticAt_periodOneSobolevMomentum _).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hξ
  change HasDerivAt (fun r => periodOneSobolevMomentum
      (sourceFiniteGapSobolevPair (by simp) (by norm_num) (D.hilbertActionReduction φ n r)
        (D.hilbertActionReduction_mem_finiteGap φ hf n r)))
    (fderiv ℂ periodOneSobolevMomentum _ _) t at hd
  have he := D.finiteGap_momentum_bracket E (D.hilbertActionReduction φ n t)
    (D.hilbertActionReduction_mem_finiteGap φ hf n t) n
    (D.hilbertActionReduction_gap_ne_zero n φ (hilbert_action_pos_of_gap_ne_zero φ n hn) ht)
  rw [he, neg_neg]
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r =>
    (periodOneSobolevMomentum_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (D.hilbertActionReduction φ n r) (D.hilbertActionReduction_mem_finiteGap φ hf n r)).symm)

/-- At the base source, the bracket is the negative physical H2 action derivative. -/
theorem finiteGap_momentum_bracket_eq_physical_deriv
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sourceSobolevThetaMomentumBracket n u (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) =
      -deriv (D.physicalActionReductionHamiltonian φ hf n 2) 0 := by
  have hd := D.hasDerivAt_physicalActionReductionHamiltonian_two E φ hf n hn 0
    (hilbert_action_pos_of_gap_ne_zero φ n hn)
  simpa only [D.hilbertActionReduction_zero, neg_neg] using (congrArg Neg.neg hd.deriv).symm

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
