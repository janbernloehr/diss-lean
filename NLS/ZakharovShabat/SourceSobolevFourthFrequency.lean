import NLS.ZakharovShabat.SourceSobolevFourthActionDependence
import NLS.ZakharovShabat.SourceSobolevActionReduction
import NLS.ZakharovShabat.SourceLemma5_2

/-! # Independent physical H₄ frequencies on the full H^(3/2) domain

Open actions use the physical derivative along the actual unit-speed action
reduction. Closed actions use the second physical amplitude derivative, with
action t²/2. Neither definition uses Abelian moments or an extended frequency.
The full finite-gap calibration is retained in the fractional source topology.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The independently defined full physical H₄ on its actual action-reduction curve. -/
def sobolevFourthActionReductionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) (t : ℝ) : ℂ :=
  sourceSobolevFourthHamiltonian (D.sobolevActionReduction (3/2) (by norm_num) a n t)

/-- The native derivative exists and is the actual H₄ Birkhoff differential
applied to the physical unit-speed radial vector. -/
theorem hasDerivAt_sobolevFourthActionReductionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) :
    HasDerivAt (D.sobolevFourthActionReductionHamiltonian a n)
      (fderiv ℝ D.sobolevFourthBirkhoffHamiltonian (D.originalWeightedRealMap fourthSobolevSpectralWeight a)
        ((-1/(2*RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight
          (D.originalWeightedRealMap fourthSobolevSpectralWeight a)) n)) •
            WeightedRealCoeff.pairModeCLM (sourceFrequencyWeight fourthSobolevSpectralWeight) n
              (D.originalWeightedRealMap fourthSobolevSpectralWeight a))) 0 := by
  let w := sourceFrequencyWeight fourthSobolevSpectralWeight
  let hw : ∀ k, 1 ≤ w k := fun k => fourthSobolevSpectralWeight.one_le (2*k)
  let z := D.originalWeightedRealMap fourthSobolevSpectralWeight a
  let γ := WeightedRealCoeff.actionReduction w hw z n
  have hγ := WeightedRealCoeff.hasDerivAt_actionReduction_zero w hw z n
  have hH : HasFDerivAt D.sobolevFourthBirkhoffHamiltonian
      (fderiv ℝ D.sobolevFourthBirkhoffHamiltonian z) (γ 0) := by
    have hzero : γ 0 = z := WeightedRealCoeff.actionReduction_zero w hw z n
    exact hzero.symm ▸ (D.analyticOnNhd_sobolevFourthBirkhoffHamiltonian z (mem_univ _)).differentiableAt.hasFDerivAt
  exact hH.comp_hasDerivAt 0 hγ

/-- The physical open-action frequency uses only the actual H₄ derivative. -/
def sobolevFourthOpenFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) : ℂ :=
  -deriv (D.sobolevFourthActionReductionHamiltonian a n) 0

/-- The closed-action amplitude used by the frequency has exactly the
physical action t²/2 throughout the full fractional source domain. -/
theorem sobolevFourthOpening_action_same_of_closed
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n = 0) (t : ℝ) :
    (sourceRealAction (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight
        (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t)).val
      (originalWeightedRealSource fourthSobolevSpectralWeight
        (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t)).property n).re = t^2/2 := by
  have he : originalWeightedRealSource fourthSobolevSpectralWeight
      (D.sobolevGapOpening (by rfl) (3/2) (by norm_num) a n t) =
      D.hilbertGapOpening (originalWeightedRealSource fourthSobolevSpectralWeight a) n t :=
    D.originalWeightedRealSource_sobolevGapOpening_hilbert (3/2) (by norm_num) a n t
  rw [he]
  exact D.hilbertGapOpening_action_same_of_closed _ n hn t

/-- The closed frequency is the physical second amplitude derivative. -/
def sobolevFourthClosedFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) : ℂ :=
  deriv (deriv (D.sobolevFourthOpeningHamiltonian a n)) 0

/-- The full physical H₄ frequency at every original fractional source and index. -/
def sobolevFourthFrequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) (n : ℤ) : ℂ :=
  if canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n = 0 then D.sobolevFourthClosedFrequency a n
    else D.sobolevFourthOpenFrequency a n

private theorem fourth_hamiltonian_congr
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (h : φ = ψ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 4 =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) ψ hg 4 := by
  subst ψ
  rfl

/-- At finite gaps the entire reduction-line Hamiltonian is the original
physical Riccati function, with its actual action parameter unchanged. -/
theorem sobolevFourthActionReductionHamiltonian_eq_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.sobolevFourthActionReductionHamiltonian a n =
      D.physicalActionReductionHamiltonian (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n 4 := by
  funext t
  have he : originalWeightedRealSource fourthSobolevSpectralWeight
      (D.sobolevActionReduction (3/2) (by norm_num) a n t) =
      D.hilbertActionReduction (originalWeightedRealSource fourthSobolevSpectralWeight a) n t :=
    D.originalWeightedRealSource_sobolevActionReduction (3/2) (by norm_num) a n t
  have hfinite := D.sobolevActionReduction_mem_finiteGap (3/2) (by norm_num) a hf n t
  exact (sourceSobolevFourthHamiltonian_eq_finiteGap _ hfinite).trans
    (fourth_hamiltonian_congr _ _ hfinite (D.hilbertActionReduction_mem_finiteGap _ hf n t) he)

/-- Independent open frequencies agree with their already calibrated physical finite-gap values. -/
theorem sobolevFourthOpenFrequency_eq_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n ≠ 0) :
    D.sobolevFourthOpenFrequency a n = D.finiteGapFourthOpenFrequency
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n hn := by
  unfold sobolevFourthOpenFrequency finiteGapFourthOpenFrequency
  rw [D.sobolevFourthActionReductionHamiltonian_eq_finiteGap a hf n]

/-- The full original fractional frequency keeps the independently defined
finite-gap value at every selected action, including closed actions. -/
theorem sobolevFourthFrequency_eq_finiteGap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    D.sobolevFourthFrequency a n = D.finiteGapFourthFrequency
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n := by
  unfold sobolevFourthFrequency finiteGapFourthFrequency
  split_ifs with hn
  · exact D.second_deriv_sobolevFourthOpeningHamiltonian_finiteGap a hf n hn
  · exact D.sobolevFourthOpenFrequency_eq_finiteGap a hf n hn

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
