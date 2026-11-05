import NLS.ZakharovShabat.SourceBirkhoffWeightedLocalInverse
import NLS.ZakharovShabat.SourceAngularThetaHamiltonian

/-! # The actual angle Hamiltonian preserves every native spectral weight

The actual rectangular Jacobian sends the angle vector to a single-mode
radial vector. Its weighted inverse therefore supplies a unique weighted
lift, without a finite-gap assumption or an assumed regular angle vector.
-/
noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The radial vector retains the original raw coordinates. -/
def weightedThetaRadialTarget (w : SpectralWeight) (k : ℤ) (φ : CoeffPair 2) :
    WeightedCoeffPair (sourceFrequencyWeight w) 2 :=
  WithLp.toLp 2
    (WeightedCoeff.single _ k (-((sourceBirkhoffMap (by simp) (by norm_num) s φ).1 k /
      (2*sourceComplexAction (by simp) (by norm_num) k φ))),
     WeightedCoeff.single _ k (-((sourceBirkhoffMap (by simp) (by norm_num) s φ).2 k /
      (2*sourceComplexAction (by simp) (by norm_num) k φ))))

theorem jacobian_thetaHamiltonian_eq_weighted_radial
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (w : SpectralWeight) (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem _) k ≠ 0) :
    sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u φ.val) =
        weightedBirkhoffTargetInclusion w (weightedThetaRadialTarget (s := s) w k φ.val) := by
  let v := sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u φ.val
  have hrow (n : ℤ) := D.jacobian_coordinates φ.val (D.real_subset φ.property) v n
  have hd (n : ℤ) := D.fderiv_coordinates n φ.val (D.real_subset φ.property)
  have hv (n : ℤ) := D.map_coordinates_thetaHamiltonian E le_rfl k n φ hk
  apply Prod.ext <;> ext n
  · rw [(hrow n).1,← (hd n).1]
    refine (hv n).1.trans ?_
    rw [weightedBirkhoffTargetInclusion_fst]
    change -((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).1 k /
      (2*sourceComplexAction (by simp) (by norm_num) k φ.val))*(if n = k then 1 else 0) =
        (WeightedCoeff.single _ k _).val n
    rw [WeightedCoeff.single_val]
    by_cases hn : n = k <;> simp [hn]
  · rw [(hrow n).2,← (hd n).2]
    refine (hv n).2.trans ?_
    rw [weightedBirkhoffTargetInclusion_snd]
    change -((sourceBirkhoffMap (by simp) (by norm_num) s φ.val).2 k /
      (2*sourceComplexAction (by simp) (by norm_num) k φ.val))*(if n = k then 1 else 0) =
        (WeightedCoeff.single _ k _).val n
    rw [WeightedCoeff.single_val]
    by_cases hn : n = k <;> simp [hn]

/-- The actual angle vector has a unique lift in every spectral weight
at every weighted real source, including arbitrary infinite support. -/
theorem existsUnique_thetaHamiltonian_weighted
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := 2) w) (k : ℤ)
    (hk : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource w a).val) (periodOnePotential_mem _) k ≠ 0) :
    ∃! v : WeightedCoeffPair (sourceFrequencyWeight w) 2, originalWeightedSourceCLM w v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u
        (originalWeightedRealSource w a).val := by
  let φ := originalWeightedRealSource w a
  let z := weightedThetaRadialTarget (s := s) w k φ.val
  let v := (D.originalWeightedJacobianEquiv w a).symm z
  have hv : originalWeightedSourceCLM w v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl k u φ.val := by
    have h := congrArg (fun L => L z) (D.originalWeightedJacobianEquiv_symm_forget w a)
    change originalWeightedSourceCLM w v = (D.jacobianEquivAll φ).symm
      (weightedBirkhoffTargetInclusion w z) at h
    rw [h,← D.jacobian_thetaHamiltonian_eq_weighted_radial E w k φ hk]
    exact (D.jacobianEquivAll φ).symm_apply_apply _
  exact ⟨v,hv,fun v' hv' => originalWeightedSourceCLM_injective w (hv'.trans hv.symm)⟩

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
