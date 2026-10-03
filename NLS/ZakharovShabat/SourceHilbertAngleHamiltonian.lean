import NLS.ZakharovShabat.SourceAngularThetaHamiltonian
import NLS.ZakharovShabat.SourceHilbertActionReduction

/-! # The Hilbert action-reduction curve follows the actual angle Hamiltonian

Canonical Poisson relations identify the actual angle Hamiltonian with
the radial vector pulled back by the Birkhoff Jacobian. The previously
constructed source curve therefore solves the original Hamiltonian
initial value problem throughout the interval before collapse.
-/
noncomputable section
open Set Filter Topology Complex NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The complex action agrees with the real quadratic coordinate action. -/
theorem hilbert_complexAction_eq_pairAction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) :
    sourceComplexAction (by simp) (by norm_num) k φ.val =
      (RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k : ℂ) := by
  rw [D.hilbert_pairAction_eq,sourceComplexAction_eq_sourceRealAction]
  apply Complex.ext
  · rfl
  · exact (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
      φ.val φ.property k).2.1

/-- The actual complex Jacobian sends the theta Hamiltonian to the
real radial vector, including all unselected closed gaps. -/
theorem hilbert_jacobian_thetaHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u φ.val) =
    ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
      (RealCoeff.actionReductionVector (D.hilbertRealHomeomorph φ) k) := by
  let v := sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u φ.val
  have hrow (n : ℤ) := D.jacobian_coordinates φ.val (D.real_subset φ.property) v n
  have hd (n : ℤ) := D.fderiv_coordinates n φ.val (D.real_subset φ.property)
  have hv (n : ℤ) := D.map_coordinates_thetaHamiltonian E (le_refl 2) k n φ hk
  have hinc := D.real_map_complex_inclusion φ
  have hval : sourceBirkhoffMap (by simp) (by norm_num) s φ.val =
      ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) (D.hilbertRealHomeomorph φ) := hinc.symm
  apply Prod.ext <;> ext n
  · rw [(hrow n).1,← (hd n).1]
    refine (hv n).1.trans ?_
    rw [D.hilbert_complexAction_eq_pairAction,hval]
    change -(((D.hilbertRealHomeomorph φ).1 k : ℂ) /
      (2*(RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k : ℂ)))*(if n = k then 1 else 0) =
      ((-(1/(2*RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k))) *
        (lp.single (E := fun _ : ℤ => ℝ) 2 k ((D.hilbertRealHomeomorph φ).1 k)) n : ℝ)
    by_cases hn : n = k
    · subst n
      simp only [ite_true,lp.single_apply,Pi.single_eq_same,mul_one]
      push_cast
      ring
    · simp [hn,lp.single_apply]
  · rw [(hrow n).2,← (hd n).2]
    refine (hv n).2.trans ?_
    rw [D.hilbert_complexAction_eq_pairAction,hval]
    change -(((D.hilbertRealHomeomorph φ).2 k : ℂ) /
      (2*(RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k : ℂ)))*(if n = k then 1 else 0) =
      ((-(1/(2*RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k))) *
        (lp.single (E := fun _ : ℤ => ℝ) 2 k ((D.hilbertRealHomeomorph φ).2 k)) n : ℝ)
    by_cases hn : n = k
    · subst n
      simp only [ite_true,lp.single_apply,Pi.single_eq_same,mul_one]
      push_cast
      ring
    · simp [hn,lp.single_apply]

/-- The pulled-back radial vector is the original angle Hamiltonian.
The identity is independent of the normalized family's choice. -/
theorem hilbertActionReductionVector_eq_thetaHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (hk : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) k ≠ 0) :
    (D.hilbertActionReductionVector φ k).val =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u φ.val := by
  apply (D.jacobian_bijective_all_exponents φ).1
  rw [D.hilbert_jacobian_thetaHamiltonian E k φ hk,
    ← D.real_jacobian_complex_inclusion φ (D.hilbertActionReductionVector φ k)]
  congr 1
  change (D.realJacobianEquivAll φ) ((D.realJacobianEquivAll φ).symm _) = _
  exact (D.realJacobianEquivAll φ).apply_symm_apply _

/-- Before collapse the selected gap stays open along the constructed curve. -/
theorem hilbertActionReduction_gap_ne_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    {t : ℝ} (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (D.hilbertActionReduction φ k t).val)
      (periodOnePotential_mem (D.hilbertActionReduction φ k t).val) k ≠ 0 := by
  intro hz
  have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num)
      (D.hilbertActionReduction φ k t).val k = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply] using hz
  have hzero := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (D.hilbertActionReduction φ k t).val (D.hilbertActionReduction φ k t).property k).2.2.mpr hg
  have h := D.hilbertActionReduction_action_same φ k ha t ht.le
  rw [hzero,Complex.zero_re] at h
  linarith

/-- The constructed curve solves the original angle Hamiltonian equation,
with the derivative taken in the actual complex coefficient source space. -/
theorem hasDerivAt_hilbertActionReduction_thetaHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (k : ℤ) (φ : realTypeSourceSubmodule 2)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    {t : ℝ} (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    HasDerivAt (fun t : ℝ => (D.hilbertActionReduction φ k t).val)
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) (le_refl 2) k u
        (D.hilbertActionReduction φ k t).val) t := by
  have hd := (realTypeSourceSubmodule 2).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (D.hasDerivAt_hilbertActionReduction φ k ha ht)
  have he := D.hilbertActionReductionVector_eq_thetaHamiltonian E k
    (D.hilbertActionReduction φ k t) (D.hilbertActionReduction_gap_ne_zero k φ ha ht)
  change HasDerivAt (fun t : ℝ => (D.hilbertActionReduction φ k t).val)
    (D.hilbertActionReductionVector (D.hilbertActionReduction φ k t) k).val t at hd
  rw [he] at hd
  exact hd

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
