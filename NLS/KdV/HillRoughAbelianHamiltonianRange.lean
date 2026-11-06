import NLS.KdV.HillRoughAbelianGardner
import NLS.Poisson.GardnerHamiltonianZeroMode
import NLS.SequenceSpaces.MeanZeroSobolevInclusion
import NLS.SequenceSpaces.DeletedDenseRange

/-! # The actual canonical Hamiltonian directions give dense Jacobian range -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Poisson

def hillMeanZeroAbelianDerivative
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (q : PeriodOneHminusOne) : DeletedCoeff 2 0 →L[ℂ] DeletedCoeff 2 0 :=
  (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))).comp
    ((fderiv ℂ Z q).comp (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))))

private theorem component_derivative_hamiltonian
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (q : PeriodOneHminusOne) (hZ : DifferentiableAt ℂ Z q)
    (σ τ : Bool) (n m : ℕ+) :
    (fderiv ℂ Z q (gardnerHamiltonianVector (hillRoughSignedAbelianComponent Z τ m) q)).val
      (if σ then (n : ℤ) else -(n : ℤ)) =
      hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
        (hillRoughSignedAbelianComponent Z τ m) q := by
  have hd := ((WeightedCoeff.evalCLM (Weight.sobolev (-1/2)) 2
    (if σ then (n : ℤ) else -(n : ℤ))).hasFDerivAt.comp q hZ.hasFDerivAt).fderiv
  change fderiv ℂ (hillRoughSignedAbelianComponent Z σ n) q = _ at hd
  rw [←fderiv_apply_gardnerHamiltonianVector,hd]
  rfl

/-- The image is the literal retained coordinate vector with the ACTUAL
half-order weight and mixed signed factor. -/
theorem hillMeanZeroAbelianDerivative_hamiltonian
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (q : PeriodOneHminusOne) (hZ : DifferentiableAt ℂ Z q)
    (hM : ∀ (σ τ : Bool) (n m : ℕ+),
      hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
        (hillRoughSignedAbelianComponent Z τ m) q = hillOriginalComplexGardnerMatrixEntry σ τ n m/2)
    (τ : Bool) (m : ℕ+) :
    hillMeanZeroAbelianDerivative Z q
      (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
        (gardnerHamiltonianVector (hillRoughSignedAbelianComponent Z τ m) q)) =
      Coeff.deleteCoordinateTo 0 (lp.single 2 (if τ then -(m : ℤ) else (m : ℤ))
        ((if τ then -I else I)*(Weight.sobolev (-1/2) (if τ then -(m : ℤ) else (m : ℤ)) : ℂ))) := by
  let v := gardnerHamiltonianVector (hillRoughSignedAbelianComponent Z τ m) q
  have hv : v.val 0 = 0 := gardnerHamiltonianDirection_zero_mode _
  apply Subtype.ext
  ext j
  by_cases hj : j = 0
  · subst j
    exact (hillMeanZeroAbelianDerivative Z q _).property.trans (Coeff.deleteCoordinateTo 0 _).property.symm
  · change (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1/2))
      (fderiv ℂ Z q (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1))
        (WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1)) v)))).val j = _
    rw [WeightedCoeff.meanZeroWeightedLift_projection _ v hv,
      WeightedCoeff.meanZeroWeightedProjection_apply_other _ _ j hj]
    change (Weight.sobolev (-1/2) j : ℂ)*(fderiv ℂ Z q v).val j =
      Coeff.deleteCoordinate 0 (lp.single 2 (if τ then -(m : ℤ) else (m : ℤ))
        ((if τ then -I else I)*(Weight.sobolev (-1/2) (if τ then -(m : ℤ) else (m : ℤ)) : ℂ))) j
    rw [Coeff.deleteCoordinate_apply_other 0 j hj]
    have hmpos : (0 : ℤ) < (m : ℤ) := by exact_mod_cast m.pos
    by_cases hjp : 0 < j
    · let n : ℕ+ := ⟨j.toNat,by omega⟩
      have hn : (n : ℤ) = j := by change (j.toNat : ℤ) = j; omega
      have hnm : (n : ℕ) = (m : ℕ) ↔ j = (m : ℤ) := by omega
      have hc := (component_derivative_hamiltonian Z q hZ true τ n m).trans (hM true τ n m)
      change (fderiv ℂ Z q v).val (n : ℤ) = _ at hc
      rw [hn] at hc
      rw [hc]
      cases τ <;> simp only [hillOriginalComplexGardnerMatrixEntry,↓reduceIte,hnm]
      · by_cases he : j = (m : ℤ)
        · rw [he]
          simp [lp.single_apply]
          ring
        · simp [he,lp.single_apply]
      · have he : j ≠ -(m : ℤ) := by omega
        simp [he,lp.single_apply]
    · let n : ℕ+ := ⟨(-j).toNat,by omega⟩
      have hn : -(n : ℤ) = j := by change -(((-j).toNat : ℕ) : ℤ) = j; omega
      have hnm : (n : ℕ) = (m : ℕ) ↔ j = -(m : ℤ) := by omega
      have hc := (component_derivative_hamiltonian Z q hZ false τ n m).trans (hM false τ n m)
      change (fderiv ℂ Z q v).val (-(n : ℤ)) = _ at hc
      rw [hn] at hc
      rw [hc]
      cases τ <;> simp only [hillOriginalComplexGardnerMatrixEntry,↓reduceIte,hnm]
      · have he : j ≠ (m : ℤ) := by omega
        simp [he,lp.single_apply]
      · by_cases he : j = -(m : ℤ)
        · rw [he]
          simp [lp.single_apply]
          ring
        · simp [he,lp.single_apply]

/-- The actual signed canonical matrix supplies every retained unit
vector and hence dense range of the literal mean-zero derivative. -/
theorem denseRange_hillMeanZeroAbelianDerivative_of_Gardner_matrix
    (Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2)
    (q : PeriodOneHminusOne) (hZ : DifferentiableAt ℂ Z q)
    (hM : ∀ (σ τ : Bool) (n m : ℕ+),
      hminusGardnerBracket (hillRoughSignedAbelianComponent Z σ n)
        (hillRoughSignedAbelianComponent Z τ m) q = hillOriginalComplexGardnerMatrixEntry σ τ n m/2) :
    DenseRange (hillMeanZeroAbelianDerivative Z q) := by
  apply Coeff.denseRange_of_deletedSingle_mem_range (by simp) 0
  intro j hj
  have he : ∃ (τ : Bool) (m : ℕ+), (if τ then -(m : ℤ) else (m : ℤ)) = j := by
    by_cases h : 0 < j
    · exact ⟨false,⟨j.toNat,by omega⟩,by change (j.toNat : ℤ) = j; omega⟩
    · exact ⟨true,⟨(-j).toNat,by omega⟩,by change -(((-j).toNat : ℕ) : ℤ) = j; omega⟩
  obtain ⟨τ,m,hm⟩ := he
  let c : ℂ := (if τ then -I else I)*(Weight.sobolev (-1/2) j : ℂ)
  have hc : c ≠ 0 := mul_ne_zero (by cases τ <;> simp) (Weight.complex_ne_zero _ _)
  have H := hillMeanZeroAbelianDerivative_hamiltonian Z q hZ hM τ m
  rw [hm,Coeff.deleteCoordinateTo_single_other 0 j hj] at H
  let x := WeightedCoeff.meanZeroWeightedProjectionCLM (Weight.sobolev (-1))
    (gardnerHamiltonianVector (hillRoughSignedAbelianComponent Z τ m) q)
  change hillMeanZeroAbelianDerivative Z q x = Coeff.deletedSingleCLM 0 j hj c at H
  refine ⟨c⁻¹ • x,?_⟩
  rw [map_smul]
  change c⁻¹ • hillMeanZeroAbelianDerivative Z q x = Coeff.deletedSingleCLM 0 j hj 1
  rw [H,←map_smul]
  simp only [smul_eq_mul,inv_mul_cancel₀ hc]

end NLS.KdV
