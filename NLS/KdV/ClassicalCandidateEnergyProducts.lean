import NLS.KdV.ClassicalCandidateRootProducts
import NLS.KdV.ClassicalCriticalBasisProduct
import NLS.ZakharovShabat.OmittedPairedEnergyProduct

/-! # Literal positive energy products for the selected normalized roots

All positive roots are included first, with the omitted mode retained as
a critical placeholder. Deleting that one factor gives an entire candidate
with the source's literal prefactor. Equality with Psi_n is still separate.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

def classicalHillCandidateEnergyPartialProduct (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) (M : ℕ) : ℂ :=
  -∏ j ∈ Finset.range M, (classicalHillCandidateEnergy N (⟨j+1,by omega⟩ : ℕ+) t-lambda)/
    ((Real.pi : ℂ)*((j : ℂ)+1))^2

def classicalHillCandidateEnergyProduct (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ → ℂ :=
  pairedEnergyProduct (classicalHillSignedCandidate N t)

def classicalHillCandidateOmittedPartialProduct (N : ℕ) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (lambda : ℂ) (M : ℕ) : ℂ :=
  (2/((n : ℂ)*Real.pi))*∏ j ∈ (Finset.range M).erase ((n : ℕ)-1),
    (classicalHillCandidateEnergy N (⟨j+1,by omega⟩ : ℕ+) t-lambda)/
      ((Real.pi : ℂ)*((j : ℂ)+1))^2

def classicalHillCandidateOmittedProduct (N : ℕ) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ → ℂ :=
  omittedPairedEnergyProduct (classicalHillSignedCandidate N t) n

theorem classicalHillSignedCandidate_paired (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) (k : ℕ+) :
    classicalHillSignedCandidate N t (-(k : ℤ)) = -classicalHillSignedCandidate N t (k : ℤ) := by
  rw [classicalHillSignedCandidate_positive N t haux,classicalHillSignedCandidate_negative N t haux]

theorem classicalHillCandidateEnergyPartialProduct_eq (N : ℕ)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (lambda : ℂ) (M : ℕ) :
    classicalHillCandidateEnergyPartialProduct N t lambda M =
      pairedEnergyPartialProduct (classicalHillSignedCandidate N t) lambda M := by
  unfold classicalHillCandidateEnergyPartialProduct pairedEnergyPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have he : classicalHillSignedCandidate N t ((j : ℤ)+1) =
      classicalHillCandidateFrequency N (⟨j+1,by omega⟩ : ℕ+) t := by
    simpa only [Nat.cast_add,Nat.cast_one] using!
      classicalHillSignedCandidate_positive N t haux (⟨j+1,by omega⟩ : ℕ+)
  rw [he]
  rfl

theorem classicalHillCandidateOmittedPartialProduct_eq (N : ℕ) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (lambda : ℂ) (M : ℕ) :
    classicalHillCandidateOmittedPartialProduct N n t lambda M =
      omittedPairedEnergyPartialProduct (classicalHillSignedCandidate N t) n lambda M := by
  unfold classicalHillCandidateOmittedPartialProduct omittedPairedEnergyPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have he : classicalHillSignedCandidate N t ((j : ℤ)+1) =
      classicalHillCandidateFrequency N (⟨j+1,by omega⟩ : ℕ+) t := by
    simpa only [Nat.cast_add,Nat.cast_one] using!
      classicalHillSignedCandidate_positive N t haux (⟨j+1,by omega⟩ : ℕ+)
  rw [he]
  rfl

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem candidate_energy_product
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) :
    AnalyticOnNhd ℂ (classicalHillCandidateEnergyProduct N t) univ ∧
    TendstoLocallyUniformlyOn (fun M z => classicalHillCandidateEnergyPartialProduct N t z M)
      (classicalHillCandidateEnergyProduct N t) atTop univ ∧
    (∀ lambda : ℂ, classicalHillCandidateEnergyProduct N t lambda = 0 ↔
      ∃ k : ℕ+, classicalHillCandidateEnergy N k t = lambda) ∧
    ∀ lambda : ℂ, classicalHillCandidateEnergyProduct N t lambda = 0 →
      deriv (classicalHillCandidateEnergyProduct N t) lambda ≠ 0 := by
  have hlp := D.signedCandidate_displacement_memlp t ht.2
  have hzero := classicalHillSignedCandidate_zero N t
  have hneg := classicalHillSignedCandidate_paired N t haux
  have hinj := D.signedCandidate_injective t ht
  have he (k : ℕ+) : (classicalHillSignedCandidate N t (k : ℤ))^2 = classicalHillCandidateEnergy N k t := by
    rw [classicalHillSignedCandidate_positive N t haux]
    rfl
  refine ⟨analyticOnNhd_pairedEnergyProduct (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp hzero hneg,?_,?_,?_⟩
  · simpa only [classicalHillCandidateEnergyPartialProduct_eq N t haux] using!
      tendstoLocallyUniformlyOn_pairedEnergyProduct (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp hzero hneg
  · intro lambda
    simpa only [he] using! pairedEnergyProduct_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj lambda
  · exact pairedEnergyProduct_simple_zeros (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj

theorem candidate_omitted_product (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0) :
    AnalyticOnNhd ℂ (classicalHillCandidateOmittedProduct N n t) univ ∧
    TendstoLocallyUniformlyOn (fun M z => classicalHillCandidateOmittedPartialProduct N n t z M)
      (classicalHillCandidateOmittedProduct N n t) atTop univ ∧
    (∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n t lambda = 0 ↔
      ∃ k : ℕ+, k ≠ n ∧ classicalHillCandidateEnergy N k t = lambda) ∧
    ∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n t lambda = 0 →
      deriv (classicalHillCandidateOmittedProduct N n t) lambda ≠ 0 := by
  have hlp := D.signedCandidate_displacement_memlp t ht.2
  have hzero := classicalHillSignedCandidate_zero N t
  have hneg := classicalHillSignedCandidate_paired N t haux
  have hinj := D.signedCandidate_injective t ht
  have he (k : ℕ+) : (classicalHillSignedCandidate N t (k : ℤ))^2 = classicalHillCandidateEnergy N k t := by
    rw [classicalHillSignedCandidate_positive N t haux]
    rfl
  refine ⟨analyticOnNhd_omittedPairedEnergyProduct (by norm_num : (2 : ENNReal) ≠ ⊤) _ hlp hzero hneg n,?_,?_,?_⟩
  · simpa only [classicalHillCandidateOmittedPartialProduct_eq N n t haux] using!
      tendstoLocallyUniformlyOn_omittedPairedEnergyProduct (by norm_num : (2 : ENNReal) ≠ ⊤)
        (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj n
  · intro lambda
    simpa only [he] using! omittedPairedEnergyProduct_eq_zero_iff (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj n lambda
  · exact omittedPairedEnergyProduct_simple_zeros (by norm_num : (2 : ENNReal) ≠ ⊤)
      (by norm_num : 1 < (2 : ENNReal)) _ hlp hzero hneg hinj n

/-- At zero displacement the constructed product is the actual filled
critical basis, with the same exact prefactor. -/
theorem candidate_omitted_product_zero_displacement (n : ℕ+)
    (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) (lambda : ℂ) :
    classicalHillCandidateOmittedProduct N n (0,q) lambda = classicalHillUniformNumerator N n (lambda,q) := by
  have ht : ((0 : NLS.Coeff 2),q) ∈ classicalHillCandidateDomain V :=
    ⟨Metric.mem_ball_self (by positivity),hq⟩
  have hP := (D.candidate_omitted_product n (0,q) ht (fun _ _ => rfl)).2.1.tendsto_at (mem_univ lambda)
  have hB := (D.critical_basis_product n q hq).tendsto_at (mem_univ lambda)
  have he (M : ℕ) : classicalHillCandidateOmittedPartialProduct N n (0,q) lambda M =
      classicalHillCriticalBasisPartialProduct N n q lambda M := by
    simp only [classicalHillCandidateOmittedPartialProduct,classicalHillCriticalBasisPartialProduct,
      classicalHillCandidateEnergy,classicalHillCandidateFrequency,lp.coeFn_zero,Pi.zero_apply,
      add_zero,classicalHillCriticalFrequency,NLS.ComplexAnalysis.sq_sqrt]
  exact tendsto_nhds_unique hP (by simpa only [he] using! hB)

end ClassicalAllContourPeriodData
end NLS.KdV
