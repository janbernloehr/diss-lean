import NLS.KdV.HillBalancedGapFrequencies
import NLS.ZakharovShabat.BalancedSingleSpectralProducts

/-! Literal finite positive-energy products and their deleted-index
versions. Pairing the ACTUAL balanced signed frequency cutoffs gives
these exact factors, with no unidentified entire normalization. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyProductFactor (σ : ℕ+ → ℝ) (E : ℂ) (j : ℕ) : ℂ :=
  ((σ ⟨j+1,by omega⟩:ℂ)-E)/((Real.pi:ℂ)*((j:ℂ)+1))^2

def hillEnergyPartialProduct (σ : ℕ+ → ℝ) (E : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, hillEnergyProductFactor σ E j

def hillEnergyDeletedPartialProduct (σ : ℕ+ → ℝ) (n : ℕ+) (E : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ (Finset.range N).erase ((n:ℕ)-1), hillEnergyProductFactor σ E j

theorem hillEnergyProduct_denominator_ne_zero (j : ℕ) : ((Real.pi:ℂ)*((j:ℂ)+1))^2 ≠ 0 :=
  pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (Nat.cast_add_one_ne_zero j))

theorem analyticOnNhd_hillEnergyDeletedPartialProduct (σ : ℕ+ → ℝ) (n : ℕ+) (N : ℕ) :
    AnalyticOnNhd ℂ (fun E => hillEnergyDeletedPartialProduct σ n E N) univ := by
  intro E _
  unfold hillEnergyDeletedPartialProduct hillEnergyProductFactor
  exact Finset.analyticAt_fun_prod _ (fun j _ =>
    (analyticAt_const.sub analyticAt_id).div analyticAt_const (hillEnergyProduct_denominator_ne_zero j))

theorem hillEnergyProductFactor_deleted_index (σ : ℕ+ → ℝ) (n : ℕ+) (E : ℂ) :
    hillEnergyProductFactor σ E ((n:ℕ)-1) = ((σ n:ℂ)-E)/((Real.pi:ℂ)*(n:ℕ))^2 := by
  have hNat : (n:ℕ)-1+1 = (n:ℕ) := Nat.sub_add_cancel n.property
  have hindex : (⟨((n:ℕ)-1)+1,by omega⟩:ℕ+) = n := by
    apply Subtype.ext
    change (n:ℕ)-1+1 = (n:ℕ)
    exact hNat
  have hcast : (((n:ℕ)-1:ℕ):ℂ)+1 = ((n:ℕ):ℂ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using congrArg (fun j : ℕ => (j:ℂ)) hNat
  rw [hillEnergyProductFactor,hindex,hcast]

theorem hillEnergyPartialProduct_restore (σ : ℕ+ → ℝ) (n : ℕ+) (E : ℂ) (N : ℕ) (hN : (n:ℕ) ≤ N) :
    hillEnergyPartialProduct σ E N =
      (((σ n:ℂ)-E)/((Real.pi:ℂ)*(n:ℕ))^2)*hillEnergyDeletedPartialProduct σ n E N := by
  have hmem : (n:ℕ)-1 ∈ Finset.range N := by simp only [Finset.mem_range]; have h := n.pos; omega
  have h := Finset.mul_prod_erase (Finset.range N) (hillEnergyProductFactor σ E) hmem
  rw [hillEnergyProductFactor_deleted_index] at h
  exact h.symm

theorem singleSpectralPartialProduct_balanced_energy (σ : ℕ+ → ℝ) (c : ℝ) (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct (hillBalancedGapFrequency σ c) z N =
      -2*z*hillEnergyPartialProduct σ (z^2-(c:ℂ)) N := by
  rw [singleSpectralPartialProduct_eq_of_balanced _ (hillBalancedGapFrequency_zero σ c)
    (hillBalancedGapFrequency_neg σ c),hillEnergyPartialProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  unfold hillEnergyProductFactor
  apply congrArg (fun a : ℂ => a/((Real.pi:ℂ)*((j:ℂ)+1))^2)
  let m : ℕ+ := ⟨j+1,by omega⟩
  have hindex : (j:ℤ)+1 = ((m:ℕ):ℤ) := by
    change (j:ℤ)+1 = ((j+1:ℕ):ℤ)
    omega
  have hs := hillBalancedGapFrequency_pos_sq σ c m
  rw [← hindex] at hs
  linear_combination hs

def hillEnergyRestoringPolynomial (σ : ℕ+ → ℝ) (n : ℕ+) (c : ℝ) (z : ℂ) : ℂ :=
  -2*z*(((σ n:ℂ)-(z^2-(c:ℂ)))/((Real.pi:ℂ)*(n:ℕ))^2)

theorem singleSpectralPartialProduct_balanced_deleted (σ : ℕ+ → ℝ) (n : ℕ+) (c : ℝ)
    (N : ℕ) (hN : (n:ℕ) ≤ N) (z : ℂ) :
    singleSpectralPartialProduct (hillBalancedGapFrequency σ c) z N =
      hillEnergyRestoringPolynomial σ n c z*hillEnergyDeletedPartialProduct σ n (z^2-(c:ℂ)) N := by
  rw [singleSpectralPartialProduct_balanced_energy,hillEnergyPartialProduct_restore σ n _ N hN]
  dsimp only [hillEnergyRestoringPolynomial]
  ring

theorem hillEnergyRestoringPolynomial_ne_zero_off_finite
    (σ : ℕ+ → ℝ) (n : ℕ+) (c : ℝ) (z : ℂ)
    (hz : z ∉ ({0,hillBalancedGapFrequency σ c ((n:ℕ):ℤ),-hillBalancedGapFrequency σ c ((n:ℕ):ℤ)}:Set ℂ)) :
    hillEnergyRestoringPolynomial σ n c z ≠ 0 := by
  have hz0 : z ≠ 0 := by intro he; exact hz (by simp [he])
  have hzp : z ≠ hillBalancedGapFrequency σ c ((n:ℕ):ℤ) := by intro he; exact hz (by simp [he])
  have hzm : z ≠ -hillBalancedGapFrequency σ c ((n:ℕ):ℤ) := by intro he; exact hz (by simp [he])
  have hden : ((Real.pi:ℂ)*(n:ℕ))^2 ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))
  unfold hillEnergyRestoringPolynomial
  apply mul_ne_zero (mul_ne_zero (by norm_num) hz0)
  apply div_ne_zero _ hden
  intro he
  have hs := hillBalancedGapFrequency_pos_sq σ c n
  have heq : z^2 = (hillBalancedGapFrequency σ c ((n:ℕ):ℤ))^2 := by linear_combination -he-hs
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp heq).elim hzp hzm

end NLS.KdV
