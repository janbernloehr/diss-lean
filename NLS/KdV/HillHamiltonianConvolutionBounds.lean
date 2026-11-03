import NLS.KdV.HillHamiltonianNormBounds

/-! # Lower Sobolev control of the source nonlinear trace convolution. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem hill_norm_mass_product_le (x : ℝ) (hx : 0 ≤ x) (i k m : ℕ)
    (hik : i+k+1 ≤ m) :
    ((1+x)^(2*i)*x^2)*((1+x)^(2*k)*x^2) ≤ (1+x)^(2*m)*x^2 := by
  have hp : 1 ≤ 1+x := by linarith
  have hs : x^2 ≤ (1+x)^2 := by nlinarith
  calc
    _ = (1+x)^(2*i+2*k)*(x^2*x^2) := by rw [pow_add]; ring
    _ ≤ (1+x)^(2*i+2*k)*((1+x)^2*x^2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (sq_nonneg x)) (by positivity)
    _ = (1+x)^(2*i+2*k+2)*x^2 := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp (by omega : 2*i+2*k+2 ≤ 2*m)) (sq_nonneg x)

theorem exists_hillNativeConvolution_lower_bound (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0 = 0 →
      let H := hillSobolevHamiltonianFamily m (hillNativeIntegerToScalar m p.val)
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      (if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0) ≤
        S*(1+‖b.val‖)^(2*m)*‖b.val‖^2 := by
  let C : ℕ → ℝ := fun j => if hj : j ≤ m-1 then
    (exists_hillNativeHamiltonianFamily_norm_bound (m-1) j hj).choose else 0
  have hC (j : ℕ) : 0 ≤ C j := by
    dsimp only [C]
    split_ifs with hj
    · exact (exists_hillNativeHamiltonianFamily_norm_bound (m-1) j hj).choose_spec.1
    · exact le_rfl
  let S : ℝ := ∑ ik ∈ Finset.antidiagonal (m-2), C ik.1*C ik.2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun ik _ => mul_nonneg (hC _) (hC _))
  refine ⟨S,hS,?_⟩
  intro p hmean
  dsimp only
  let b := hillRealNativeIntegerLower m (m-1) (by omega) p
  let H := hillSobolevHamiltonianFamily m (hillNativeIntegerToScalar m p.val)
  have hlow (j : ℕ) (hj : j ≤ m-1) : ‖H j‖ ≤ C j*(1+‖b.val‖)^(2*j)*‖b.val‖^2 := by
    have ht := (exists_hillNativeHamiltonianFamily_norm_bound (m-1) j hj).choose_spec.2 b
      (hillRealNativeIntegerLower_mean_zero m (m-1) (by omega) p hmean)
    rw [hillNativeHamiltonianFamily_lower m (m-1) j (by omega) hj p] at ht
    simpa only [C,dif_pos hj] using ht
  split_ifs with hm2
  · change (∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖) ≤ S*(1+‖b.val‖)^(2*m)*‖b.val‖^2
    dsimp only [S]
    rw [Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ik hik
    have he := Finset.mem_antidiagonal.mp hik
    have hi : ik.1 ≤ m-1 := by omega
    have hk : ik.2 ≤ m-1 := by omega
    calc
      _ ≤ (C ik.1*(1+‖b.val‖)^(2*ik.1)*‖b.val‖^2)*
          (C ik.2*(1+‖b.val‖)^(2*ik.2)*‖b.val‖^2) :=
        mul_le_mul (hlow _ hi) (hlow _ hk) (norm_nonneg _) (by
          exact mul_nonneg (mul_nonneg (hC _) (by positivity)) (sq_nonneg _))
      _ = (C ik.1*C ik.2)*(((1+‖b.val‖)^(2*ik.1)*‖b.val‖^2)*
          ((1+‖b.val‖)^(2*ik.2)*‖b.val‖^2)) := by ring
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left
          (hill_norm_mass_product_le ‖b.val‖ (norm_nonneg _) ik.1 ik.2 m (by omega))
          (mul_nonneg (hC ik.1) (hC ik.2))
        simpa only [mul_assoc] using hb
  · exact mul_nonneg (mul_nonneg hS (by positivity)) (sq_nonneg _)


theorem norm_hillHierarchyTraceCoefficient_le (H : ℕ → ℂ) (m : ℕ) :
    ‖hillHierarchyTraceCoefficient H m‖ ≤ ‖H m‖+
      2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0) := by
  let V := if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), H ik.1*H ik.2 else 0
  let W := if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0
  have hV : ‖V‖ ≤ W := by
    dsimp only [V,W]
    split_ifs
    · simpa only [norm_mul] using norm_sum_le (Finset.antidiagonal (m-2)) (fun ik => H ik.1*H ik.2)
    · simp
  have h4 : (1 : ℝ) ≤ 4^m := one_le_pow₀ (by norm_num)
  have h4p : (0 : ℝ) < 4^m := by positivity
  have hfirst : ‖H m/4^m‖ ≤ ‖H m‖ := by
    simp only [norm_div,norm_pow,Complex.norm_ofNat]
    exact div_le_self (norm_nonneg _) h4
  have hsecond : ‖(2/(4 : ℂ)^m)*V‖ ≤ 2*W := by
    simp only [norm_mul,norm_div,norm_pow,Complex.norm_ofNat]
    have hfrac : (2 : ℝ)/4^m ≤ 2 := (div_le_iff₀ h4p).mpr (by linarith)
    exact (mul_le_mul_of_nonneg_right hfrac (norm_nonneg V)).trans
      (mul_le_mul_of_nonneg_left hV (by norm_num))
  change ‖H m/4^m-(2/(4 : ℂ)^m)*V‖ ≤ ‖H m‖+2*W
  exact (norm_sub_le _ _).trans (add_le_add hfirst hsecond)

theorem hillNativeMomentMass_le_Hamiltonian_convolution (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) (hmean : p.val.val 0 = 0) :
    let H := hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val)
    (∑' n, hillGapMomentTerm (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
      (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) m n) ≤
      ‖H m‖+2*(if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0) := by
  dsimp only
  have ht := tsum_hillHierarchyMomentTerm_hierarchy_sobolev_of_le M m hm p hmean
  have hn := norm_hillHierarchyTraceCoefficient_le
    (hillSobolevHamiltonianFamily M (hillNativeIntegerToScalar M p.val)) m
  unfold hillSobolevTraceValue at ht
  rw [← ht,Complex.norm_real,Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans hn



end NLS.KdV
