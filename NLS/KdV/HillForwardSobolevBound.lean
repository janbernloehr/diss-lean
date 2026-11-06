import NLS.KdV.HillHamiltonianConvolutionBounds

/-! # The actual forward integer spectral action estimate and positive-index action series. -/

noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV
theorem hillNativeBaseAction_error_le_lower_norm (m : ℕ) (hm : 1 ≤ m)
    (p : RealHillWeightedPotential (hillIntegerWeight m)) (hmean : p.val.val 0 = 0) :
    let b := hillRealNativeIntegerLower m (m-1) (by omega) p
    (1+hillNativeActionMass m 0 p)^m*hillNativeActionMass m 0 p ≤
      (1+‖b.val‖)^(2*m)*‖b.val‖^2 := by
  dsimp only
  let b := hillRealNativeIntegerLower m (m-1) (by omega) p
  let q := hillPeriodOneUnitPotential (hillIntegerWeight m) p.val
  have hn : ‖q‖ ≤ ‖b.val‖ := by
    change ‖hillPeriodOneUnitPotential (hillIntegerWeight m) p.val‖ ≤ ‖b.val‖
    rw [← hillPeriodOneUnitPotential_lower m (m-1) (by omega) p.val]
    exact norm_hillPeriodOneUnitPotential_le (hillIntegerWeight (m-1)) b.val
  have hmass := tsum_hillNativeBaseActions_eq_half_norm m p hmean
  change hillNativeActionMass m 0 p = (1/2 : ℝ)*‖q‖^2 at hmass
  have hs := pow_le_pow_left₀ (norm_nonneg q) hn 2
  have hA : hillNativeActionMass m 0 p ≤ ‖b.val‖^2 := by nlinarith [sq_nonneg ‖q‖]
  have hp : 1+hillNativeActionMass m 0 p ≤ (1+‖b.val‖)^2 := by nlinarith [norm_nonneg b.val]
  have hpow := pow_le_pow_left₀ (show 0 ≤ 1+hillNativeActionMass m 0 p by
    linarith [hillNativeActionMass_nonneg m 0 p]) hp m
  have hb := mul_le_mul hpow hA (hillNativeActionMass_nonneg m 0 p) (by positivity : 0 ≤ ((1+‖b.val‖)^2)^m)
  simpa only [← pow_mul] using hb

theorem exists_hillNativeForwardSobolevBound (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RealHillWeightedPotential (hillIntegerWeight m), p.val.val 0 = 0 →
      let b := hillRealNativeIntegerLower m (m-1) (by omega) p
      hillNativeActionMass m m p ≤ C*(‖p.val‖^2+(1+‖b.val‖)^(2*m)*‖b.val‖^2) := by
  obtain ⟨CM,hCM,hMom⟩ := exists_hillNativeGlobalMomentComparisons_uniform m
  obtain ⟨CH,hCH,hHam⟩ := exists_hillNativeHamiltonianTop_mixed_bound m hm
  obtain ⟨S,hS,hConv⟩ := exists_hillNativeConvolution_lower_bound m hm
  let K : ℝ := (2*Real.pi)^(2*m)
  let C : ℝ := K*(CH+2*S)+CM
  have hK : 0 ≤ K := by positivity
  have hC : 0 ≤ C := add_nonneg (mul_nonneg hK (add_nonneg hCH (mul_nonneg (by norm_num) hS))) hCM
  refine ⟨C,hC,?_⟩
  intro p hmean
  dsimp only
  let H := hillSobolevHamiltonianFamily m (hillNativeIntegerToScalar m p.val)
  let b := hillRealNativeIntegerLower m (m-1) (by omega) p
  let E := (1+‖b.val‖)^(2*m)*‖b.val‖^2
  let V := if 2 ≤ m then ∑ ik ∈ Finset.antidiagonal (m-2), ‖H ik.1‖*‖H ik.2‖ else 0
  let T := ∑' n, hillGapMomentTerm (hillPeriodOneUnitPotential (hillIntegerWeight m) p.val)
    (hillPeriodOneUnitPotential_even (hillIntegerWeight m) p.val)
    (hillPeriodOneUnitPotential_real (hillIntegerWeight m) p.val p.property) m n
  have hc := (hMom m le_rfl p hmean).1
  change hillNativeActionMass m m p ≤ K*T+CM*(1+hillNativeActionMass m 0 p)^m*hillNativeActionMass m 0 p at hc
  have ht : T ≤ ‖H m‖+2*V := hillNativeMomentMass_le_Hamiltonian_convolution m m le_rfl p hmean
  have hh := hHam p.val
  change ‖hillSobolevHamiltonian m hm (hillNativeIntegerToScalar m p.val)‖ ≤ CH*(‖p.val‖^2+E) at hh
  rw [← hillSobolevHamiltonianFamily_self m hm] at hh
  have hv : V ≤ S*E := by simpa only [V,H,E,mul_assoc] using hConv p hmean
  have he : (1+hillNativeActionMass m 0 p)^m*hillNativeActionMass m 0 p ≤ E :=
    hillNativeBaseAction_error_le_lower_norm m hm p hmean
  have hkT := mul_le_mul_of_nonneg_left ht hK
  have hkH := mul_le_mul_of_nonneg_left hh hK
  have hkV := mul_le_mul_of_nonneg_left hv hK
  have hcm := mul_le_mul_of_nonneg_left he hCM
  have hE : 0 ≤ E := by positivity
  change hillNativeActionMass m m p ≤ C*(‖p.val‖^2+E)
  dsimp only [C]
  nlinarith [mul_nonneg (mul_nonneg hK hS) (sq_nonneg ‖p.val‖),mul_nonneg hCM (sq_nonneg ‖p.val‖)]


theorem hasSum_hillNativePositiveActions (M m : ℕ) (hm : m ≤ M)
    (p : RealHillWeightedPotential (hillIntegerWeight M)) :
    HasSum (fun n : ℕ => (2*Real.pi*(n+1 : ℕ))^(2*m+1)*
      hillRealGapIntegral (hillPeriodOneUnitPotential (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_even (hillIntegerWeight M) p.val)
        (hillPeriodOneUnitPotential_real (hillIntegerWeight M) p.val p.property) (n+1) 0)
      (hillNativeActionMass M m p) := by
  have hs := summable_hillNativeGapActions M m hm p
  have ht := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,hillGapActionTerm_zero_index,zero_add] at ht
  have h := ((summable_nat_add_iff 1).mpr hs).hasSum
  rw [ht] at h
  exact h

end NLS.KdV
