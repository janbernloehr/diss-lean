import NLS.KdV.HillSignedCriticalFrequencies
import NLS.KdV.HillEnergyRootAnalytic

/-! # The absolutely convergent energy critical product equals minus the actual Hill discriminant derivative everywhere. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
def hillEnergyCriticalFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  ((hillGapCriticalPoint q hq hr n : ℂ)-z)/(freeHillValue n : ℂ)

theorem hillSignedCriticalFrequency_pairedFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (k : ℕ) :
    singleSpectralFactor (hillSignedCriticalFrequency q hq hr) z ((k+1 : ℕ) : ℤ)*
      singleSpectralFactor (hillSignedCriticalFrequency q hq hr) z (-((k+1 : ℕ) : ℤ)) =
      hillEnergyCriticalFactor q hq hr (k+1) (z^2) := by
  have hs : (Complex.sqrt (hillGapCriticalPoint q hq hr (k+1)))^2 = (hillGapCriticalPoint q hq hr (k+1) : ℂ) := by
    have h := Complex.cpow_nat_inv_pow (hillGapCriticalPoint q hq hr (k+1) : ℂ) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hd : (freeHillValue ((k+1 : ℕ) : ℤ) : ℂ) = ((Real.pi : ℂ)*(k+1 : ℕ))^2 := by
    simp only [freeHillValue,ofReal_mul,ofReal_pow,ofReal_intCast]
    push_cast
    ring
  simp only [singleSpectralFactor,singleSpectralDenominator,
    if_neg (by omega : ((k+1 : ℕ) : ℤ) ≠ 0),if_neg (by omega : -((k+1 : ℕ) : ℤ) ≠ 0),
    hillSignedCriticalFrequency_natSucc,hillSignedCriticalFrequency_negNatSucc,hillEnergyCriticalFactor]
  rw [hd]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : (k : ℂ)+1 ≠ 0 := Nat.cast_add_one_ne_zero k
  field_simp
  linear_combination hs

theorem singleSpectralPartialProduct_hillSignedCriticalFrequency
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) (N : ℕ) :
    singleSpectralPartialProduct (hillSignedCriticalFrequency q hq hr) z N =
      -2*z*∏ k ∈ Finset.range N, hillEnergyCriticalFactor q hq hr (k+1) (z^2) := by
  rw [singleSpectralPartialProduct,prod_symmetric_interval]
  have hp (k : ℕ) := hillSignedCriticalFrequency_pairedFactor q hq hr z k
  simp only [Nat.cast_add,Nat.cast_one] at hp
  have hzero : singleSpectralFactor (hillSignedCriticalFrequency q hq hr) z 0 = -z := by
    simp only [singleSpectralFactor,singleSpectralDenominator,hillSignedCriticalFrequency,if_true,zero_sub,div_one]
  simp only [hp,hzero]
  ring


theorem exists_hillEnergyCriticalFactor_bounded_majorant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖hillEnergyCriticalFactor q hq hr (k+1) z-1‖ ≤ u k := by
  let C := 4*‖q‖+R
  let u : ℕ → ℝ := fun k => C/(k+1 : ℕ)^2
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable u := by
    simpa only [u,div_eq_mul_inv,one_mul] using ((summable_nat_add_iff 1).mpr hs0).mul_left C
  refine ⟨hillRealLabelCutoff q,u,hs,?_⟩
  intro k hk z hz
  have hn2 : 2 ≤ k+1 := by have h := hillRealLabelCutoff_ge_two q; omega
  have hcut : 8*‖q‖ ≤ (k+1 : ℕ) := (hillRealLabelCutoff_bound q).trans (by exact_mod_cast (show hillRealLabelCutoff q ≤ k+1 by omega))
  have hloc := hillGapCriticalPoint_high_localization q hq hr (k+1) hn2 hcut
  have hnle : ((k+1 : ℕ) : ℝ)^2 ≤ freeHillValue (k+1 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three])
      (sq_nonneg ((k+1 : ℕ) : ℝ))
    simpa only [one_mul,freeHillValue,Int.cast_natCast] using h
  have hc : 0 < freeHillValue (k+1 : ℕ) := lt_of_lt_of_le (by positivity) hnle
  have he : hillEnergyCriticalFactor q hq hr (k+1) z-1 =
      (((hillGapCriticalPoint q hq hr (k+1)-freeHillValue (k+1 : ℕ) : ℝ) : ℂ)-z)/(freeHillValue (k+1 : ℕ) : ℂ) := by
    unfold hillEnergyCriticalFactor
    have hne : (freeHillValue (k+1 : ℕ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hc)
    rw [div_sub_one hne]
    push_cast
    ring
  rw [he,norm_div,norm_real,Real.norm_eq_abs,abs_of_pos hc]
  have hnum : ‖((hillGapCriticalPoint q hq hr (k+1)-freeHillValue (k+1 : ℕ) : ℝ) : ℂ)-z‖ ≤ C := by
    apply (norm_sub_le _ _).trans
    rw [norm_real,Real.norm_eq_abs]
    exact add_le_add hloc hz
  exact (div_le_div_of_nonneg_right hnum hc.le).trans
    (div_le_div_of_nonneg_left (by dsimp only [C]; positivity) (by positivity) hnle)

def hillEnergyCriticalProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) : ℂ :=
  ∏' k : ℕ, hillEnergyCriticalFactor q hq hr (k+1) z

theorem summable_norm_hillEnergyCriticalFactor_sub_one
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Summable (fun k : ℕ => ‖hillEnergyCriticalFactor q hq hr (k+1) z-1‖) := by
  obtain ⟨N,u,hu,hbound⟩ := exists_hillEnergyCriticalFactor_bounded_majorant q hq hr ‖z‖ (norm_nonneg z)
  apply hu.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [norm_norm] using hbound k hk z le_rfl

theorem multipliable_hillEnergyCriticalFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    Multipliable (fun k : ℕ => hillEnergyCriticalFactor q hq hr (k+1) z) := by
  have h := multipliable_one_add_of_summable (summable_norm_hillEnergyCriticalFactor_sub_one q hq hr z)
  convert! h using 1
  funext k
  ring


theorem hasProdUniformlyOn_hillEnergyCriticalFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (K : Set ℂ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun k z => hillEnergyCriticalFactor q hq hr (k+1) z)
      (hillEnergyCriticalProduct q hq hr) K := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ := exists_hillEnergyCriticalFactor_bounded_majorant q hq hr R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K, ‖hillEnergyCriticalFactor q hq hr (k+1) z-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun z hz => hmajor k hk z (hbound z hz)
  have hc (k : ℕ) : ContinuousOn (fun z => hillEnergyCriticalFactor q hq hr (k+1) z-1) K := by
    unfold hillEnergyCriticalFactor
    fun_prop
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (z : ℂ) : 1+(hillEnergyCriticalFactor q hq hr (k+1) z-1) = hillEnergyCriticalFactor q hq hr (k+1) z := by ring
  simp only [he] at hp
  convert! hp using 1

theorem hasProdLocallyUniformlyOn_hillEnergyCriticalFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    HasProdLocallyUniformlyOn (fun k z => hillEnergyCriticalFactor q hq hr (k+1) z)
      (hillEnergyCriticalProduct q hq hr) univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  exact fun K _ hK => hasProdUniformlyOn_hillEnergyCriticalFactors q hq hr K hK

theorem analyticOnNhd_hillEnergyCriticalProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (hillEnergyCriticalProduct q hq hr) univ := by
  have hf (k : ℕ) : DifferentiableOn ℂ (hillEnergyCriticalFactor q hq hr (k+1)) univ := by
    unfold hillEnergyCriticalFactor
    fun_prop
  have hd : DifferentiableOn ℂ (hillEnergyCriticalProduct q hq hr) univ :=
    (hasProdLocallyUniformlyOn_hillEnergyCriticalFactors q hq hr).differentiableOn
      (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd (fun k _ => hf k))) isOpen_univ
  exact hd.analyticOnNhd isOpen_univ


theorem entireSingleSpectralProduct_hillEnergyCriticalProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ) :
    entireSingleSpectralProduct (hillSignedCriticalFrequency q hq hr) z =
      -2*z*hillEnergyCriticalProduct q hq hr (z^2) := by
  have hf := (tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by simp : (2 : ℝ≥0∞) ≠ ⊤)
    (hillSignedCriticalFrequency q hq hr) (memℓp_hillSignedCriticalFrequency_displacement q hq hr)).tendsto_at (mem_univ z)
  have he := ((multipliable_hillEnergyCriticalFactors q hq hr (z^2)).hasProd.tendsto_prod_nat).const_mul (-2*z)
  simp only [singleSpectralPartialProduct_hillSignedCriticalFrequency] at hf
  exact tendsto_nhds_unique hf he

theorem hillL2Discriminant_derivative_eq_energyCriticalProduct_of_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (energy : ℂ) (henergy : energy ≠ 0) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) energy = -hillEnergyCriticalProduct q hq hr energy := by
  have hs : (Complex.sqrt energy)^2 = energy := by
    have h := Complex.cpow_nat_inv_pow energy (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hz : Complex.sqrt energy ≠ 0 := by
    intro hz
    apply henergy
    rw [← hs,hz]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  have he := entireSingleSpectralProduct_hillEnergyCriticalProduct q hq hr (Complex.sqrt energy)
  rw [entireSingleSpectralProduct_hillSignedCriticalFrequency,
    deriv_canonicalDiscriminant_hillL2CoefficientPotential,hs] at he
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) hz)
  calc
    _ = -2*Complex.sqrt energy*hillEnergyCriticalProduct q hq hr energy := he
    _ = _ := by ring

theorem hillL2Discriminant_derivative_eq_energyCriticalProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (energy : ℂ) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) energy = -hillEnergyCriticalProduct q hq hr energy := by
  have hD : Continuous (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q))) :=
    continuousOn_univ.mp (analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv.continuousOn
  have hP : Continuous (fun z => -hillEnergyCriticalProduct q hq hr z) :=
    (continuousOn_univ.mp (analyticOnNhd_hillEnergyCriticalProduct q hq hr).continuousOn).neg
  have heq := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hD hP
    (fun z hz => hillL2Discriminant_derivative_eq_energyCriticalProduct_of_ne_zero q hq hr z hz)
  exact congrFun heq energy



end NLS.KdV
