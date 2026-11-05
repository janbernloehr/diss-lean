import NLS.KdV.HillEnergyLogarithmicProduct
import NLS.ComplexAnalysis.EndpointCriticalRatioBounds

/-! # The omitted energy critical product and chi_n extend analytically through the selected Hill gap. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat
open NLS.ComplexAnalysis
namespace NLS.KdV
def hillGapFilledDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) : Set ℂ :=
  {z | z.im ≠ 0 ∨ z.re ∈ Ioo (hillRealLabels q hq hr (2*n-2)) (hillRealLabels q hq hr (2*n+1))}

theorem isOpen_hillGapFilledDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    IsOpen (hillGapFilledDomain q hq hr n) :=
  (isOpen_ne_fun continuous_im continuous_const).union (isOpen_Ioo.preimage continuous_re)

theorem hillGapSegment_subset_filledDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) ⊆
      hillGapFilledDomain q hq hr n := by
  intro z hz
  have hx := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) z hz
  have hlo := hillRealLabels_band_strict q hq hr (n-1)
  have hi0 : 2*(n-1) = 2*n-2 := by omega
  have hi1 : 2*n-2+1 = 2*n-1 := by omega
  rw [hi0,hi1] at hlo
  exact Or.inr ⟨hlo.trans_le hx.1,hx.2.trans_lt (hillRealLabels_band_strict q hq hr n)⟩

theorem not_mem_other_gap_of_mem_hillGapFilledDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n)
    (z : ℂ) (hz : z ∈ hillGapFilledDomain q hq hr n) :
    z ∉ segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ) := by
  rcases hz with hi | hx
  · exact not_mem_real_segment_of_im_ne_zero _ _ z hi
  · intro hs
    have hseg := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m)) z hs
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · have hb := monotone_hillRealLabels q hq hr (by omega : 2*m ≤ 2*n-2)
      linarith [hx.1,hseg.2]
    · have hb := monotone_hillRealLabels q hq hr (by omega : 2*n+1 ≤ 2*m-1)
      linarith [hx.2,hseg.1]

theorem analyticAt_hillEnergyCriticalRootRatio
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ)
    (hz : z ∉ segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ)) :
    AnalyticAt ℂ (hillEnergyCriticalRootRatio q hq hr n) z :=
  (analyticAt_const.sub analyticAt_id).div (analyticOnNhd_endpointRoot _ _ z hz)
    (endpointRoot_ne_zero_of_not_mem_segment _ _ z hz)

def hillOmittedEnergyCriticalRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n k : ℕ) (z : ℂ) : ℂ :=
  if k+1 = n then 1 else hillEnergyCriticalRootRatio q hq hr (k+1) z

theorem analyticOnNhd_hillOmittedEnergyCriticalRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n k : ℕ) :
    AnalyticOnNhd ℂ (hillOmittedEnergyCriticalRootFactor q hq hr n k) (hillGapFilledDomain q hq hr n) := by
  intro z hz
  unfold hillOmittedEnergyCriticalRootFactor
  by_cases hk : k+1 = n
  · simp only [if_pos hk]
    exact analyticAt_const
  · simp only [if_neg hk]
    exact analyticAt_hillEnergyCriticalRootRatio q hq hr (k+1) z
        (not_mem_other_gap_of_mem_hillGapFilledDomain q hq hr n (k+1) (by omega) hk z hz)


theorem exists_hillOmittedEnergyCriticalRootFactor_bounded_majorant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖hillOmittedEnergyCriticalRootFactor q hq hr n k z-1‖ ≤ u k := by
  obtain ⟨Nc,v,hv,hvc⟩ := exists_hillEnergyCriticalFactor_bounded_majorant q hq hr R hR
  obtain ⟨Nr,u,hu,hur⟩ := exists_hillEnergyRootFactor_bounded_majorant q hq hr R hR
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hu.tendsto_atTop_zero.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)))
  let N := max Nc (max Nr M)
  have hs : Summable (fun k => 2*(v k+u k)) := (hv.add hu).mul_left 2
  refine ⟨N,fun k => 2*(v k+u k),hs,?_⟩
  intro k hk z hz
  have hvk := hvc k (by dsimp only [N] at hk; omega) z hz
  have huk := hur k (by dsimp only [N] at hk; omega) z hz
  have hsmall : u k ≤ 1/2 := (hM k (by dsimp only [N] at hk; omega)).le
  unfold hillOmittedEnergyCriticalRootFactor
  split_ifs
  · simp only [sub_self,norm_zero]
    have hv0 := (norm_nonneg _).trans hvk
    have hu0 := (norm_nonneg _).trans huk
    positivity
  · rw [hillEnergyCriticalRootRatio_eq_factor_div q hq hr (k+1) (by omega) z]
    exact norm_div_sub_one_le_of_half_error _ _ _ _ hvk huk hsmall

def hillOmittedEnergyCriticalRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  ∏' k : ℕ, hillOmittedEnergyCriticalRootFactor q hq hr n k z

theorem hasProdUniformlyOn_hillOmittedEnergyCriticalRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ)
    (K : Set ℂ) (hK : IsCompact K) (hdom : K ⊆ hillGapFilledDomain q hq hr n) :
    HasProdUniformlyOn (fun k z => hillOmittedEnergyCriticalRootFactor q hq hr n k z)
      (hillOmittedEnergyCriticalRootProduct q hq hr n) K := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ := exists_hillOmittedEnergyCriticalRootFactor_bounded_majorant q hq hr n R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K, ‖hillOmittedEnergyCriticalRootFactor q hq hr n k z-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun z hz => hmajor k hk z (hbound z hz)
  have hc (k : ℕ) : ContinuousOn (fun z => hillOmittedEnergyCriticalRootFactor q hq hr n k z-1) K :=
    (((analyticOnNhd_hillOmittedEnergyCriticalRootFactor q hq hr n k).continuousOn).mono hdom).sub continuousOn_const
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (z : ℂ) : 1+(hillOmittedEnergyCriticalRootFactor q hq hr n k z-1) = hillOmittedEnergyCriticalRootFactor q hq hr n k z := by ring
  simp only [he] at hp
  convert! hp using 1

theorem hasProdLocallyUniformlyOn_hillOmittedEnergyCriticalRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    HasProdLocallyUniformlyOn (fun k z => hillOmittedEnergyCriticalRootFactor q hq hr n k z)
      (hillOmittedEnergyCriticalRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_hillGapFilledDomain q hq hr n)
  exact fun K hKsub hK => hasProdUniformlyOn_hillOmittedEnergyCriticalRootFactors q hq hr n K hK hKsub

theorem analyticOnNhd_hillOmittedEnergyCriticalRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    AnalyticOnNhd ℂ (hillOmittedEnergyCriticalRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) := by
  have hf (k : ℕ) : DifferentiableOn ℂ (hillOmittedEnergyCriticalRootFactor q hq hr n k) (hillGapFilledDomain q hq hr n) :=
    (analyticOnNhd_hillOmittedEnergyCriticalRootFactor q hq hr n k).differentiableOn
  have hd : DifferentiableOn ℂ (hillOmittedEnergyCriticalRootProduct q hq hr n) (hillGapFilledDomain q hq hr n) :=
    (hasProdLocallyUniformlyOn_hillOmittedEnergyCriticalRootFactors q hq hr n).differentiableOn
      (Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd (fun k _ => hf k))) (isOpen_hillGapFilledDomain q hq hr n)
  exact hd.analyticOnNhd (isOpen_hillGapFilledDomain q hq hr n)


theorem hillGroundShift_mem_slitPlane_of_mem_filledDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ)
    (hz : z ∈ hillGapFilledDomain q hq hr n) :
    z-(hillRealLabels q hq hr 0 : ℂ) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hz with hi | hx
  · right
    simpa only [sub_im,ofReal_im,sub_zero] using hi
  · left
    have h0 := monotone_hillRealLabels q hq hr (Nat.zero_le (2*n-2))
    simp only [sub_re,ofReal_re]
    linarith [hx.1]

def hillEnergyChi
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (z : ℂ) : ℂ :=
  (Complex.sqrt (z-hillRealLabels q hq hr 0))⁻¹ * hillOmittedEnergyCriticalRootProduct q hq hr n z

theorem analyticOnNhd_hillEnergyChi
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    AnalyticOnNhd ℂ (hillEnergyChi q hq hr n) (hillGapFilledDomain q hq hr n) := by
  intro z hz
  have hs : AnalyticAt ℂ Complex.sqrt (z-hillRealLabels q hq hr 0) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds
      (hillGroundShift_mem_slitPlane_of_mem_filledDomain q hq hr n z hz))
  have hc := hs.comp (f := fun w : ℂ => w-hillRealLabels q hq hr 0) (analyticAt_id.sub analyticAt_const)
  have hne : Complex.sqrt (z-hillRealLabels q hq hr 0) ≠ 0 := by
    intro he
    have hsq : (Complex.sqrt (z-hillRealLabels q hq hr 0))^2 = z-hillRealLabels q hq hr 0 := by
      have h := Complex.cpow_nat_inv_pow (z-hillRealLabels q hq hr 0) (Nat.succ_ne_zero 1)
      norm_num at h
      simpa only [Complex.sqrt,one_div] using h
    rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsq
    have hslit := hillGroundShift_mem_slitPlane_of_mem_filledDomain q hq hr n z hz
    rw [← hsq] at hslit
    exact zero_notMem_slitPlane hslit
  exact (hc.inv hne).mul (analyticOnNhd_hillOmittedEnergyCriticalRootProduct q hq hr n z hz)

theorem tprod_hillEnergyCriticalRootRatio_extract
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillGapFilledDomain q hq hr n) :
    (∏' k : ℕ, hillEnergyCriticalRootRatio q hq hr (k+1) z) =
      hillEnergyCriticalRootRatio q hq hr n z * hillOmittedEnergyCriticalRootProduct q hq hr n z := by
  have hp := (hasProd_ite_eq (n-1) (hillEnergyCriticalRootRatio q hq hr n z)).mul
    ((hasProdLocallyUniformlyOn_hillOmittedEnergyCriticalRootFactors q hq hr n).hasProd hz)
  have he (k : ℕ) : (if k = n-1 then hillEnergyCriticalRootRatio q hq hr n z else 1)*
      hillOmittedEnergyCriticalRootFactor q hq hr n k z = hillEnergyCriticalRootRatio q hq hr (k+1) z := by
    by_cases hk : k = n-1
    · have hkn : k+1 = n := by omega
      simp only [if_pos hk,hillOmittedEnergyCriticalRootFactor,hkn,if_true,mul_one]
    · have hkn : k+1 ≠ n := by omega
      simp only [if_neg hk,hillOmittedEnergyCriticalRootFactor,if_neg hkn,one_mul]
  simp only [he] at hp
  exact hp.tprod_eq

theorem hillL2LogarithmicDifferential_selectedFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) (hzn : z ∈ hillGapFilledDomain q hq hr n) :
    deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
      hillEnergyCanonicalRootProduct q hq hr z =
      hillEnergyCriticalRootRatio q hq hr n z / (2*I) * hillEnergyChi q hq hr n z := by
  rw [hillL2LogarithmicDifferential_energyProduct q hq hr z hz,
    tprod_hillEnergyCriticalRootRatio_extract q hq hr n hn z hzn,hillEnergyChi]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring


end NLS.KdV
