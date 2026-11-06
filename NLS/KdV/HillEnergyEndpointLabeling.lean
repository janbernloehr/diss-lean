import NLS.KdV.HillCentralEnergyLabeling
import NLS.ZakharovShabat.PeriodicEndpointCandidates
import NLS.ZakharovShabat.PeriodicEndpointProducts

/-! # The actual signed Hill energy roots form complete original periodic endpoint labels and give the canonical frequency product. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillSignedEnergyRoot_mem_high_disc
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (upper : Bool) (n : ℤ)
    (hn : 2 ≤ n.natAbs) (hcut : 8*‖q‖ ≤ (n.natAbs : ℝ)) :
    hillSignedEnergyRoot q hq hr upper n ∈ refinedResonantDisk n := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n.natAbs ≠ 0)
  have hk' : n.natAbs = k+1 := hk
  have hncase : n = ((k+1 : ℕ) : ℤ) ∨ n = -((k+1 : ℕ) : ℤ) := by omega
  have hpos : (0 : ℝ) < (k+1 : ℕ) := by positivity
  have hc : 0 < Real.pi*(k+1 : ℕ) := mul_pos Real.pi_pos hpos
  have hsmall : 4*‖q‖/(Real.pi*(k+1 : ℕ)) < Real.pi/4 := by
    apply (div_lt_iff₀ hc).mpr
    rw [hk'] at hcut
    have hp := mul_pos (show 0 < Real.pi^2-2 by nlinarith [Real.pi_gt_three]) hpos
    nlinarith
  have hbd : ‖hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(k+1 : ℕ)‖ < Real.pi/4 := by
    have h := hillRealLabels_sqrt_frequency_bound q hq hr (k+1) (by omega) (by simpa only [hk'] using hcut)
    cases upper with
    | false => exact h.1.trans_lt hsmall
    | true => exact h.2.trans_lt hsmall
  rcases hncase with rfl | rfl
  · simpa only [refinedResonantDisk,mem_ball,dist_eq_norm,hillSignedEnergyRoot_natSucc,Int.cast_natCast] using hbd
  · simp only [refinedResonantDisk, mem_ball, dist_eq_norm]
    rw [hillSignedEnergyRoot_negNatSucc]
    simp only [Int.cast_neg,Int.cast_natCast]
    rw [show -hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(-((k+1 : ℕ) : ℂ)) =
      -(hillEnergyFrequencyRoot q hq hr upper (k+1)-(Real.pi : ℂ)*(k+1 : ℕ)) by ring,norm_neg]
    exact hbd

theorem hillSignedEnergyRoot_collapsed_multiplicity_ge_two
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ) (hn : n ≠ 0)
    (hclosed : hillSignedEnergyRoot q hq hr false n = hillSignedEnergyRoot q hq hr true n) :
    2 ≤ periodicAlgebraicMultiplicity (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillSignedEnergyRoot q hq hr false n) := by
  classical
  let m := n.natAbs
  have hm : 1 ≤ m := by dsimp only [m]; omega
  let x := hillRealLabels q hq hr (2*m-1)
  have hx : hillSignedEnergyRoot q hq hr false n^2 = (x : ℂ) := by
    simpa only [if_neg hn,Bool.false_eq_true,if_false,m,x] using hillSignedEnergyRoot_sq q hq hr false n
  have hy : hillSignedEnergyRoot q hq hr true n^2 = (hillRealLabels q hq hr (2*m) : ℂ) := by
    simpa only [if_neg hn,if_true,m] using hillSignedEnergyRoot_sq q hq hr true n
  have he : hillRealLabels q hq hr (2*m) = x := by
    apply Complex.ofReal_injective
    rw [← hy,← hx,hclosed]
  let f : ℕ → ℕ := fun j => if hillRealLabels q hq hr j = x then 1 else 0
  have hmem : ({2*m-1,2*m} : Finset ℕ) ⊆ Finset.range (2*m+1) := by
    intro j hj
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hj : j = 2*m-1 ∨ j = 2*m) with rfl | rfl <;> simp only [Finset.mem_range] <;> omega
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := f) hmem (fun _ _ _ => Nat.zero_le _)
  have htwo : 2 ≤ ∑ j ∈ Finset.range (2*m+1), f j := by
    simpa only [Finset.sum_pair (by omega : 2*m-1 ≠ 2*m),f,x,if_pos rfl,if_pos he,if_true,Nat.reduceAdd] using hsum
  have hfull := hillEnergy_occurrence_sum_le_full q hq hr m x
  change (∑ j ∈ Finset.range (2*m+1), f j) ≤ ∑ᶠ j : ℕ, f j at hfull
  rw [periodicAlgebraicMultiplicity_hill_energy_census q hq hr _ x hx]
  change 2 ≤ (if hillSignedEnergyRoot q hq hr false n = 0 then 2 else 1) * (∑ᶠ j : ℕ, f j)
  split_ifs <;> omega

theorem hillSignedEnergyRoot_distantPair
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℤ)
    (hn : 2 ≤ n.natAbs) (hcut : 8*‖q‖ ≤ (n.natAbs : ℝ))
    (hcanon : canonicalPeriodicCutoff (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _) < n.natAbs) :
    PeriodicEndpointPair (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) n
      (hillSignedEnergyRoot q hq hr false n) (hillSignedEnergyRoot q hq hr true n) := by
  have hp := (canonicalPeriodicEndpoints_spec (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞))
    (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) (hillL2CoefficientPotential_even _)).1.distant n hcanon
  apply hp.of_candidates (hillSignedEnergyRoot_mem_high_disc q hq hr false n hn hcut)
    (hillSignedEnergyRoot_mem_high_disc q hq hr true n hn hcut)
  · exact (periodicSpectrum_hillSignedEnergyRoots q hq hr _).mpr ⟨n,Or.inl rfl⟩
  · exact (periodicSpectrum_hillSignedEnergyRoots q hq hr _).mpr ⟨n,Or.inr rfl⟩
  · exact hillSignedEnergyRoot_collapsed_multiplicity_ge_two q hq hr n (by intro he; subst n; simp at hn)

theorem exists_hillSignedEnergyRoot_endpointLabeling
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, PeriodicEndpointLabeling (by simp : (2 : ℝ≥0∞) ≠ ⊤)
      (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) N
      (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) := by
  let φ := hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)
  obtain ⟨N0,U,_,_,_,hφ,_,_,_,hd⟩ := exists_uniform_periodicCountingData (by simp : (2 : ℝ≥0∞) ≠ ⊤) φ
  let K := canonicalPeriodicCutoff (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : 1 < (2 : ℝ≥0∞)) φ
    (hillL2CoefficientPotential_even _)
  let N := max N0 (max K (hillRealLabelCutoff q))
  have h0 : N0 ≤ N := le_max_left _ _
  have hK : K ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hL : hillRealLabelCutoff q ≤ N := (le_max_right _ _).trans (le_max_right _ _)
  have hN : 2 ≤ N := (hillRealLabelCutoff_ge_two q).trans hL
  have hcut : 8*‖q‖ ≤ (N : ℝ) := (hillRealLabelCutoff_bound q).trans (by exact_mod_cast hL)
  have hcount := hd φ hφ N h0
  refine ⟨N,hcount,hillSignedEnergyRoot_centralLabeling q hq hr N hN hcut hcount,?_,
    memℓp_hillSignedEnergyRoot_displacement q hq hr false,
    memℓp_hillSignedEnergyRoot_displacement q hq hr true⟩
  intro n hn
  exact hillSignedEnergyRoot_distantPair q hq hr n (by omega)
    (hcut.trans (by exact_mod_cast (Nat.le_of_lt hn))) (lt_of_le_of_lt hK hn)

theorem entireSpectralPairProduct_hillSignedEnergyRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    entireSpectralPairProduct (hillSignedEnergyRoot q hq hr false) (hillSignedEnergyRoot q hq hr true) =
      canonicalPeriodicProduct (by simp : (2 : ℝ≥0∞) ≠ ⊤) (hillL2CoefficientPotential (SpectralWeight.one.toCoeff q)) := by
  obtain ⟨N,hN⟩ := exists_hillSignedEnergyRoot_endpointLabeling q hq hr
  exact hN.fullProduct_eq_canonical



end NLS.KdV
