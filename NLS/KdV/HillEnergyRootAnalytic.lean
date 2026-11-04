import NLS.KdV.HillCanonicalEnergyRootProduct
import NLS.KdV.HillL2RealCutDifferential
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-! # Local uniform convergence, analyticity and nonvanishing of the literal energy root product on the actual real-cut domain. -/

noncomputable section
set_option autoImplicit false
open scoped ENNReal
open Set Metric Complex Filter Topology
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV
theorem exists_hillEnergyRootFactor_bounded_majorant
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ k : ℕ, N ≤ k → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖hillEnergyRootFactor q hq hr (k+1) z-1‖ ≤ u k := by
  let D : ℝ := 4*‖q‖
  let C : ℝ := D+R+2*D^2
  have hD : 0 ≤ D := by positivity
  have hC : 0 ≤ C := by positivity
  have hs0 : Summable (fun n : ℕ => 1/(n : ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun k : ℕ => C/(k+1 : ℕ)^2) := by
    simpa only [div_eq_mul_inv,one_mul] using ((summable_nat_add_iff 1).mpr hs0).mul_left C
  obtain ⟨N,hN⟩ := exists_nat_gt (8*‖q‖+2*(D+R)+2)
  refine ⟨N,fun k : ℕ => C/(k+1 : ℕ)^2,hs,?_⟩
  intro k hk z hz
  have hkR : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hn2 : 2 ≤ k+1 := by
    have hn : (2 : ℝ) < k := by linarith [norm_nonneg q,norm_nonneg z]
    exact_mod_cast (show (2 : ℝ) ≤ (k+1 : ℕ) by push_cast; linarith)
  have hn : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hcut : 8*‖q‖ ≤ (k+1 : ℕ) := by push_cast; linarith [norm_nonneg z]
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr (k+1) hn2 hcut
  have hloc := p.localization q hq (k+1) (by omega) hcut
  have hlo : |hillRealLabels q hq hr (2*(k+1)-1)-freeHillValue (k+1)| ≤ D := by simpa only [hl,D,Nat.cast_add,Nat.cast_one] using hloc.1
  have hup : |hillRealLabels q hq hr (2*(k+1))-freeHillValue (k+1)| ≤ D := by simpa only [hu,D,Nat.cast_add,Nat.cast_one] using hloc.2
  have hnle : (k+1 : ℝ)^2 ≤ freeHillValue (k+1) := by
    have h := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ Real.pi^2 by nlinarith [Real.pi_gt_three])
      (sq_nonneg (k+1 : ℝ))
    simpa only [one_mul,freeHillValue,Int.cast_add,Int.cast_natCast,Int.cast_one] using h
  have hc : 1 ≤ freeHillValue (k+1) := by
    have hp : (1 : ℝ) ≤ (k+1 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k,sq_nonneg (k : ℝ)]
    exact hp.trans hnle
  have hlarge : 2*(D+‖z‖) < freeHillValue (k+1) := by
    have hsq : (k+1 : ℝ) ≤ (k+1 : ℝ)^2 := by nlinarith
    have hnR : 2*(D+‖z‖) < (k+1 : ℝ) := by linarith [norm_nonneg q]
    exact hnR.trans_le (hsq.trans hnle)
  have hf := norm_endpointRoot_div_sub_one_le
    (hillRealLabels q hq hr (2*(k+1)-1)) (hillRealLabels q hq hr (2*(k+1)))
    (freeHillValue (k+1)) D z hc hlo hup hlarge
  have hfC : ‖hillEnergyRootFactor q hq hr (k+1) z-1‖ ≤ C/freeHillValue (k+1) :=
    hf.trans (div_le_div_of_nonneg_right (by dsimp only [C]; linarith) (by linarith : 0 ≤ freeHillValue (k+1)))
  exact hfC.trans (div_le_div_of_nonneg_left hC (by positivity) (by exact_mod_cast hnle))

theorem not_mem_hillGapSegment_of_mem_realCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) (n : ℕ) (hn : 1 ≤ n) :
    z ∉ segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) := by
  rcases hz with hi | ⟨m,hm⟩
  · exact not_mem_real_segment_of_im_ne_zero _ _ z hi
  · intro hseg
    have himg := mem_image_of_mem Complex.reCLM.toLinearMap.toAffineMap hseg
    have hre : z.re ∈ segment ℝ (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)) := by
      simpa only [image_segment,Complex.reCLM_apply,Complex.ofReal_re] using! himg
    have hx := (segment_eq_Icc (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n))) ▸ hre
    by_cases hnm : n ≤ m
    · have hu := monotone_hillRealLabels q hq hr (show 2*n ≤ 2*m by omega)
      linarith [hx.2,hm.1]
    · have hl := monotone_hillRealLabels q hq hr (show 2*m+1 ≤ 2*n-1 by omega)
      linarith [hx.1,hm.2]

theorem analyticAt_hillEnergyRootFactor
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) (n : ℕ) (hn : 1 ≤ n) :
    AnalyticAt ℂ (hillEnergyRootFactor q hq hr n) z :=
  (analyticOnNhd_endpointRoot _ _ z (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr z hz n hn)).div_const

theorem hasProdUniformlyOn_hillEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (K : Set ℂ) (hK : IsCompact K) (hdom : K ⊆ hillL2RealCutDomain q hq hr) :
    HasProdUniformlyOn (fun k z => hillEnergyRootFactor q hq hr (k+1) z)
      (hillEnergyRootProduct q hq hr) K := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N,u,hu,hmajor⟩ := exists_hillEnergyRootFactor_bounded_majorant q hq hr R hR.le
  have hevent : ∀ᶠ k : ℕ in cofinite, ∀ z ∈ K, ‖hillEnergyRootFactor q hq hr (k+1) z-1‖ ≤ u k := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk
    exact fun z hz => hmajor k hk z (hbound z hz)
  have hc (k : ℕ) : ContinuousOn (fun z => hillEnergyRootFactor q hq hr (k+1) z-1) K := by
    intro z hz
    exact ((analyticAt_hillEnergyRootFactor q hq hr z (hdom hz) (k+1) (by omega)).continuousAt.sub
      continuousAt_const).continuousWithinAt
  have hp := hu.hasProdUniformlyOn_one_add hK hevent hc
  have he (k : ℕ) (z : ℂ) : 1+(hillEnergyRootFactor q hq hr (k+1) z-1) = hillEnergyRootFactor q hq hr (k+1) z := by ring
  simp only [he] at hp
  convert! hp using 1

theorem hasProdLocallyUniformlyOn_hillEnergyRootFactors
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    HasProdLocallyUniformlyOn (fun k z => hillEnergyRootFactor q hq hr (k+1) z)
      (hillEnergyRootProduct q hq hr) (hillL2RealCutDomain q hq hr) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (isOpen_hillL2RealCutDomain q hq hr)
  exact fun K hKsub hK => hasProdUniformlyOn_hillEnergyRootFactors q hq hr K hK hKsub

theorem analyticOnNhd_hillEnergyRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (hillEnergyRootProduct q hq hr) (hillL2RealCutDomain q hq hr) := by
  have hf (k : ℕ) : DifferentiableOn ℂ (hillEnergyRootFactor q hq hr (k+1)) (hillL2RealCutDomain q hq hr) := by
    intro z hz
    exact (analyticAt_hillEnergyRootFactor q hq hr z hz (k+1) (by omega)).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ (hillEnergyRootProduct q hq hr) (hillL2RealCutDomain q hq hr) :=
    (hasProdLocallyUniformlyOn_hillEnergyRootFactors q hq hr).differentiableOn
      (Filter.Eventually.of_forall (fun s => DifferentiableOn.fun_finsetProd (fun k _ => hf k)))
      (isOpen_hillL2RealCutDomain q hq hr)
  exact hd.analyticOnNhd (isOpen_hillL2RealCutDomain q hq hr)

theorem hillGroundShift_mem_slitPlane_of_mem_realCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    z-(hillRealLabels q hq hr 0 : ℂ) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  rcases hz with hi | ⟨n,hn⟩
  · right
    simpa only [sub_im,ofReal_im,sub_zero] using hi
  · left
    have h0 := monotone_hillRealLabels q hq hr (Nat.zero_le (2*n))
    simp only [sub_re,ofReal_re]
    linarith [hn.1]

theorem analyticOnNhd_hillEnergyCanonicalRootProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    AnalyticOnNhd ℂ (hillEnergyCanonicalRootProduct q hq hr) (hillL2RealCutDomain q hq hr) := by
  intro z hz
  have hs : AnalyticAt ℂ Complex.sqrt (z-hillRealLabels q hq hr 0) :=
    Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds
      (hillGroundShift_mem_slitPlane_of_mem_realCutDomain q hq hr z hz))
  have hc : AnalyticAt ℂ (fun w : ℂ => Complex.sqrt (w-hillRealLabels q hq hr 0)) z :=
    hs.comp (f := fun w : ℂ => w-hillRealLabels q hq hr 0) (analyticAt_id.sub analyticAt_const)
  change AnalyticAt ℂ (fun w : ℂ => -2*I*Complex.sqrt (w-hillRealLabels q hq hr 0)*hillEnergyRootProduct q hq hr w) z
  exact (analyticAt_const.mul hc).mul (analyticOnNhd_hillEnergyRootProduct q hq hr z hz)

theorem hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) : hillEnergyCanonicalRootProduct q hq hr z ≠ 0 := by
  have hzero : z-(hillRealLabels q hq hr 0 : ℂ) ≠ 0 := by
    intro he
    have hs := hillGroundShift_mem_slitPlane_of_mem_realCutDomain q hq hr z hz
    rw [he] at hs
    exact Complex.zero_notMem_slitPlane hs
  have hs : (Complex.sqrt (z-hillRealLabels q hq hr 0))^2 = z-hillRealLabels q hq hr 0 := by
    have h := Complex.cpow_nat_inv_pow (z-hillRealLabels q hq hr 0) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hroot : Complex.sqrt (z-hillRealLabels q hq hr 0) ≠ 0 := by
    intro he
    rw [he,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
    exact hzero hs.symm
  exact mul_ne_zero (mul_ne_zero (by norm_num : (-2*I : ℂ) ≠ 0) hroot)
    (hillEnergyRootProduct_ne_zero q hq hr z (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr z hz))

end NLS.KdV
