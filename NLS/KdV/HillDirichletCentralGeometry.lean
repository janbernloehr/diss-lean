import NLS.KdV.HillDirichletLabelContinuity
import NLS.KdV.HillGapNumeratorDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem strictMono_hillDirichletEnergy_sequence :
    StrictMono (fun j : ℕ => hillDirichletEnergy q hq hr (j+1) (by omega)) :=
  strictMono_nat_of_lt_succ (fun j => hillDirichletEnergy_lt_succ q hq hr (j+1) (by omega))

/-- For every sufficiently large central circle, all of the first k
original gap-labelled Dirichlet energies lie strictly inside it. -/
theorem exists_hillDirichletEnergy_central_containment :
    ∃ K : ℕ, ∀ k : ℕ, K≤k → ∀ j : ℕ, j<k →
      (hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ)∈
        ball (0 : ℂ) ((centralCircleRadius k)^2) := by
  obtain ⟨K0,hK0⟩ := exists_nat_gt (8*‖q‖+2)
  obtain ⟨K1,hK1⟩ := eventually_atTop.mp
    (tendsto_hillEnergyCircleRadius.eventually_ge_atTop (|hillRealLabels q hq hr 0|+1))
  refine ⟨max K0 K1,?_⟩
  intro k hk j hj
  have hk0 : K0≤k := (le_max_left _ _).trans hk
  have hk1 : K1≤k := (le_max_right _ _).trans hk
  have hkR : (K0 : ℝ)≤k := by exact_mod_cast hk0
  have hk2 : 2≤k := by
    have hh : (2 : ℝ)<k := by linarith [norm_nonneg q]
    exact_mod_cast hh.le
  have hcut : 8*‖q‖≤(k : ℝ) := by linarith
  have hlabel := hillDirichletEnergy_mem_gap q hq hr (j+1) (by omega)
  have hlo : hillRealLabels q hq hr 0≤hillDirichletEnergy q hq hr (j+1) (by omega) :=
    (monotone_hillRealLabels q hq hr (by omega : 0≤2*(j+1)-1)).trans hlabel.1
  have hhi : hillDirichletEnergy q hq hr (j+1) (by omega)≤hillRealLabels q hq hr (2*k) :=
    hlabel.2.trans (monotone_hillRealLabels q hq hr (by omega : 2*(j+1)≤2*k))
  obtain ⟨p,_,hu⟩ := hillRealLabels_high_pair q hq hr k hk2 hcut
  have hup := (abs_le.mp (p.localization q hq k (by omega) hcut).2).2
  rw [← hu] at hup
  have henergy : hillRealLabels q hq hr (2*k)≤freeHillValue k+4*‖q‖ := by linarith
  have hfree : freeHillValue k+4*‖q‖<(centralCircleRadius k)^2 := by
    have hpi2 : 9≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
    have hh := mul_le_mul_of_nonneg_right hpi2 (show 0≤(k : ℝ) by positivity)
    unfold freeHillValue centralCircleRadius
    push_cast
    nlinarith [norm_nonneg q,sq_nonneg Real.pi]
  have hbig := hK1 k hk1
  have hleft : -(centralCircleRadius k)^2<hillDirichletEnergy q hq hr (j+1) (by omega) := by
    have hh := neg_abs_le (hillRealLabels q hq hr 0)
    linarith
  rw [mem_ball,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_lt]
  exact ⟨hleft,lt_of_le_of_lt (hhi.trans henergy) hfree⟩

end NLS.KdV
