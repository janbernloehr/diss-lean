import NLS.KdV.HillDirichletSpectrumExhaustion
import NLS.ZakharovShabat.FreeCircleSeparation

/-! # Exact positive Dirichlet root selection by expanding energy circles -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem abs_hillDirichletEnergy_sub_free_le (n : ℕ) (hn : 2≤n) (hcut : 8*‖q‖≤(n : ℝ)) :
    |hillDirichletEnergy q hq hr n (by omega)-freeHillValue n|≤4*‖q‖ := by
  obtain ⟨p,hl,hu⟩ := hillRealLabels_high_pair q hq hr n hn hcut
  have hp := p.localization q hq n (by omega) hcut
  have hm := hillDirichletEnergy_mem_gap q hq hr n (by omega)
  rw [hl,hu] at hm
  exact abs_le.mpr ⟨by linarith [hm.1,(abs_le.mp hp.1).1],by linarith [hm.2,(abs_le.mp hp.2).2]⟩

/-- Each sufficiently high free half-integer energy circle separates
exactly the k-th and (k+1)-st actual Dirichlet labels. -/
theorem hillDirichletEnergy_free_circle_bracket (k : ℕ) (hk : 2≤k) (hcut : 8*‖q‖≤(k : ℝ)) :
    hillDirichletEnergy q hq hr k (by omega)<(centralCircleRadius k)^2 ∧
      (centralCircleRadius k)^2<hillDirichletEnergy q hq hr (k+1) (by omega) := by
  have hlow := abs_hillDirichletEnergy_sub_free_le q hq hr k hk hcut
  have hhigh := abs_hillDirichletEnergy_sub_free_le q hq hr (k+1) (by omega)
    (hcut.trans (by exact_mod_cast (Nat.le_succ k)))
  have hpi : 1≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hm1 := le_mul_of_one_le_left (show (0 : ℝ)≤(k : ℝ)+1/4 by positivity) hpi
  have hm2 := le_mul_of_one_le_left (show (0 : ℝ)≤(k : ℝ)+3/4 by positivity) hpi
  have hf1 : (centralCircleRadius k)^2-freeHillValue k=Real.pi^2*((k : ℝ)+1/4) := by
    simp only [centralCircleRadius,freeHillValue,Int.cast_natCast]
    ring
  have hf2 : freeHillValue (k+1 : ℕ)-(centralCircleRadius k)^2=Real.pi^2*((k : ℝ)+3/4) := by
    simp only [centralCircleRadius,freeHillValue]
    push_cast
    ring
  constructor
  · linarith [(abs_le.mp hlow).2,norm_nonneg q]
  · linarith [(abs_le.mp hhigh).1,norm_nonneg q]

/-- The first k positive Dirichlet labels are exactly all characteristic
zeros in the k-th closed energy disc; all of them lie strictly inside. -/
theorem eventually_hillDirichlet_sequence_circle_selection :
    ∃ K : ℕ, ∀ k : ℕ, K≤k →
      (∀ j : ℕ, (hillDirichletEnergySequence q hq hr j : ℂ)∈ball (0 : ℂ) ((centralCircleRadius k)^2) ↔ j<k) ∧
      (∀ E∈closedBall (0 : ℂ) ((centralCircleRadius k)^2),
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 ↔
          ∃ j<k, E=(hillDirichletEnergySequence q hq hr j : ℂ)) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (8*‖q‖+|hillDirichletEnergySequence q hq hr 0|+2)
  refine ⟨max 2 N,?_⟩
  intro k hk
  have hk2 : 2≤k := (le_max_left _ _).trans hk
  have hNk : (N : ℝ)≤k := by exact_mod_cast (le_max_right 2 N).trans hk
  have hcut : 8*‖q‖≤(k : ℝ) := by linarith [abs_nonneg (hillDirichletEnergySequence q hq hr 0)]
  have hrad := centralCircleRadius_pos k
  have hcircle : (k : ℝ)<centralCircleRadius k := by
    have hkR : (2 : ℝ)≤k := by exact_mod_cast hk2
    unfold centralCircleRadius
    nlinarith [Real.pi_gt_three]
  have hhead : |hillDirichletEnergySequence q hq hr 0|<(centralCircleRadius k)^2 := by
    have hkR : (2 : ℝ)≤k := by exact_mod_cast hk2
    nlinarith [norm_nonneg q]
  obtain ⟨hlo,hhi⟩ := hillDirichletEnergy_free_circle_bracket q hq hr k hk2 hcut
  have hinc := (strictMono_hillDirichletEnergySequence q hq hr).monotone
  have hbefore (j : ℕ) (hj : j<k) : |hillDirichletEnergySequence q hq hr j|<(centralCircleRadius k)^2 := by
    apply abs_lt.mpr
    constructor
    · have hm := hinc (Nat.zero_le j)
      linarith [(abs_lt.mp hhead).1]
    · have hm := hinc (show j≤k-1 by omega)
      have he : hillDirichletEnergySequence q hq hr (k-1)=hillDirichletEnergy q hq hr k (by omega) := by
        simp only [hillDirichletEnergySequence,Nat.sub_add_cancel (by omega : 1≤k)]
      rw [he] at hm
      exact hm.trans_lt hlo
  have hafter (j : ℕ) (hj : k≤j) : (centralCircleRadius k)^2<hillDirichletEnergySequence q hq hr j :=
    hhi.trans_le (hinc hj)
  refine ⟨?_,?_⟩
  · intro j
    simp only [mem_ball,dist_zero_right,norm_real,Real.norm_eq_abs]
    constructor
    · intro hj
      by_contra! hn
      have hh := hafter j hn
      exact (not_lt_of_ge ((le_abs_self _).trans hj.le)) hh
    · exact hbefore j
  · intro E hE
    constructor
    · intro hz
      obtain ⟨j,rfl⟩ := (hillL2DirichletCharacteristic_zero_iff_sequence q hq hr E).mp hz
      have hm : |hillDirichletEnergySequence q hq hr j|≤(centralCircleRadius k)^2 := by
        simpa only [mem_closedBall,dist_zero_right,norm_real,Real.norm_eq_abs] using hE
      refine ⟨j,?_,rfl⟩
      by_contra! hn
      exact (not_lt_of_ge ((le_abs_self _).trans hm)) (hafter j hn)
    · rintro ⟨j,_hj,rfl⟩
      exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)

end NLS.KdV
