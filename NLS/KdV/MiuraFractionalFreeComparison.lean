import NLS.ZakharovShabat.PeriodicH1UniformRemainderL2Budget
import NLS.KdV.HillMiuraL2Discriminant
import NLS.SequenceSpaces.SobolevFrequencyTruncation

/-! Quantitative uniform free comparison for fractional Sobolev Miura
sources. The constant depends on the L2 ball and strip, while the full
fractional norm enters linearly with the exact N^(-s) decay. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.WeightedCoeff NLS.LinearVolterra
namespace NLS.KdV

theorem norm_hillMiuraDiagonal_le_two (u : Coeff 2) : ‖hillMiuraDiagonal u‖≤2*‖u‖ := by
  change ‖CoeffPair.inlCLM u+CoeffPair.inrCLM u‖≤_
  simpa only [CoeffPair.norm_inlCLM,CoeffPair.norm_inrCLM,two_mul] using norm_add_le (CoeffPair.inlCLM u) (CoeffPair.inrCLM u)

def miuraFractionalFreeConstant (R H : ℝ) : ℝ :=
  2*Real.exp (2*H+4*R)+(8+2*Real.pi)*(1+2*R*Real.exp (2*R))*Real.exp H

theorem miuraFractionalFreeConstant_nonneg (R H : ℝ) (hR : 0≤R) :
    0≤miuraFractionalFreeConstant R H := by unfold miuraFractionalFreeConstant; positivity

theorem norm_miuraL2SolutionCurve_sub_free_fractional
    (s : ℝ) (hs : 0≤s) (hs1 : s≤1) (u : WeightedCoeff (Weight.sobolev s) 2)
    (R H : ℝ) (hR : ‖sobolevToL2 hs u‖≤R) (N : ℕ) (hN : 1≤N)
    (z : ℂ) (hz : (N:ℝ)≤‖z‖) (hH : |z.im|≤H) (v : ℂ × ℂ) :
    ‖l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal (sobolevToL2 hs u))) z v-
        l2SolutionCurve 0 z v‖ ≤
      miuraFractionalFreeConstant R H*(N:ℝ)^(-s)*‖u‖*‖v‖ := by
  let a := sobolevHeadToH1 s hs1 N hN u
  let b := scalarInclusion a
  let U := sourcePhysicalL2 (hillMiuraDiagonal (sobolevToL2 hs u))
  let A := sourcePeriodicH1L2Class (a,a)
  have hR0 : 0≤R := (norm_nonneg _).trans hR
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hzpos : 0<‖z‖ := hNp.trans_le hz
  have hz0 : z≠0 := norm_pos_iff.mp hzpos
  have hb : ‖b‖≤R := (norm_scalarInclusion_sobolevHeadToH1_le s hs hs1 N hN u).trans hR
  have hArep : A=sourcePhysicalL2 (hillMiuraDiagonal b) := by
    change sourcePeriodicH1L2Class (a,a)=sourcePhysicalL2 (hillMiuraDiagonal (scalarInclusion a))
    rw [sourcePeriodicH1L2Class_eq_sourcePhysical,← hillMiuraDiagonal_scalarInclusion]
  have hUnorm : ‖U‖≤2*R := by
    rw [norm_sourcePhysicalL2]
    exact (norm_hillMiuraDiagonal_le_two _).trans (mul_le_mul_of_nonneg_left hR (by norm_num))
  have hAnorm : ‖A‖≤2*R := by
    rw [hArep,norm_sourcePhysicalL2]
    exact (norm_hillMiuraDiagonal_le_two _).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
  have hdiff : ‖U-A‖≤2*((N:ℝ)^(-s)*‖u‖) := by
    rw [hArep,← map_sub,← map_sub,norm_sourcePhysicalL2]
    exact (norm_hillMiuraDiagonal_le_two _).trans
      (mul_le_mul_of_nonneg_left (norm_sobolevHeadToH1_remainder_le s hs hs1 N hN u) (by norm_num))
  have hstab := norm_l2SolutionCurve_sub_le_of_strip_bounds U A z v (2*R) H hUnorm hAnorm hH
  have hstab' : ‖l2SolutionCurve U z v-l2SolutionCurve A z v‖ ≤
      (2*Real.exp (2*H+4*R))*(N:ℝ)^(-s)*‖u‖*‖v‖ := by
    apply hstab.trans
    apply (mul_le_mul_of_nonneg_left hdiff (by positivity)).trans_eq
    rw [show 2*H+2*(2*R)=2*H+4*R by ring]
    ring
  let K : ℝ := (8+2*Real.pi)*(1+2*R*Real.exp (2*R))*Real.exp H
  have hK : 0≤K := by dsimp only [K]; positivity
  have hraw : ‖sobolevSourceInclusion (a,a)‖≤2*R := by
    rw [← hillMiuraDiagonal_scalarInclusion]
    exact (norm_hillMiuraDiagonal_le_two b).trans (mul_le_mul_of_nonneg_left hb (by norm_num))
  have hfree := norm_periodicH1SolutionCurve_sub_free_L2_budget (a,a) (2*R) H hraw z hz0 hH v
  have hhead : ‖(a,a)‖≤(N:ℝ)^(1-s)*‖u‖ := by
    simpa only [Prod.norm_def,max_self] using norm_sobolevHeadToH1_le s hs1 N hN u
  have hratio : (N:ℝ)^(1-s)/‖z‖≤(N:ℝ)^(-s) := by
    rw [show 1-s=1+(-s) by ring,Real.rpow_add hNp,Real.rpow_one]
    apply (div_le_iff₀ hzpos).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz (Real.rpow_nonneg hNp.le (-s))
  have hfree' : ‖l2SolutionCurve A z v-l2SolutionCurve 0 z v‖≤K*(N:ℝ)^(-s)*‖u‖*‖v‖ := by
    apply hfree.trans
    calc
      _ ≤ K*((N:ℝ)^(1-s)*‖u‖)/‖z‖*‖v‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
        apply div_le_div_of_nonneg_right _ (norm_nonneg z)
        exact mul_le_mul_of_nonneg_left hhead hK
      _ = (K*((N:ℝ)^(1-s)/‖z‖))*‖u‖*‖v‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hK) (norm_nonneg u)) (norm_nonneg v)
  have htri := norm_add_le (l2SolutionCurve U z v-l2SolutionCurve A z v)
    (l2SolutionCurve A z v-l2SolutionCurve 0 z v)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans ((add_le_add hstab' hfree').trans_eq (by unfold miuraFractionalFreeConstant; dsimp only [K]; ring))

end NLS.KdV
