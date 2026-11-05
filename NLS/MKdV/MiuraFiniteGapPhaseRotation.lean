import NLS.MKdV.MiuraFiniteGapTerminalGenerator
import NLS.MKdV.MiuraFiniteGapPhaseTerminalRegularity
import NLS.FunctionalAnalysis.ScalarLinearODE

/-! # Complete physical action rotation of the actual independent finite-gap phase

The all-configuration generator integrates along the original action
group. Terminal divisors and closed gaps are included for every real time.
-/
noncomputable section
open Set Complex Filter Topology NLS.LinearVolterra NLS.ZakharovShabat NLS.KdV
namespace NLS.MKdV

theorem miuraNativeRealActionFlow_add (s : ℕ) (a : MiuraRealSobolevSource s)
    (j : ℕ) (t u : ℝ) :
    miuraNativeRealActionFlow s (miuraNativeRealActionFlow s a j t) j u =
      miuraNativeRealActionFlow s a j (t+u) := by
  apply Subtype.ext
  exact miuraActionFlow_add s a.val (fun k => a.property k) j t u

theorem miuraNativeClosedComplement_actionFlow (s : ℕ) (hs : 1 ≤ s) (F : Finset ℕ)
    (a : MiuraRealSobolevSource s) (ha : a ∈ miuraNativeClosedComplement s hs F) (j : ℕ) (t : ℝ) :
    miuraNativeRealActionFlow s a j t ∈ miuraNativeClosedComplement s hs F := by
  intro k hk
  exact (congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillActionCurve s hs a j t)
    (miuraNativeHillPotential s hs a) (miuraNativeHillLabels_actionFlow s hs a j t)) (k+1)).trans (ha k hk)

theorem miuraNativeNLSAngularCoordinate_actionFlow_ne_zero
    (s : ℕ) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    miuraNativeNLSAngularCoordinate s n (miuraNativeRealActionFlow s a j t) ≠ 0 := by
  intro hz
  have hnorm := norm_miuraNativeNLSAngularCoordinate_actionFlow s n hn a j hj t
  rw [hz,norm_zero] at hnorm
  exact ha (norm_eq_zero.mp hnorm.symm)

theorem hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap_allConfigurations
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hclosed : a ∈ miuraNativeClosedComplement s hs F)
    (hangle : miuraNativeNLSAngularCoordinate s n a ≠ 0) (t : ℝ) :
    HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r))
      (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) t := by
  let b := miuraNativeRealActionFlow s a j t
  have hb := miuraNativeClosedComplement_actionFlow s hs F a hclosed j t
  have hbn := miuraNativeNLSAngularCoordinate_actionFlow_ne_zero s a n hn hangle j hj t
  have hdiff := differentiableAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap s hs b j hj n hn F 0
    (fun k hk => by simpa only [miuraNativeHillActionCurve_zero,miuraNativeHillPotential] using hb k hk)
  have h0 : HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s b j r))
      (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn b) 0 := by
    apply hdiff.hasDerivAt.congr_deriv
    exact miuraNativeOppositeAbelianPhase_Lie_finiteGap s hs b j hj n hn F hb hbn
  have h0' : HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s b j r))
      (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn b) (t-t) := by
    simpa only [sub_self] using h0
  have ht : HasDerivAt (fun r : ℝ => r-t) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const t
  have hd := h0'.scomp (h := fun r : ℝ => r-t) t ht
  have he : (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s b j (r-t))) =
      (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) := by
    funext r
    change miuraNativeOppositeAbelianPhase s hs n hn
      (miuraNativeRealActionFlow s (miuraNativeRealActionFlow s a j t) j (r-t)) = _
    rw [miuraNativeRealActionFlow_add,add_sub_cancel]
  change HasDerivAt (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s b j (r-t)))
    ((1:ℝ) • (-I*(if j = n then 1 else 0)*miuraNativeOppositeAbelianPhase s hs n hn b)) t at hd
  rw [he,one_smul] at hd
  exact hd

theorem miuraNativeOppositeAbelianPhase_actionFlow_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (hclosed : a ∈ miuraNativeClosedComplement s hs F) (t : ℝ) :
    miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) =
      Complex.exp (-(if n = j then I else 0)*(t:ℂ))*miuraNativeOppositeAbelianPhase s hs n hn a := by
  by_cases hangle : miuraNativeNLSAngularCoordinate s n a = 0
  · have hn0 := (miuraNativeHill_halfLength_zero_iff_angular_zero s hs a n hn).mpr hangle
    have horbit := miuraNativeFullAbelianPhase_actionFlow_closed s hs a j n hn 0
      (by simpa only [miuraNativeHillActionCurve_zero] using hn0) t
    rw [miuraNativeOppositeAbelianPhase,horbit,map_zero,
      miuraNativeOppositeAbelianPhase_closed s hs n hn a hangle,mul_zero]
  · have hd := hasDerivAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap_allConfigurations
      s hs a j hj n hn F hclosed hangle
    have he := NLS.FunctionalAnalysis.eq_scalarExponential_of_hasDerivAt _ _ hd t
    have hα : -I*(if j = n then (1:ℂ) else 0) = -(if n = j then I else 0) := by
      by_cases h : j = n
      · simp only [h,ite_true,mul_one]
      · simp only [if_neg h,if_neg (Ne.symm h),mul_zero,neg_zero]
    simpa only [hα,miuraNativeRealActionFlow_zero] using he

end NLS.MKdV
