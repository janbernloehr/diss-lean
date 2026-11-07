import NLS.KdV.HillMiuraCommonGapContour
import NLS.KdV.MiuraHillPsiLoopPeriods
import NLS.ComplexAnalysis.EnergySqrtLoop

/-! The square-root image of an original common energy contour avoids
the ACTUAL frequency cut and has winding one about its actual midpoint.
Consequently it computes every normalized Hill differential period. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillMiura_frequencyLoop_inside_cutDisk
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (Γ : PiecewiseC1Loop) (hdom : Γ.Inside (energyFrequencyDomain (c:ℂ)))
    (hΓ : Γ.Inside (energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))))) :
    (Γ.frequencyLoop (c:ℂ) hdom).Inside (ball (D.center:ℂ) D.radius \
      sourcePeriodicSegment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) := by
  intro i t
  change energyFrequency (c:ℂ) (Γ.edge i t) ∈ ball (D.center:ℂ) D.radius ∧ _
  refine ⟨(hΓ i t).1.2,?_⟩
  intro hcut
  obtain ⟨E,hE,he⟩ := hillMiura_gap_energy_mem_original q hq u c hi hc m _ hcut
  have hback : (energyFrequency (c:ℂ) (Γ.edge i t))^2-(c:ℂ) = Γ.edge i t := by
    rw [energyFrequency_sq]
    ring
  exact (hΓ i t).2 ⟨E,hE,he.symm.trans hback⟩

theorem hillMiura_frequencyLoop_winding_one
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) (Γ : PiecewiseC1Loop) (hdom : Γ.Inside (energyFrequencyDomain (c:ℂ)))
    (hΓ : Γ.Inside (energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))))
    (hwind : ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))),
      Γ.windingIntegral (E:ℂ) = 1) :
    (Γ.frequencyLoop (c:ℂ) hdom).windingIntegral
      (sourceStandardRootMidpoint (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) = 1 := by
  have hin := hillMiura_frequencyLoop_inside_cutDisk q hq u c hi hc m D Γ hdom hΓ
  have hm := sourcePeriodicMidpoint_mem_segment (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)
  obtain ⟨E,hE,he⟩ := hillMiura_gap_energy_mem_original q hq u c hi hc m _ hm
  apply Γ.frequencyLoop_winding_one_of_positive_disk (c:ℂ) hdom D.center D.radius _ hpos
    (fun i t => (hin i t).1) (D.gap hm) _ _
  · intro i t heq
    exact (hin i t).2 (heq.symm ▸ hm)
  · rw [he]
    exact hwind E hE

theorem hillMiura_common_energy_period
    (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) (Γ : PiecewiseC1Loop) (hdom : Γ.Inside (energyFrequencyDomain (c:ℂ)))
    (hΓ : Γ.Inside (energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))))
    (hwind : ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))),
      Γ.windingIntegral (E:ℂ) = 1) (n : ℕ+) :
    (2*Real.pi:ℂ)⁻¹*Γ.integral (fun E => A.differential n (c:ℂ) (E,u.val)) = if m = n then 1 else 0 := by
  have hin := hillMiura_frequencyLoop_inside_cutDisk q hq u c hi hc m D Γ hdom hΓ
  have hw := hillMiura_frequencyLoop_winding_one q hq u c hi hc m D hpos Γ hdom hΓ hwind
  have hp : (Γ.frequencyLoop (c:ℂ) hdom).Inside {z : ℂ | 0 < z.re} := by
    intro i t
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall (hin i t).1)
    change 0 < ((Γ.frequencyLoop (c:ℂ) hdom).edge i t).re
    linarith [hb.1]
  have h := A.energy_loop_period n m u.val (A.real_mem_source u) (c:ℂ) D
    (Γ.frequencyLoop (c:ℂ) hdom) hin hp
  rw [Γ.integral_energy_frequencyLoop (c:ℂ) hdom,hw,mul_one] at h
  exact h

end NLS.KdV
