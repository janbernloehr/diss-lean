import NLS.KdV.HillMiuraTransportedLoop
import NLS.KdV.MiuraHillEnergyRootIndependence
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-! The two actual normalized periods on a common original energy
contour agree even when the Miura shifts differ. Their difference has
zero period on an actual positive frequency circle. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillMiura_energyRootDomain_of_mem_energyCutDisk
    (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (E : ℂ) (hE : E ∈ energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :
    (E,u.val) ∈ A.energyRootDomain (c:ℂ) := by
  refine ⟨A.real_mem_source u,hE.1.1,D.cutDisk_subset_rootDomain ⟨hE.1.2,?_⟩⟩
  intro hcut
  obtain ⟨a,ha,he⟩ := hillMiura_gap_energy_mem_original q hq u c hi hc m _ hcut
  have hback : (energyFrequency (c:ℂ) E)^2-(c:ℂ) = E := by
    rw [energyFrequency_sq]
    ring
  exact hE.2 ⟨a,ha,he.symm.trans hback⟩

theorem hillMiura_common_energy_difference_zero
    (A B : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u v : PeriodOneRealL2) (c d : ℝ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (d:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (hd : -(d:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (T : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal v.val) ((m:ℕ):ℤ))
    (hD : 0 < D.center-D.radius) (hT : 0 < T.center-T.radius)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside ((energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius ∩
      energyFrequencyDisk (d:ℂ) (T.center:ℂ) T.radius) \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))))
    (hw : ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))),
      Γ.windingIntegral (E:ℂ) = 1) (n : ℕ+) :
    Γ.integral (fun E => (A.numerator n (E+(c:ℂ),u.val)-B.numerator n (E+(d:ℂ),v.val))/
      hillHminusMiuraRoot u.val (c:ℂ) E) = 0 := by
  have hΓD : Γ.Inside (energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :=
    fun i t => ⟨(hΓ i t).1.1,(hΓ i t).2⟩
  have hΓT : Γ.Inside (energyFrequencyDisk (d:ℂ) (T.center:ℂ) T.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) :=
    fun i t => ⟨(hΓ i t).1.2,(hΓ i t).2⟩
  have hp := hillMiura_common_energy_period A q hq u c hu hc m D hD Γ
    (fun i t => (hΓD i t).1.1) hΓD hw n
  have hq' := hillMiura_common_energy_period B q hq v d hv hd m T hT Γ
    (fun i t => (hΓT i t).1.1) hΓT hw n
  let U := (fun E : ℂ => (E,u.val)) ⁻¹' A.energyRootDomain (c:ℂ)
  let V := (fun E : ℂ => (E,v.val)) ⁻¹' B.energyRootDomain (d:ℂ)
  have hU : ContinuousOn (fun E => A.differential n (c:ℂ) (E,u.val)) U :=
    (A.analytic_differential n (c:ℂ)).continuousOn.comp'
      (f := fun E : ℂ => (E,u.val)) (continuous_id.prodMk continuous_const).continuousOn
      (Set.mapsTo_preimage _ _)
  have hV : ContinuousOn (fun E => B.differential n (d:ℂ) (E,v.val)) V :=
    (B.analytic_differential n (d:ℂ)).continuousOn.comp'
      (f := fun E : ℂ => (E,v.val)) (continuous_id.prodMk continuous_const).continuousOn
      (Set.mapsTo_preimage _ _)
  have hin : Γ.Inside (U ∩ V) := by
    intro i t
    exact ⟨hillMiura_energyRootDomain_of_mem_energyCutDisk A q hq u c hu hc m D _ (hΓD i t),
      hillMiura_energyRootDomain_of_mem_energyCutDisk B q hq v d hv hd m T _ (hΓT i t)⟩
  have he : Γ.integral (fun E => (A.numerator n (E+(c:ℂ),u.val)-B.numerator n (E+(d:ℂ),v.val))/
      hillHminusMiuraRoot u.val (c:ℂ) E) =
      Γ.integral (fun E => A.differential n (c:ℂ) (E,u.val)-B.differential n (d:ℂ) (E,v.val)) := by
    apply Γ.integral_congr hin
    intro E hE
    dsimp only [MiuraHillPsiFamily.differential]
    rw [hillHminusMiuraRoot_eq_of_real_images A B q u v c d hu hv hE]
    ring
  rw [he,Γ.integral_sub _ _ (hU.mono inter_subset_left) (hV.mono inter_subset_right) hin]
  have hn : (2*Real.pi:ℂ)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
  apply (mul_eq_zero.mp (show (2*Real.pi:ℂ)⁻¹ *
      (Γ.integral (fun E => A.differential n (c:ℂ) (E,u.val))-
       Γ.integral (fun E => B.differential n (d:ℂ) (E,v.val))) = 0 by
    rw [mul_sub,hp,hq',sub_self])).resolve_left hn

theorem hillMiura_circle_zero_of_energy_difference_zero
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ))
    (hpos : 0 < D.center-D.radius) (Γ : PiecewiseC1Loop)
    (hdom : Γ.Inside (energyFrequencyDomain (c:ℂ)))
    (hΓ : Γ.Inside (energyFrequencyDisk (c:ℂ) (D.center:ℂ) D.radius \
      Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))))
    (hw : ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))),
      Γ.windingIntegral (E:ℂ) = 1) (P Q : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ (fun z : ℂ => 2*z*(P (z^2-(c:ℂ))-Q (z^2-(c:ℂ)))) univ)
    (hzero : Γ.integral (fun E => (P E-Q E)/hillHminusMiuraRoot u.val (c:ℂ) E) = 0) :
    (∮ z in C((D.center:ℂ),D.radius), (2*z*(P (z^2-(c:ℂ))-Q (z^2-(c:ℂ))))/
      sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0 := by
  have hin := hillMiura_frequencyLoop_inside_cutDisk q hq u c hi hc m D Γ hdom hΓ
  have hwind := hillMiura_frequencyLoop_winding_one q hq u c hi hc m D hpos Γ hdom hΓ hw
  have hp : (Γ.frequencyLoop (c:ℂ) hdom).Inside {z : ℂ | 0 < z.re} := by
    intro i t
    have hb := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall (hin i t).1)
    change 0 < ((Γ.frequencyLoop (c:ℂ) hdom).edge i t).re
    linarith [hb.1]
  have he : (quadraticEnergyLoop (Γ.frequencyLoop (c:ℂ) hdom) (c:ℂ)).integral
      (fun E => (P E-Q E)/hillHminusMiuraRoot u.val (c:ℂ) E) =
      (Γ.frequencyLoop (c:ℂ) hdom).integral (fun z => (2*z*(P (z^2-(c:ℂ))-Q (z^2-(c:ℂ))))/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) := by
    apply integral_quadraticEnergyLoop _ (c:ℂ) _ _ _ hp
    intro z hz
    rw [hillHminusMiuraRoot_at_squared_energy u.val (c:ℂ) z hz]
    ring
  rw [Γ.integral_energy_frequencyLoop (c:ℂ) hdom,hzero,
    D.entireNumerator_loop_integral _ hF _ hin,hwind,mul_one] at he
  exact he.symm

end NLS.KdV
