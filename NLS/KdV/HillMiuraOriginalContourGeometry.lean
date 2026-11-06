import NLS.KdV.HillHminusPhysicalPsiZeros
import NLS.KdV.HillMiuraPeriodCircleGeometry
import NLS.ComplexAnalysis.QuadraticEnergyLoop

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- Every positive real Miura period circle maps inside the ORIGINAL
physical Hill cut domain, at the same index. The shift condition is the
actual nonzero characteristic, including low and collapsed gap cases. -/
theorem energy_contour_inside_original_cut (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ)) :
    (quadraticEnergyLoop (PiecewiseC1Loop.circle (D.center:ℂ) D.radius)
      P.miura.energyShift).Inside (hillL2RealCutDomain q.val q.property.1 q.property.2) := by
  let u : PeriodOneRealL2 := ⟨P.miura.lift (hillOriginalHminusSource q.val),
    hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2)⟩
  have he := P.original_labels_eq_squared_miuraDirac q hq hreal houtside c hshift
  have hrights (j : ℕ) : hillRealLabels q.val q.property.1 q.property.2 (2*j)=
      (hillMiuraDiracRight u.val j).re^2-c^2 := by
    by_cases hj : j=0
    · subst j
      simpa only [Nat.mul_zero,hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_initial,Nat.cast_zero,u] using congrFun he 0
    · simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_right _ _ (Nat.pos_of_ne_zero hj)] using congrFun he (2*j)
  have hlefts (j : ℕ) (hj : 0<j) : hillRealLabels q.val q.property.1 q.property.2 (2*j-1)=
      (hillMiuraDiracLeft u.val j).re^2-c^2 := by
    simpa only [hillMiuraSquaredLabels,hillMiuraPositiveFrequencies_left _ _ hj] using congrFun he (2*j-1)
  have hm := m.pos
  have hcast : (((m:ℕ)-1 : ℕ):ℤ)=((m:ℕ):ℤ)-1 := by omega
  have hprev := hrights ((m:ℕ)-1)
  rw [show 2*((m:ℕ)-1)=2*(m:ℕ)-2 by omega,hcast] at hprev
  have hnext := hlefts ((m:ℕ)+1) (by omega)
  rw [show 2*((m:ℕ)+1)-1=2*(m:ℕ)+1 by omega,Nat.cast_add,Nat.cast_one] at hnext
  have hl := hlefts (m:ℕ) hm
  have hr := hrights (m:ℕ)
  have hb := miuraPeriodCircle_adjacent_bounds u ((m:ℕ):ℤ) D
  have hp := miuraPeriodCircle_left_pos u m D
  have hprevnonneg : 0≤(hillMiuraDiracRight u.val (((m:ℕ):ℤ)-1)).re := by
    have h := hillMiuraPositiveFrequencies_nonneg u (2*((m:ℕ)-1))
    by_cases hzero : (m:ℕ)-1=0
    · simp only [hzero,Nat.mul_zero,hillMiuraPositiveFrequencies_initial] at h
      have hz : ((m:ℕ):ℤ)-1=0 := by omega
      simpa only [hz] using h
    · rw [hillMiuraPositiveFrequencies_right _ _ (Nat.pos_of_ne_zero hzero),hcast] at h
      exact h
  have hlpos : 0<(hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re :=
    hillMiura_positive_gap_left_pos u _ (by exact_mod_cast hm)
  have hrpos : 0<(hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re :=
    hlpos.trans_le (hillMiuraDiracPair_ordered u.val _)
  have hnpos : 0<(hillMiuraDiracLeft u.val (((m:ℕ):ℤ)+1)).re :=
    hillMiura_positive_gap_left_pos u _ (by omega)
  intro i t
  let z := (PiecewiseC1Loop.circle (D.center:ℂ) D.radius).edge i t
  have hz : z∈sphere (D.center:ℂ) D.radius := circleMap_mem_sphere _ D.radius_pos.le _
  have hzbound := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
  have hzpos : 0<z.re := hp.trans_le hzbound.1
  change (z^2-P.miura.energyShift)∈hillL2RealCutDomain q.val q.property.1 q.property.2
  by_cases hzi : z.im=0
  · have hzne : z.re∉Icc (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re
        (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re := by
      intro hx
      have hmem := sourcePeriodicSegment_mem_of_realIcc (by norm_num) (by norm_num)
        (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z.re hx
      have hez : (z.re:ℂ)=z := Complex.ext rfl hzi.symm
      rw [hez] at hmem
      exact D.sphere_subset_rootDomain hz ((m:ℕ):ℤ) hmem
    have henergy : (z^2-P.miura.energyShift).re=z.re^2-c^2 := by
      rw [hshift]
      simp only [pow_two,sub_re,mul_re,hzi,mul_zero,ofReal_re,ofReal_im,sub_zero]
    rcases lt_or_ge z.re (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re with hx | hx
    · refine Or.inr ⟨(m:ℕ)-1,?_⟩
      rw [show 2*((m:ℕ)-1)+1=2*(m:ℕ)-1 by omega,
        show 2*((m:ℕ)-1)=2*(m:ℕ)-2 by omega,hprev,hl,henergy]
      constructor <;> nlinarith [hb.1,hzbound.1]
    · have hx' : (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re<z.re :=
        lt_of_not_ge (fun h => hzne ⟨hx,h⟩)
      refine Or.inr ⟨(m:ℕ),?_⟩
      rw [hr,hnext,henergy]
      constructor <;> nlinarith [hb.2,hzbound.2]
  · apply Or.inl
    rw [hshift]
    simp only [pow_two,sub_im,mul_im,ofReal_re,ofReal_im,mul_zero,zero_mul,add_zero,sub_zero]
    intro h
    have hmul := mul_ne_zero hzpos.ne' hzi
    apply hmul
    linear_combination h/2

end HillHminusPsiChart
end NLS.KdV
