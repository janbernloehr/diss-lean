import NLS.KdV.HillHminusPhysicalPsiZeros
import NLS.KdV.HillMiuraPeriodCircleGeometry
import NLS.KdV.HillRealGapContours
import NLS.ComplexAnalysis.QuadraticEnergyLoop

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
namespace HillHminusPsiChart

/-- Both real crossings of every positive Miura period circle map into
the SAME original physical adjacent bands, including low and collapsed gaps.
The shift condition uses the actual nonzero characteristic. -/
theorem energy_contour_endpoints_in_original_bands (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal (P.miura.lift (hillOriginalHminusSource q.val))) ((m:ℕ):ℤ)) :
    ((D.center-D.radius)^2-c^2)∈Ioo
      (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-2))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1)) ∧
    ((D.center+D.radius)^2-c^2)∈Ioo
      (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)))
      (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)+1)) := by
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
  have hleft : hillMiuraDiracLeft u.val ((m:ℕ):ℤ)∈ball (D.center:ℂ) D.radius :=
    D.gap (left_mem_segment ℝ _ _)
  have hright : hillMiuraDiracRight u.val ((m:ℕ):ℤ)∈ball (D.center:ℂ) D.radius :=
    D.gap (right_mem_segment ℝ _ _)
  have hlt := re_bounds_of_mem_realCenteredBall hleft
  have hrt := re_bounds_of_mem_realCenteredBall hright
  rw [hprev,hl,hr,hnext]
  constructor <;> constructor <;> nlinarith [hb.1,hb.2]

end HillHminusPsiChart

/-- Both real-axis crossings of the original intrinsic circle lie in
the prescribed adjacent bands, also when its gap is collapsed. -/
theorem hillIntrinsicCircle_endpoints_in_bands (q : RealPeriodOneHillPotential)
    (m : ℕ+) :
    (hillRealGapCenter q.val q.property.1 q.property.2 m-
      (hillRealGapHalfLength q.val q.property.1 q.property.2 m+
        hillRealGapCollar q.val q.property.1 q.property.2 m))∈
      Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-2))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1)) ∧
    (hillRealGapCenter q.val q.property.1 q.property.2 m+
      (hillRealGapHalfLength q.val q.property.1 q.property.2 m+
        hillRealGapCollar q.val q.property.1 q.property.2 m))∈
      Ioo (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)))
        (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)+1)) := by
  obtain ⟨_,hη,hl,hr,_⟩ := hillRealGapContour_geometry q.val q.property.1 q.property.2 m m.pos
  have hminl := min_le_left
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1)-
      hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-2))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)+1)-
      hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)))
  have hminr := min_le_right
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-1)-
      hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)-2))
    (hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)+1)-
      hillRealLabels q.val q.property.1 q.property.2 (2*(m:ℕ)))
  unfold hillRealGapCollar at hη ⊢
  constructor <;> constructor <;> linarith

end NLS.KdV
