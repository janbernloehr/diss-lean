import NLS.KdV.HillProductJointPeriods
import NLS.ZakharovShabat.SourceCorollary10_6

/-! Near EVERY real Dirac source, ONE complex source neighborhood
and ONE genuine isolating-circle family work before ALL Hill numerator
indices. The literal periods are jointly analytic in full independent
l2 zero data, energy shift and the moving source on that SAME domain. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_hillEnergyProduct_common_period_neighborhood (ψ : CoeffPair 2)
    (hreal : IsRealType (CoeffPair.toMax 2 ψ)) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ ψ ∈ V ∧
    ∃ a R : ℤ → ℝ, (∀ m : ℤ, 0 < R m) ∧
      (∀ χ ∈ V, ∀ m : ℤ,
        ∃ D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) χ m,
          D.center = a m ∧ D.radius = R m) ∧
      ∀ (n : ℕ+) (m : ℤ), AnalyticOnNhd ℂ
        (hillEnergyProductJointPeriod n (a m:ℂ) (R m)) (univ ×ˢ (univ ×ˢ V)) := by
  obtain ⟨W,hW,_,hRW,hDom,hRoot⟩ := exists_global_source_analytic_canonicalRoot (p := 2) (by norm_num) (by norm_num)
  obtain ⟨W₀,_,_,hR₀,H⟩ := sourceCorollary10_6 (p := 2) (by norm_num) (by norm_num)
  obtain ⟨U,hU,_,hψU,_,D,c,hD⟩ := H.neighborhoods ψ (hR₀ hreal)
  choose a R hR he using hD.discs
  let V := U ∩ W
  refine ⟨V,hU.inter hW,⟨hψU,hRW hreal⟩,a,R,hR,?_,?_⟩
  · intro χ hχ m
    let P := hD.toSourceIsolatingNeighborhoods.periodCircle χ hχ.1 m (a m) (R m) (hR m) (he m)
    exact ⟨P,rfl,rfl⟩
  · intro n m
    apply analyticOnNhd_hillEnergyProductJointPeriod W V hDom hRoot (hU.inter hW)
      inter_subset_right (a m:ℂ) (R m) (hR m).le _ n
    intro χ hχ
    exact (hD.toSourceIsolatingNeighborhoods.periodCircle χ hχ.1 m (a m) (R m) (hR m) (he m)).sphere_subset_rootDomain

end NLS.KdV
