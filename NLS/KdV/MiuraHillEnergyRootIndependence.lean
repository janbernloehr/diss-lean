import NLS.KdV.MiuraHillPsiEnergyRoot

/-! Actual real-source energy sheets are independent of the Miura lift
and the physical constant shift on their ENTIRE common energy domains.
The existing nonreal physical-sheet identity fixes the sign; density and
continuity also identify the real-band values. -/
noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillHminusMiuraRoot_eq_of_real_images
    (A B : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (u v : PeriodOneRealL2) (c d : ℝ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (d:ℂ))) :
    EqOn (hillHminusMiuraRoot u.val (c:ℂ)) (hillHminusMiuraRoot v.val (d:ℂ))
      ((fun E : ℂ => (E,u.val)) ⁻¹' A.energyRootDomain (c:ℂ) ∩
       (fun E : ℂ => (E,v.val)) ⁻¹' B.energyRootDomain (d:ℂ)) := by
  let U := (fun E : ℂ => (E,u.val)) ⁻¹' A.energyRootDomain (c:ℂ)
  let V := (fun E : ℂ => (E,v.val)) ⁻¹' B.energyRootDomain (d:ℂ)
  have hU : IsOpen U := (A.energyRootDomain_open (c:ℂ)).preimage
    (continuous_id.prodMk continuous_const)
  have hV : IsOpen V := (B.energyRootDomain_open (d:ℂ)).preimage
    (continuous_id.prodMk continuous_const)
  have hF : ContinuousOn (hillHminusMiuraRoot u.val (c:ℂ)) U := by
    have hc : ContinuousOn (fun t : ℂ × Coeff 2 => hillHminusMiuraRoot t.2 (c:ℂ) t.1)
        (A.energyRootDomain (c:ℂ)) := (A.analytic_energyRoot (c:ℂ)).continuousOn
    exact hc.comp' (f := fun E : ℂ => (E,u.val)) (continuous_id.prodMk continuous_const).continuousOn
      (Set.mapsTo_preimage _ _)
  have hG : ContinuousOn (hillHminusMiuraRoot v.val (d:ℂ)) V := by
    have hc : ContinuousOn (fun t : ℂ × Coeff 2 => hillHminusMiuraRoot t.2 (d:ℂ) t.1)
        (B.energyRootDomain (d:ℂ)) := (B.analytic_energyRoot (d:ℂ)).continuousOn
    exact hc.comp' (f := fun E : ℂ => (E,v.val)) (continuous_id.prodMk continuous_const).continuousOn
      (Set.mapsTo_preimage _ _)
  apply continuous_eqOn_of_dense_on_open {E : ℂ | E.im ≠ 0} (U ∩ V) dense_complex_nonreal
    (hU.inter hV) _ _ (hF.mono inter_subset_left) (hG.mono inter_subset_right)
  intro E hE
  exact (hillHminusMiuraRoot_eq_physical_of_real u q c hu E hE.2).trans
    (hillHminusMiuraRoot_eq_physical_of_real v q d hv E hE.2).symm

end NLS.KdV
