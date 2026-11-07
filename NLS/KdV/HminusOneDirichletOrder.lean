import NLS.KdV.MiuraDirichletSignedSymmetry
import NLS.KdV.HminusOneDirichletAuxiliary

/-! Analytic multiplicities of the full rough Dirichlet characteristic
under the exact auxiliary Dirac identity. Squaring is locally invertible
at every nonzero frequency, and the factor z there has analytic order zero. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Every nonzero square-root frequency retains the exact actual auxiliary
operator algebraic multiplicity as scalar Dirichlet analytic order. This
holds at all complex potentials and energies, not only at simple zeros. -/
theorem analyticOrderAt_hillHminusDirichlet_shifted_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (hz : z ≠ 0) :
    analyticOrderAt (hillHminusDirichlet q) (z^2-c) =
      (BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property z : ℕ∞) := by
  let g : ℂ → ℂ := fun w => w^2-c
  have hg : AnalyticAt ℂ g z := (analyticAt_id.pow 2).sub analyticAt_const
  have hd : HasDerivAt g (2*z) z := by
    simpa [g] using! ((hasDerivAt_id z).pow 2).sub_const c
  have hdn : deriv g z ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (by norm_num) hz
  have hf : AnalyticAt ℂ (hillHminusDirichlet q) (g z) :=
    (analyticOnNhd_hillHminusDirichlet_joint (g z,q) (mem_univ _)).comp
      (f := fun w : ℂ => (w,q)) (analyticAt_id.prod analyticAt_const)
  have hc := analyticOrderAt_comp_of_deriv_ne_zero (f := hillHminusDirichlet q) hg hdn
  have hfun : auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) = fun w => w*hillHminusDirichlet q (g w) :=
    funext fun w => auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c w hi
  have ho := analyticOrderAt_auxiliaryPeriodOneCharacteristic (by simp) (by norm_num)
    .dirichlet (hillMiuraDiagonal u) z
  rw [hfun] at ho
  have hid : analyticOrderAt (fun w : ℂ => w) z = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hz)
  change analyticOrderAt ((fun w : ℂ => w)*(hillHminusDirichlet q ∘ g)) z = _ at ho
  rw [analyticOrderAt_mul (f := fun w : ℂ => w) (g := hillHminusDirichlet q ∘ g)
    analyticAt_id (hf.comp hg),hid,zero_add,hc] at ho
  exact ho

/-- The same exact auxiliary multiplicity identity in natural-order notation. -/
theorem analyticOrderNatAt_hillHminusDirichlet_shifted_miura
    (q : PeriodOneHminusOne) (u : Coeff 2) (c z : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (hz : z ≠ 0) :
    analyticOrderNatAt (hillHminusDirichlet q) (z^2-c) =
      BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
        (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property z := by
  have he := congrArg ENat.toNat
    (analyticOrderAt_hillHminusDirichlet_shifted_miura q u c z hi hz)
  simpa only [analyticOrderNatAt,ENat.toNat_natCast] using he

end NLS.KdV
