import NLS.KdV.HillHminusOneDirichlet
import NLS.KdV.HminusOneMiuraTrace

/-! The complete rough Miura and constant-energy identities for the original
H-minus-one Dirichlet characteristic, proved in the full source norms. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat NLS.MKdV

theorem continuous_hillHminusDirichlet_potential (lambda : ℂ) :
    Continuous (fun q : PeriodOneHminusOne => hillHminusDirichlet q lambda) := by
  have hd := analyticOnNhd_hillHminusDirichlet_joint.continuous
  have hm : Continuous (fun q : PeriodOneHminusOne => (lambda,q)) := continuous_const.prodMk continuous_id
  exact Continuous.comp (g := fun t : ℂ × PeriodOneHminusOne => hillHminusDirichlet t.2 t.1)
    (f := fun q : PeriodOneHminusOne => (lambda,q)) hd hm

/-- The full rough Miura image has the independently verified fixed Dirac energy Dirichlet characteristic. -/
theorem hillHminusDirichlet_miura (u : Coeff 2) (lambda : ℂ) :
    hillHminusDirichlet (periodOneMiura u) lambda = quasiHillL2Dirichlet u lambda := by
  have hleft : Continuous (fun a : Coeff 2 => hillHminusDirichlet (periodOneMiura a) lambda) :=
    (continuous_hillHminusDirichlet_potential lambda).comp continuous_periodOneMiura
  have hright : Continuous (fun a : Coeff 2 => quasiHillL2Dirichlet a lambda) := by
    have hm : Continuous (fun a : Coeff 2 => (lambda,a)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (g := fun t : ℂ × Coeff 2 => quasiHillL2Dirichlet t.2 t.1)
      (f := fun a : Coeff 2 => (lambda,a)) analyticOnNhd_quasiHillL2Dirichlet_joint.continuous hm
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer hleft hright (by
    funext a
    change hillHminusDirichlet (periodOneMiura (scalarInclusion a)) lambda =
      quasiHillL2Dirichlet (scalarInclusion a) lambda
    have hi := periodOneMiura_scalarInclusion a
    calc
      _ = hillL2Dirichlet (Coeff.periodDouble (sobolevMiuraUnitPotential a)) lambda := by
        rw [hi,hillHminusDirichlet_eq_hillL2]
      _ = _ := (quasiHillL2Dirichlet_eq_hillL2 (scalarInclusion a)
        (sobolevMiuraUnitPotential a) hi lambda).symm)
  exact congrFun he u

/-- Adding the same constant to the potential and energy preserves the full rough physical Dirichlet characteristic. -/
theorem hillHminusDirichlet_add_const (q : PeriodOneHminusOne) (c lambda : ℂ) :
    hillHminusDirichlet (q+periodOneL2Inclusion (lp.single 2 0 c)) (lambda+c) =
      hillHminusDirichlet q lambda := by
  have hleft : Continuous (fun a : PeriodOneHminusOne =>
      hillHminusDirichlet (a+periodOneL2Inclusion (lp.single 2 0 c)) (lambda+c)) :=
    (continuous_hillHminusDirichlet_potential (lambda+c)).comp
      (continuous_id.add continuous_const)
  have he := denseRange_periodOneL2Inclusion.equalizer hleft
    (continuous_hillHminusDirichlet_potential lambda) (by
      funext a
      change hillHminusDirichlet (periodOneL2Inclusion a+periodOneL2Inclusion (lp.single 2 0 c))
        (lambda+c) = hillHminusDirichlet (periodOneL2Inclusion a) lambda
      rw [← map_add,hillHminusDirichlet_eq_hillL2,hillHminusDirichlet_eq_hillL2,
        map_add,periodDouble_single_zero,hillL2Dirichlet_add_const])
  exact congrFun he q

/-- A literal shifted Miura representation gives an exact identity of Dirichlet characteristics,
not just equality of their spectral zero sets. -/
theorem hillHminusDirichlet_eq_miura_of_shifted_image (q : PeriodOneHminusOne)
    (u : Coeff 2) (c lambda : ℂ)
    (h : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDirichlet q lambda = quasiHillL2Dirichlet u (lambda+c) := by
  rw [← hillHminusDirichlet_miura,h,hillHminusDirichlet_add_const]


end NLS.KdV
