import NLS.KdV.HillHminusOneDiscriminant

/-! Exact Miura-image and constant-energy translation identities for the
actual H-minus-one trace, extended in the full norms by verified density. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.ZakharovShabat NLS.MKdV

theorem continuous_periodOneMiura : Continuous periodOneMiura := by
  change Continuous (fun u : Coeff 2 => periodOneShiftedMiura 0 u-periodOneL2Inclusion u)
  exact (continuous_iff_continuousAt.mpr fun u => (analyticAt_periodOneShiftedMiura 0 u).continuousAt).sub
    periodOneL2Inclusion.continuous

theorem continuous_hillHminusDiscriminant_potential (lambda : ℂ) :
    Continuous (fun q : PeriodOneHminusOne => hillHminusDiscriminant q lambda) := by
  have hd := analyticOnNhd_hillHminusDiscriminant_joint.continuous
  have hm : Continuous (fun q : PeriodOneHminusOne => (lambda,q)) := continuous_const.prodMk continuous_id
  exact Continuous.comp (g := fun t : ℂ × PeriodOneHminusOne => hillHminusDiscriminant t.2 t.1)
    (f := fun q : PeriodOneHminusOne => (lambda,q)) hd hm

theorem periodOneMiura_scalarInclusion (a : ScalarDomain 2) :
    periodOneMiura (scalarInclusion a) = periodOneL2Inclusion (sobolevMiuraUnitPotential a) := by
  apply Subtype.ext
  funext n
  rw [periodOneMiura_apply,periodOneL2Inclusion_apply,sobolevMiuraUnitPotential_apply]
  simp only [scalarInclusion_apply]

/-- The full rough Miura image has the independently verified fixed Dirac energy trace. -/
theorem hillHminusDiscriminant_miura (u : Coeff 2) (lambda : ℂ) :
    hillHminusDiscriminant (periodOneMiura u) lambda = hillMiuraL2Discriminant u lambda := by
  have hleft : Continuous (fun a : Coeff 2 => hillHminusDiscriminant (periodOneMiura a) lambda) :=
    (continuous_hillHminusDiscriminant_potential lambda).comp continuous_periodOneMiura
  have hright : Continuous (fun a : Coeff 2 => hillMiuraL2Discriminant a lambda) := by
    have hm : Continuous (fun a : Coeff 2 => (lambda,a)) := continuous_const.prodMk continuous_id
    exact Continuous.comp (g := fun t : ℂ × Coeff 2 => hillMiuraL2Discriminant t.2 t.1)
      (f := fun a : Coeff 2 => (lambda,a)) analyticOnNhd_hillMiuraL2Discriminant_joint.continuous hm
  have he := (scalarInclusion_denseRange (p := 2) (by simp)).equalizer hleft hright (by
    funext a
    change hillHminusDiscriminant (periodOneMiura (scalarInclusion a)) lambda =
      hillMiuraL2Discriminant (scalarInclusion a) lambda
    have hi := periodOneMiura_scalarInclusion a
    calc
      _ = hillL2Discriminant (Coeff.periodDouble (sobolevMiuraUnitPotential a)) lambda := by
        rw [hi,hillHminusDiscriminant_eq_hillL2]
      _ = _ := (hillMiuraL2Discriminant_eq_hillL2 (scalarInclusion a)
        (sobolevMiuraUnitPotential a) hi lambda).symm)
  exact congrFun he u

/-- Adding the same constant to the potential and energy preserves the full rough physical trace. -/
theorem hillHminusDiscriminant_add_const (q : PeriodOneHminusOne) (c lambda : ℂ) :
    hillHminusDiscriminant (q+periodOneL2Inclusion (lp.single 2 0 c)) (lambda+c) =
      hillHminusDiscriminant q lambda := by
  have hleft : Continuous (fun a : PeriodOneHminusOne =>
      hillHminusDiscriminant (a+periodOneL2Inclusion (lp.single 2 0 c)) (lambda+c)) :=
    (continuous_hillHminusDiscriminant_potential (lambda+c)).comp
      (continuous_id.add continuous_const)
  have he := denseRange_periodOneL2Inclusion.equalizer hleft
    (continuous_hillHminusDiscriminant_potential lambda) (by
      funext a
      change hillHminusDiscriminant (periodOneL2Inclusion a+periodOneL2Inclusion (lp.single 2 0 c))
        (lambda+c) = hillHminusDiscriminant (periodOneL2Inclusion a) lambda
      rw [← map_add,hillHminusDiscriminant_eq_hillL2,hillHminusDiscriminant_eq_hillL2,
        map_add,periodDouble_single_zero,hillL2Discriminant_add_const])
  exact congrFun he q

/-- A literal shifted Miura representation gives an exact identity of traces,
not just equality of their spectral zero sets. -/
theorem hillHminusDiscriminant_eq_miura_of_shifted_image (q : PeriodOneHminusOne)
    (u : Coeff 2) (c lambda : ℂ)
    (h : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusDiscriminant q lambda = hillMiuraL2Discriminant u (lambda+c) := by
  rw [← hillHminusDiscriminant_miura,h,hillHminusDiscriminant_add_const]

end NLS.KdV
