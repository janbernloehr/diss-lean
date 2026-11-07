import NLS.KdV.HillHminusOneMiuraContour
import NLS.KdV.HillDiscriminantJointCotangent

/-! The actual derivative of a locally lifted Dirac discriminant is
the native Hill source derivative at the shifted squared energy.
The equality is differentiated on a whole open source neighborhood. -/
noncomputable section
open Set Filter Topology Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_liftedMiuraDiscriminant_eq_native
    (U : Set PeriodOneHminusOne) (hU : IsOpen U)
    (u : PeriodOneHminusOne → Coeff 2) (hu : AnalyticOnNhd ℂ u U)
    (c : ℂ) (himage : ∀ a ∈ U, periodOneMiura (u a)=
      a+periodOneL2Inclusion (lp.single 2 0 c))
    (q : PeriodOneHminusOne) (hq : q ∈ U) (z : ℂ) (h : PeriodOneHminusOne) :
    (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z)
      (hillMiuraDiagonal (u q)))
      ((fderiv ℂ (fun a => hillMiuraDiagonal (u a)) q) h)=
        hillHminusDiscriminantCotangent (z^2-c) q h := by
  let v : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (u a)
  have hv : AnalyticAt ℂ v q := (hillMiuraDiagonal.analyticAt _).comp (hu q hq)
  have hD : AnalyticAt ℂ
      (fun ψ : CoeffPair 2 => canonicalDiscriminant (by simp) (periodOnePotential ψ) z) (v q) :=
    (analyticOnNhd_canonicalDiscriminant_periodOne (p := 2) (by simp) (by norm_num)
      (z,v q) (mem_univ _)).comp (f := fun ψ : CoeffPair 2 => (z,ψ))
        (analyticAt_const.prod analyticAt_id)
  have he : (fun a => canonicalDiscriminant (by simp) (periodOnePotential (v a)) z) =ᶠ[𝓝 q]
      (fun a => hillHminusDiscriminant a (z^2-c)) := by
    filter_upwards [hU.mem_nhds hq] with a ha
    exact (hillHminusDiscriminant_shifted_miura_square a (u a) c z (himage a ha)).symm
  have hc := (hD.differentiableAt.hasFDerivAt.comp q hv.differentiableAt.hasFDerivAt).fderiv
  change fderiv ℂ (fun a => canonicalDiscriminant (by simp) (periodOnePotential (v a)) z) q=_ at hc
  rw [he.fderiv_eq] at hc
  have hh := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hc
  exact hh.symm

end NLS.KdV
