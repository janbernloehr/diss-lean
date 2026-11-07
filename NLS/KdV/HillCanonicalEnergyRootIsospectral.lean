import NLS.KdV.HillCanonicalEnergyRoot
import NLS.KdV.HillCanonicalActionIsospectral

/-! The actual nonzero energy sheet is stationary in every native
isospectral direction on its unchanged open joint domain. The proof
differentiates its actual square and uses nonvanishing of the sheet. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_hillHminusCanonicalEnergyRoot_isospectral_eq_zero
    (E : ℂ) (q : PeriodOneHminusOne) (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain)
    (h : PeriodOneHminusOne) (hiso : hillHminusDiscriminantCotangent E q h = 0) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyRoot (E,a)) q) h = 0 := by
  let R : PeriodOneHminusOne → ℂ := fun a => hillHminusCanonicalEnergyRoot (E,a)
  let D : PeriodOneHminusOne → ℂ := fun a => hillHminusDiscriminant a E
  have hR : DifferentiableAt ℂ R q :=
    ((analyticOnNhd_hillHminusCanonicalEnergyRoot (E,q) hq).comp
      (f := fun a : PeriodOneHminusOne => (E,a)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hD : DifferentiableAt ℂ D q :=
    (analyticOnNhd_hillHminusDiscriminant_source E q (mem_univ _)).differentiableAt
  have he : (fun a => R a * R a) =ᶠ[𝓝 q] (fun a => D a * D a - 4) := by
    have hnear := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (isOpen_hillHminusCanonicalEnergyRootDomain.mem_nhds hq)
    filter_upwards [hnear] with a ha
    simpa only [R,D,pow_two,hillHminusRadicand] using hillHminusCanonicalEnergyRoot_sq (E,a) ha
  have hc := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) he.fderiv_eq
  have hRR := hR.hasFDerivAt.mul hR.hasFDerivAt
  have hDD := (hD.hasFDerivAt.mul hD.hasFDerivAt).sub_const 4
  change HasFDerivAt (fun a => R a * R a) _ q at hRR
  change HasFDerivAt (fun a => D a * D a - 4) _ q at hDD
  rw [hRR.fderiv,hDD.fderiv] at hc
  have hd : (fderiv ℂ D q) h = 0 := hiso
  have hz : R q ≠ 0 := hillHminusCanonicalEnergyRoot_ne_zero (E,q) hq
  simp only [add_apply,smul_apply,smul_eq_mul,hd,
    mul_zero,add_zero] at hc
  have hh : (2 * R q) * ((fderiv ℂ R q) h) = 0 := by
    linear_combination hc
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (by norm_num) hz)

theorem hillHminusCanonicalEnergyRoot_action_Hamiltonian_direction
    (E : ℂ) (m : ℕ+) (q : PeriodOneHminusOne)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain)
    (ha : q ∈ hillHminusCanonicalActionDomain) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyRoot (E,a)) q)
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m) q) = 0 :=
  fderiv_hillHminusCanonicalEnergyRoot_isospectral_eq_zero E q hq _
    (hillHminusDiscriminant_action_Hamiltonian_direction E m q ha)

theorem hillHminusCanonicalEnergyRoot_action_Gardner_commute
    (E : ℂ) (m : ℕ+) (q : PeriodOneHminusOne)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain)
    (ha : q ∈ hillHminusCanonicalActionDomain) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalEnergyRoot (E,a))
      (hillHminusCanonicalAction m) q = 0 := by
  rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusCanonicalEnergyRoot_action_Hamiltonian_direction E m q hq ha

end NLS.KdV
