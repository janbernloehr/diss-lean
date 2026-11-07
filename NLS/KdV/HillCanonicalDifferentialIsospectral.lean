import NLS.KdV.HillCanonicalPsiIsospectral
import NLS.KdV.HillCanonicalEnergyRootIsospectral
import NLS.KdV.HillCanonicalEnergyDifferentials

/-! The actual normalized energy differential is stationary along
every action Hamiltonian direction throughout its original joint
energy/source sheet domain. This retains the canonical numerator and
the actual nonzero physical sheet, with no gap or action division. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.KdV

theorem hillHminusCanonicalEnergyRootDomain_subset_psiSource :
    hillHminusCanonicalEnergyRootDomain ⊆ univ ×ˢ hillHminusCanonicalPsiDomain := by
  intro t ht
  exact ⟨mem_univ _,hillHminusCanonicalZeroSequenceDomain_subset_psiDomain
    (hillHminusSimpleZeroSequenceDomain_subset_zeroDomain
      (hillHminusCanonicalEnergyRootDomain_subset_simpleSource ht).2)⟩

theorem fderiv_hillHminusCanonicalEnergyDifferential_eq_zero_of_stationary
    (n : ℕ+) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain) (h : PeriodOneHminusOne)
    (hpsi : (fderiv ℂ (fun a => hillHminusCanonicalPsi n (E,a)) q) h = 0)
    (hroot : (fderiv ℂ (fun a => hillHminusCanonicalEnergyRoot (E,a)) q) h = 0) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyDifferential n (E,a)) q) h = 0 := by
  let N : PeriodOneHminusOne → ℂ := fun a => hillHminusCanonicalPsi n (E,a)
  let R : PeriodOneHminusOne → ℂ := fun a => hillHminusCanonicalEnergyRoot (E,a)
  let Q : ℂ × ℂ → ℂ := fun t => t.1/t.2
  have hn : DifferentiableAt ℂ N q :=
    ((analyticOnNhd_hillHminusCanonicalPsi n (E,q)
      (hillHminusCanonicalEnergyRootDomain_subset_psiSource hq)).comp
        (f := fun a : PeriodOneHminusOne => (E,a))
        (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hr : DifferentiableAt ℂ R q :=
    ((analyticOnNhd_hillHminusCanonicalEnergyRoot (E,q) hq).comp
      (f := fun a : PeriodOneHminusOne => (E,a))
      (analyticAt_const.prod analyticAt_id)).differentiableAt
  have hQ : DifferentiableAt ℂ Q (N q,R q) :=
    (analyticAt_fst.div analyticAt_snd (hillHminusCanonicalEnergyRoot_ne_zero (E,q) hq)).differentiableAt
  have hc := (hQ.hasFDerivAt.comp q (hn.hasFDerivAt.prodMk hr.hasFDerivAt)).fderiv
  have heval := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hc
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    hpsi,hroot,Prod.mk_zero_zero,map_zero,N,R,Q,hillHminusCanonicalEnergyDifferential] using heval

theorem fderiv_hillHminusCanonicalEnergyDifferential_isospectral_eq_zero_of_real
    (n : ℕ+) (E : ℂ) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain) (h : PeriodOneHminusOne)
    (hiso : ∀ e : ℂ, hillHminusDiscriminantCotangent e q h = 0) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyDifferential n (E,a)) q) h = 0 :=
  fderiv_hillHminusCanonicalEnergyDifferential_eq_zero_of_stationary n E q hq h
    (fderiv_hillHminusCanonicalPsi_isospectral_eq_zero_of_real n q hr h hiso E)
    (fderiv_hillHminusCanonicalEnergyRoot_isospectral_eq_zero E q hq h (hiso E))

theorem hillHminusCanonicalEnergyDifferential_action_Hamiltonian_direction
    (n m : ℕ+) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain) :
    (fderiv ℂ (fun a => hillHminusCanonicalEnergyDifferential n (E,a)) q)
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m) q) = 0 := by
  have hp := (hillHminusCanonicalEnergyRootDomain_subset_psiSource hq).2
  exact fderiv_hillHminusCanonicalEnergyDifferential_eq_zero_of_stationary n E q hq _
    (hillHminusCanonicalPsi_action_Hamiltonian_direction n m E q hp)
    (hillHminusCanonicalEnergyRoot_action_Hamiltonian_direction E m q hq
      (hillHminusCanonicalPsiDomain_subset_actionDomain hp))

theorem hillHminusCanonicalEnergyDifferential_action_Gardner_commute
    (n m : ℕ+) (E : ℂ) (q : PeriodOneHminusOne)
    (hq : (E,q) ∈ hillHminusCanonicalEnergyRootDomain) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalEnergyDifferential n (E,a))
      (hillHminusCanonicalAction m) q = 0 := by
  rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusCanonicalEnergyDifferential_action_Hamiltonian_direction n m E q hq

end NLS.KdV
