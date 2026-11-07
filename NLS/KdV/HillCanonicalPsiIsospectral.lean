import NLS.KdV.HillMiuraIsospectralDirection
import NLS.KdV.HminusOneCanonicalHillPsi
import NLS.ZakharovShabat.SourcePsiAnalyticIsospectral

/-! The actual intrinsic Hill numerators are stationary in native
isospectral directions at every real source. Their Gardner brackets
with the actual actions vanish on the entire unchanged complex psi
domain, including collapsed gaps and the filled shifted zero energy. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem HillHminusDirichletBall.fderiv_psiNumerator_isospectral_eq_zero
    (B : HillHminusDirichletBall) (A : MiuraHillPsiFamily) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.psiSource A)
    (hr : IsRealPeriodOneHminusOne q) (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) (E : ℂ) :
    (fderiv ℂ (fun a => B.psiNumerator A n (E,a)) q) h = 0 := by
  let M := B.miuraBall.actionBall
  let φ : realTypeSourceLocus 2 := ⟨M.diracSource q,M.diracSource_real q hq.1 hr⟩
  let F : CoeffPair 2 → ℂ := fun ψ =>
    sourcePsiEnergyNumerator A.roots ((n:ℕ):ℤ) (E+(M.shift:ℂ),ψ)
  have hF : AnalyticAt ℂ F φ.val :=
    (A.verified.analytic_energyNumerator A.domain_open ((n:ℕ):ℤ)
      (E+(M.shift:ℂ),φ.val) ⟨mem_univ _,hq.2⟩).comp
        (f := fun ψ : CoeffPair 2 => (E+(M.shift:ℂ),ψ))
        (analyticAt_const.prod analyticAt_id)
  have hc := (hF.differentiableAt.hasFDerivAt.comp q
    (M.analytic_diracSource q hq.1).differentiableAt.hasFDerivAt).fderiv
  have hz := A.verified.fderiv_energyNumerator_isospectral_eq_zero ((n:ℕ):ℤ)
    φ hq.2 ((fderiv ℂ M.diracSource q) h)
    (M.fderiv_diracSource_isospectral q hq.1 h hiso) (E+(M.shift:ℂ))
  have heval := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hc
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,F,M,
    HillHminusDirichletBall.psiNumerator,MiuraHillPsiFamily.numerator,
    HillHminusMiuraActionBall.diracSource] using heval.trans hz

theorem fderiv_hillHminusCanonicalPsi_isospectral_eq_zero_of_real
    (n : ℕ+) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) (E : ℂ) :
    (fderiv ℂ (fun a => hillHminusCanonicalPsi n (E,a)) q) h = 0 := by
  obtain ⟨B,hq,_,heq⟩ := exists_hillHminusCanonicalPsi_local_presentation q
    (real_mem_hillHminusCanonicalPsiDomain q hr)
  have he : (fun a => hillHminusCanonicalPsi n (E,a)) =ᶠ[𝓝 q]
      (fun a => B.numerator n (E,a)) := by
    filter_upwards [B.source_open.mem_nhds hq] with a ha
    exact heq n E ha
  rw [he.fderiv_eq]
  exact B.parent.fderiv_psiNumerator_isospectral_eq_zero B.family n q (B.subset hq) hr h hiso E

theorem hillHminusCanonicalPsiDomain_subset_actionDomain :
    hillHminusCanonicalPsiDomain ⊆ hillHminusCanonicalActionDomain :=
  hillHminusCanonicalPsiDomain_subset_dirichletDomain.trans
    (hillHminusCanonicalDirichletDomain_subset.trans
      (hillHminusCanonicalRatioDomain_subset.trans
        (hillHminusCanonicalGapDomain_subset.trans hillHminusNormalizedCanonicalActionDomain_subset)))

theorem hillHminusCanonicalPsi_action_Gardner_commute_of_real
    (n m : ℕ+) (E : ℂ) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalPsi n (E,a))
      (hillHminusCanonicalAction m) q = 0 := by
  rw [← NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact fderiv_hillHminusCanonicalPsi_isospectral_eq_zero_of_real n q hr _
    (fun e => hillHminusDiscriminant_action_Hamiltonian_direction e m q
      (real_mem_hillHminusCanonicalActionDomain q hr)) E

theorem hillHminusCanonicalPsi_action_Gardner_commute
    (n m : ℕ+) (E : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalPsiDomain) :
    NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalPsi n (E,a))
      (hillHminusCanonicalAction m) q = 0 := by
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpsi : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalPsi n (E,a))
      hillHminusCanonicalPsiDomain := by
    intro a ha
    exact (analyticOnNhd_hillHminusCanonicalPsi n (E,a) ⟨mem_univ _,ha⟩).comp
      (f := fun b : PeriodOneHminusOne => (E,b)) (analyticAt_const.prod analyticAt_id)
  have he := analytic_eqOn_of_real_periodOneHminus hillHminusCanonicalPsiDomain
    isOpen_hillHminusCanonicalPsiDomain isConnected_hillHminusCanonicalPsiDomain.isPreconnected
    ⟨0,real_mem_hillHminusCanonicalPsiDomain 0 hzero,hzero⟩
    (NLS.Poisson.hminusGardnerBracket (fun a => hillHminusCanonicalPsi n (E,a))
      (hillHminusCanonicalAction m)) (fun _ => 0)
    (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _ hpsi
      ((analyticOnNhd_hillHminusCanonicalAction m).mono
        hillHminusCanonicalPsiDomain_subset_actionDomain))
    analyticOnNhd_const
    (fun a _ hr => hillHminusCanonicalPsi_action_Gardner_commute_of_real n m E a hr)
  exact he hq

theorem hillHminusCanonicalPsi_action_Hamiltonian_direction
    (n m : ℕ+) (E : ℂ) (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalPsiDomain) :
    (fderiv ℂ (fun a => hillHminusCanonicalPsi n (E,a)) q)
      (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction m) q) = 0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  exact hillHminusCanonicalPsi_action_Gardner_commute n m E q hq

end NLS.KdV
