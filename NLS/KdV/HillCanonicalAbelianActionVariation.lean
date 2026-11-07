import NLS.KdV.HillPhysicalAbelianIsospectralVariation
import NLS.KdV.HillCanonicalPhysicalAbelianValue
import NLS.KdV.HillActionDirichletContour

/-! The actual intrinsic off-index Abelian/action variation is the
actual normalized numerator times Dirichlet-divisor motion, with the
physical norming sheet retained as a factor. Real-form continuation
proves the identity on the entire original common complex domain. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem fderiv_hillHminusPhysicalOffIndexAbelianValue_isospectral_cleared_of_real
    (n m : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (h : PeriodOneHminusOne)
    (hiso : ∀ E : ℂ, hillHminusDiscriminantCotangent E q h = 0) :
    hillHminusDirichletSheet m q*((fderiv ℂ (hillHminusPhysicalOffIndexAbelianValue n m) q) h) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        ((fderiv ℂ (hillHminusCanonicalDirichlet m) q) h) := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨r,hrpos,_,heq⟩ := exists_common_canonical_physical_Abelian_patch_ball P q hq hr
  have he : hillHminusPhysicalOffIndexAbelianValue n m =ᶠ[𝓝 q] P.physicalOffIndexAbelianValue n m := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrpos)] with a ha
    exact heq n m hmn a ha
  rw [he.fderiv_eq]
  exact P.fderiv_physicalOffIndexAbelianValue_isospectral_cleared n m hmn q
    (P.real_mem_physicalDirichletSource q hq hr) hr h hiso

theorem hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared_of_real
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusDirichletSheet m q*
      NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
        (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) q := by
  have hv := fderiv_hillHminusPhysicalOffIndexAbelianValue_isospectral_cleared_of_real n m hmn q hr
    (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction k) q)
    (fun E => hillHminusDiscriminant_action_Hamiltonian_direction E k q
      (real_mem_hillHminusCanonicalActionDomain q hr))
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using hv

theorem hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    hillHminusDirichletSheet m q*
      NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
        (hillHminusCanonicalAction k) q =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) q := by
  have hd := hillHminusPhysicalAbelianDomain_subset_Dirichlet
  have hp := hillHminusPhysicalAbelianDomain_subset_Psi
  have ha := hp.trans hillHminusCanonicalPsiDomain_subset_actionDomain
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro j; simp
  have hpsi : AnalyticOnNhd ℂ (fun a => hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m a,a))
      hillHminusPhysicalAbelianDomain := by
    intro a haP
    exact (analyticOnNhd_hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m a,a)
      ⟨mem_univ _,hp haP⟩).comp
        (f := fun b : PeriodOneHminusOne => (hillHminusCanonicalDirichlet m b,b))
        ((analyticOnNhd_hillHminusCanonicalDirichlet m a (hd haP)).prod analyticAt_id)
  exact analytic_eqOn_of_real_periodOneHminus hillHminusPhysicalAbelianDomain
    isOpen_hillHminusPhysicalAbelianDomain isConnected_hillHminusPhysicalAbelianDomain.isPreconnected
    ⟨0,real_mem_hillHminusPhysicalAbelianDomain 0 hzero,hzero⟩ _ _
    (((analyticOnNhd_hillHminusDirichletSheet m).mono hd).mul
      (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
        (analyticOnNhd_hillHminusPhysicalOffIndexAbelianValue n m hmn)
        ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)))
    (hpsi.mul (NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
      ((analyticOnNhd_hillHminusCanonicalDirichlet m).mono hd)
      ((analyticOnNhd_hillHminusCanonicalAction k).mono ha)))
    (fun a _ hr => hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared_of_real n m k hmn a hr) hq

theorem hillHminusPhysicalOffIndexAbelianValue_action_Hamiltonian_cleared
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    hillHminusDirichletSheet m q*
      ((fderiv ℂ (hillHminusPhysicalOffIndexAbelianValue n m) q)
        (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction k) q)) =
      hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*
        ((fderiv ℂ (hillHminusCanonicalDirichlet m) q)
          (NLS.Poisson.gardnerHamiltonianVector (hillHminusCanonicalAction k) q)) := by
  simpa only [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector] using
    hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared n m k hmn q hq

theorem hillHminusPhysicalOffIndexAbelianValue_action_Gardner_of_sheet_ne_zero
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) (hs : hillHminusDirichletSheet m q ≠ 0) :
    NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
      (hillHminusCanonicalAction k) q =
      (hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)/hillHminusDirichletSheet m q)*
        NLS.Poisson.hminusGardnerBracket (hillHminusCanonicalDirichlet m)
          (hillHminusCanonicalAction k) q := by
  have he := hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared n m k hmn q hq
  apply mul_left_cancel₀ hs
  field_simp [hs]
  linear_combination he

theorem exists_hillHminus_offIndex_Abelian_action_bracket_contour_of_sheet_ne_zero
    (n m k : ℕ+) (hmn : m ≠ n) (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hs : hillHminusDirichletSheet m q ≠ 0) :
    ∃ u : Coeff 2, ∃ c : ℂ, periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c) ∧
      ∃ a : ℂ, ∃ R : ℝ, 0 < R ∧
        CircleIntegrable (hillMiuraActionDirichletIntegrand m q u c) a R ∧
        deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)*
          NLS.Poisson.hminusGardnerBracket (hillHminusPhysicalOffIndexAbelianValue n m)
            (hillHminusCanonicalAction k) q =
          -hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*(Real.pi:ℂ)⁻¹*
            (∮ z in C(a,R), hillMiuraActionDirichletIntegrand m q u c z) := by
  obtain ⟨u,c,himage,a,R,hR,hci,hformula⟩ :=
    exists_hillHminus_action_Dirichlet_bracket_contour q hr k m
  refine ⟨u,c,himage,a,R,hR,hci,?_⟩
  have he := hillHminusPhysicalOffIndexAbelianValue_action_Gardner_cleared_of_real n m k hmn q hr
  rw [NLS.Poisson.hminusGardnerBracket_antisymm (hillHminusCanonicalDirichlet m)
    (hillHminusCanonicalAction k) q] at he
  apply mul_left_cancel₀ hs
  linear_combination deriv (hillHminusDirichlet q) (hillHminusCanonicalDirichlet m q)*he-
    hillHminusCanonicalPsi n (hillHminusCanonicalDirichlet m q,q)*hformula

end NLS.KdV
