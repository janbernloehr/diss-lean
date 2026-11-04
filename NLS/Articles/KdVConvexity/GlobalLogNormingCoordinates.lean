import NLS.Articles.KdVConvexity.LogNormingSequenceCoordinates
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! # Global analytic ell2 extensions of the actual logarithmic norming constants

The actual real norming data identify local Banach maps on real overlaps.
Real-form uniqueness glues them on one complex neighborhood of the whole
real H^-1 space. No spectral inverse is assumed or concluded.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem exists_global_analytic_Dirichlet_log_norming :
    ∃ Ω : Set PeriodOneHminusOne, ∃ K : PeriodOneHminusOne → Coeff 2,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ K Ω ∧
      (∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
        K p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ)) ∧ K 0 = 0 := by
  classical
  choose V F hV hqV hF hrec using fun q : PeriodOneRealHminusOne =>
    exists_local_analytic_Dirichlet_log_norming q.val q.property
  choose r hr hball using fun q : PeriodOneRealHminusOne =>
    Metric.mem_nhds_iff.mp ((hV q).mem_nhds (hqV q))
  obtain ⟨K,hK,hloc,_⟩ := exists_analyticOnNhd_gluing_realHminus
    (fun q : PeriodOneRealHminusOne => q) r F (fun q => (hF q).mono (hball q)) (by
      intro i j p hp hpr
      ext k
      have hi := hrec i p (hball i hp.1) hpr (actionIndexEquiv k)
      have hj := hrec j p (hball j hp.2) hpr (actionIndexEquiv k)
      simp only [Equiv.symm_apply_apply] at hi hj
      exact hi.trans hj.symm)
  let Ω : Set PeriodOneHminusOne := ⋃ q : PeriodOneRealHminusOne, ball q.val (r q)
  have hreal (p : PeriodOneHminusOne) (hp : IsRealPeriodOneHminusOne p) : p ∈ Ω :=
    mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (hr ⟨p,hp⟩)⟩
  have hrecovery (p : PeriodOneHminusOne) (hp : IsRealPeriodOneHminusOne p) (n : ℕ+) :
      K p (actionIndexEquiv.symm n) = (hillHminusDirichletLogNorming p hp n : ℂ) := by
    rw [hloc ⟨p,hp⟩ (mem_ball_self (hr ⟨p,hp⟩))]
    exact hrec ⟨p,hp⟩ p (hqV ⟨p,hp⟩) hp n
  refine ⟨Ω,K,isOpen_iUnion (fun _ => isOpen_ball),hreal,hK,hrecovery,?_⟩
  have hr0 : IsRealPeriodOneHminusOne 0 := by intro k; simp
  ext k
  have he := hrecovery 0 hr0 (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply,hillHminusDirichletLogNorming_zero_potential,ofReal_zero] at he
  exact he

end NLS.Articles.KdVConvexity
