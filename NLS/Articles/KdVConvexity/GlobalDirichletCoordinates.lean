import NLS.Articles.KdVConvexity.DirichletSequenceCoordinates
import NLS.SequenceSpaces.PeriodOneHminusOneRealForm

/-! # Global analytic Hilbert coordinates for the normalized Dirichlet energies

The actual real labels fix the Banach-valued local maps on real overlaps.
Real-form uniqueness glues them on one complex neighborhood of all real
H^-1 inputs. Every recovered scalar branch is an actual Dirichlet zero
on that same domain. Norming coordinates and the full spectral inverse
are separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem exists_global_analytic_normalized_Dirichlet_energies :
    ∃ Ω : Set PeriodOneHminusOne, ∃ E : PeriodOneHminusOne → Coeff 2,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ E Ω ∧
      (∀ p ∈ Ω, ∀ n : ℕ+, hillHminusDirichlet p
        ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0) ∧
      (∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
        E p (actionIndexEquiv.symm n) =
          ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ)) ∧ E 0 = 0 := by
  classical
  choose V F hV hqV hF hroot hrec using fun q : PeriodOneRealHminusOne =>
    exists_local_analytic_normalized_Dirichlet_energies q.val q.property
  choose r hr hball using fun q : PeriodOneRealHminusOne =>
    Metric.mem_nhds_iff.mp ((hV q).mem_nhds (hqV q))
  obtain ⟨E,hE,hloc,_⟩ := exists_analyticOnNhd_gluing_realHminus
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
      E p (actionIndexEquiv.symm n) =
        ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ) := by
    rw [hloc ⟨p,hp⟩ (mem_ball_self (hr ⟨p,hp⟩))]
    exact hrec ⟨p,hp⟩ p (hqV ⟨p,hp⟩) hp n
  refine ⟨Ω,E,isOpen_iUnion (fun _ => isOpen_ball),hreal,hE,?_,hrecovery,?_⟩
  · intro p hp n
    obtain ⟨q,hpq⟩ := mem_iUnion.mp hp
    rw [hloc q hpq]
    exact hroot q p (hball q hpq) n
  have hr0 : IsRealPeriodOneHminusOne 0 := by intro k; simp
  ext k
  have he := hrecovery 0 hr0 (actionIndexEquiv k)
  simp only [Equiv.symm_apply_apply,hillHminusDirichletEnergy_zero_potential,sub_self,zero_div] at he
  exact he

end NLS.Articles.KdVConvexity
