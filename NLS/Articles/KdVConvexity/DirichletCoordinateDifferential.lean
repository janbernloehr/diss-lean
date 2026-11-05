import NLS.Articles.KdVConvexity.GlobalDirichletCoordinates
import NLS.KdV.HillHminusOneDirichletDifferential

/-! # Exact differentials of the global normalized Hilbert Dirichlet coordinates

The derivative is the actual H^-1 potential pairing with the squared
normalized eigenfunction, divided by its nonzero unconjugated mass and
the original coordinate weight 1+n. The result applies to the proved
Banach-valued global map and includes every positive index.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem normalizedDirichletCoordinate_fderiv
    (Ω : Set PeriodOneHminusOne) (E : PeriodOneHminusOne → Coeff 2)
    (hΩ : IsOpen Ω) (hE : AnalyticOnNhd ℂ E Ω)
    (hroot : ∀ p ∈ Ω, ∀ n : ℕ+, hillHminusDirichlet p
      ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0)
    (q : PeriodOneHminusOne) (hq : q ∈ Ω) (hr : IsRealPeriodOneHminusOne q) (n : ℕ+)
    (hEq : E q (actionIndexEquiv.symm n) =
      ((hillHminusDirichletEnergy q hr n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ))
    (h : PeriodOneHminusOne) :
    (fderiv ℂ E q h) (actionIndexEquiv.symm n) =
      hillHminusWeakPotential h
        (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))
        (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))/
      ((1+(n : ℕ) : ℂ)*(∫ s in (0 : ℝ)..1,
        extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s*
        extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s)) := by
  let c : ℂ := 1+(n : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (by positivity : (1+(n : ℕ) : ℝ) ≠ 0)
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (actionIndexEquiv.symm n)
  have hev (z : Coeff 2) : ev z = z (actionIndexEquiv.symm n) := rfl
  let a : PeriodOneHminusOne → ℂ := fun p => (freeHillValue (n : ℕ) : ℂ)+c*E p (actionIndexEquiv.symm n)
  have he := ev.hasFDerivAt.comp q (hE q hq).differentiableAt.hasFDerivAt
  have hd := (hasFDerivAt_const (freeHillValue (n : ℕ) : ℂ) q).add (he.const_mul c)
  have ha : AnalyticAt ℂ a q := analyticAt_const.add
    (analyticAt_const.mul ((ev.analyticAt _).comp (hE q hq)))
  have haq : a q = (hillHminusDirichletEnergy q hr n : ℂ) := by
    dsimp only [a]
    rw [hEq,mul_div_cancel₀ _ hc,add_sub_cancel]
  have haz : hillHminusDirichlet q (a q) = 0 := hroot q hq n
  have har : ∀ᶠ p in 𝓝 q, hillHminusDirichlet p (a p) = 0 := by
    filter_upwards [hΩ.mem_nhds hq] with p hp
    exact hroot p hp n
  have hdiff := hillHminusDirichlet_branch_differential q a ha haz har h
  have hd' : HasFDerivAt a (c • ev.comp (fderiv ℂ E q)) q := by
    simpa only [a,Pi.add_def,Function.comp_def,zero_add,hev] using! hd
  have hda : fderiv ℂ a q h = c*(fderiv ℂ E q h) (actionIndexEquiv.symm n) := by
    have hh := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L h) hd'.fderiv
    simpa only [smul_apply,smul_eq_mul,ContinuousLinearMap.comp_apply,hev] using! hh
  rw [hda,haq] at hdiff
  have hm := hillHminusDirichletColumn_square_integral_ne_zero q hr
    (hillHminusDirichletEnergy q hr n) (hillHminusDirichletEnergy_zero q hr n)
  apply (eq_div_iff (mul_ne_zero hc hm)).mpr
  change (fderiv ℂ E q h) (actionIndexEquiv.symm n)*(c*_) = _
  linear_combination hdiff

theorem exists_global_analytic_normalized_Dirichlet_energies_with_fderiv :
    ∃ Ω : Set PeriodOneHminusOne, ∃ E : PeriodOneHminusOne → Coeff 2,
      IsOpen Ω ∧ {q | IsRealPeriodOneHminusOne q} ⊆ Ω ∧ AnalyticOnNhd ℂ E Ω ∧
      (∀ p ∈ Ω, ∀ n : ℕ+, hillHminusDirichlet p
        ((freeHillValue (n : ℕ) : ℂ)+(1+(n : ℕ) : ℂ)*E p (actionIndexEquiv.symm n)) = 0) ∧
      (∀ p (hp : IsRealPeriodOneHminusOne p) (n : ℕ+),
        E p (actionIndexEquiv.symm n) =
          ((hillHminusDirichletEnergy p hp n : ℂ)-(freeHillValue (n : ℕ) : ℂ))/(1+(n : ℕ) : ℂ)) ∧
      E 0 = 0 ∧ ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+) (h : PeriodOneHminusOne),
      (fderiv ℂ E q h) (actionIndexEquiv.symm n) =
        hillHminusWeakPotential h
          (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))
          (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n))/
        ((1+(n : ℕ) : ℂ)*(∫ s in (0 : ℝ)..1,
          extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s*
          extend (hillHminusDirichletColumn q (hillHminusDirichletEnergy q hr n)) s)) := by
  obtain ⟨Ω,E,hΩ,hreal,hE,hroot,hrec,hzero⟩ := exists_global_analytic_normalized_Dirichlet_energies
  exact ⟨Ω,E,hΩ,hreal,hE,hroot,hrec,hzero,fun q hr n h =>
    normalizedDirichletCoordinate_fderiv Ω E hΩ hE hroot q (hreal hr) hr n (hrec q hr n) h⟩

end NLS.Articles.KdVConvexity
