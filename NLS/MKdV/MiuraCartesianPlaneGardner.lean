import NLS.MKdV.MiuraCartesianGardnerBracket

/-! # The radial identity forces the canonical bracket in each open plane

Differentiating the actual Cartesian action radius and using the mixed
brackets with J gives X_n times the bracket error equal to zero. This
identity remains valid at a collapsed selected gap.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraCartesianX (m : ℕ) : Coeff 2 → ℂ :=
  miuraCartesianObservable m (ContinuousLinearMap.fst ℂ ℂ ℂ)

def miuraCartesianY (m : ℕ) : Coeff 2 → ℂ :=
  miuraCartesianObservable m (ContinuousLinearMap.snd ℂ ℂ ℂ)

def miuraCartesianPlaneBracket (m : ℕ) : ScalarDomain 2 → ℂ :=
  miuraCartesianGardnerBracketExtension m m
    (ContinuousLinearMap.fst ℂ ℂ ℂ) (ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem fderiv_miuraL2Action_cartesian_radius (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (m : ℕ) (hm : 1 ≤ m) :
    fderiv ℂ (miuraL2Action m) a =
      miuraCartesianX m a • fderiv ℂ (miuraCartesianX m) a+
        miuraCartesianY m a • fderiv ℂ (miuraCartesianY m) a := by
  obtain ⟨U,hU,haU,hA,hrad⟩ := exists_local_miuraL2CartesianCoordinates_analytic_radius a ha m hm
  have hx : AnalyticAt ℂ (miuraCartesianX m) a := analyticAt_fst.comp (hA a haU)
  have hy : AnalyticAt ℂ (miuraCartesianY m) a := analyticAt_snd.comp (hA a haU)
  have he : (fun b => miuraCartesianX m b*miuraCartesianX m b+
      miuraCartesianY m b*miuraCartesianY m b) =ᶠ[𝓝 a] (fun b => 2*miuraL2Action m b) := by
    filter_upwards [hU.mem_nhds haU] with b hb
    change (miuraL2CartesianCoordinates m b).1*(miuraL2CartesianCoordinates m b).1+
      (miuraL2CartesianCoordinates m b).2*(miuraL2CartesianCoordinates m b).2 = _
    simpa only [pow_two] using hrad b hb
  have hdL := (hx.differentiableAt.hasFDerivAt.mul hx.differentiableAt.hasFDerivAt).add
    (hy.differentiableAt.hasFDerivAt.mul hy.differentiableAt.hasFDerivAt)
  have hdR := ((analyticOnNhd_miuraL2Action m hm) a (real_mem_miuraL2ActionDomain a ha)).differentiableAt.hasFDerivAt.const_mul 2
  have hop := hdL.fderiv.symm.trans (he.fderiv_eq.trans hdR.fderiv)
  apply ContinuousLinearMap.ext
  intro h
  have hv := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hop
  change (miuraCartesianX m a*(fderiv ℂ (miuraCartesianX m) a h)+
      miuraCartesianX m a*(fderiv ℂ (miuraCartesianX m) a h))+
    (miuraCartesianY m a*(fderiv ℂ (miuraCartesianY m) a h)+
      miuraCartesianY m a*(fderiv ℂ (miuraCartesianY m) a h)) = 2*(fderiv ℂ (miuraL2Action m) a h) at hv
  change (fderiv ℂ (miuraL2Action m) a) h =
    miuraCartesianX m a*(fderiv ℂ (miuraCartesianX m) a h)+
      miuraCartesianY m a*(fderiv ℂ (miuraCartesianY m) a h)
  linear_combination -(1/2 : ℂ)*hv

theorem miuraCartesianPlaneBracket_eq_actual (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    miuraCartesianPlaneBracket m a =
      l2GardnerBracket (miuraCartesianX m) (miuraCartesianY m) (scalarInclusion a) :=
  miuraCartesianGardnerBracketExtension_eq_actual a ha m m hm _ _

theorem miuraCartesianPlaneBracket_error_mul_X (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ) (hm : 1 ≤ m) :
    miuraCartesianX m (scalarInclusion a)*(miuraCartesianPlaneBracket m a-1) = 0 := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  have hyJ : l2GardnerBracket (miuraCartesianY m) (miuraL2Action m) (scalarInclusion a) =
      -miuraCartesianX m (scalarInclusion a) := by
    have h := congrArg Prod.snd (miuraCartesianActionGardner_brackets a ha m m hm hm)
    change l2GardnerBracket (fun b => (miuraL2CartesianCoordinates m b).2) (miuraL2Action m) (scalarInclusion a) =
      -(miuraL2CartesianCoordinates m (scalarInclusion a)).1
    simpa only [ite_true] using h
  have hJY := l2GardnerBracket_antisymm_of_memlp (miuraL2Action m) (miuraCartesianY m)
    (scalarInclusion a) (miuraActionGardner_memlp a ha m hm)
      (miuraCartesianObservable_Gardner_memlp a ha m hm (ContinuousLinearMap.snd ℂ ℂ ℂ))
  rw [hyJ,neg_neg] at hJY
  have hYY : l2GardnerBracket (miuraCartesianY m) (miuraCartesianY m) (scalarInclusion a) = 0 :=
    miuraCartesianGardnerBracket_self a ha m hm (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have he := congrArg
    (fun L : Coeff 2 →L[ℂ] ℂ => L (l2GardnerDirection (miuraCartesianY m) (scalarInclusion a)))
    (fderiv_miuraL2Action_cartesian_radius (scalarInclusion a) har m hm)
  change l2GardnerBracket (miuraL2Action m) (miuraCartesianY m) (scalarInclusion a) =
    miuraCartesianX m (scalarInclusion a)*
      l2GardnerBracket (miuraCartesianX m) (miuraCartesianY m) (scalarInclusion a)+
    miuraCartesianY m (scalarInclusion a)*
      l2GardnerBracket (miuraCartesianY m) (miuraCartesianY m) (scalarInclusion a) at he
  rw [hJY,hYY,mul_zero,add_zero] at he
  rw [miuraCartesianPlaneBracket_eq_actual a ha m hm]
  linear_combination -he

end NLS.MKdV
