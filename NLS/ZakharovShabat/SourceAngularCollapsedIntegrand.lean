import NLS.ZakharovShabat.SourceAngularEndpointCommonDomain
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Removing a collapsed selected gap from off-diagonal angular integrands

Lemma 12.12 places every retained psi root at the midpoint when its
gap collapses. The entire numerator therefore vanishes there. Its
filled divided difference cancels the linear selected standard root,
giving an analytic extension through the collapsed endpoint.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual retained root equals the moving midpoint at a
collapsed selected gap, also at complex sources. -/
theorem root_eq_midpoint_of_collapsed_gap
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    displacedRoots (s n ψ : Coeff p) m = sourceStandardRootMidpoint hp hp1 ψ m := by
  obtain ⟨V,_,hψV,_,C,_,hoff⟩ := hs.locally_uniform_squared_gap_offsets ψ hψ
  obtain ⟨α,_,hα,_⟩ := hoff ψ hψV n
  simpa only [hgap,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul,add_zero] using hα m hmn

theorem numerator_zero_at_collapsed_midpoint
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    sourcePsiCandidate n (sourceStandardRootMidpoint hp hp1 ψ m,(s n ψ : Coeff p)) = 0 := by
  rw [← hs.root_eq_midpoint_of_collapsed_gap ψ hψ n m hmn hgap]
  exact sourcePsiCandidate_other_root hp hp1 n m hmn (s n ψ : Coeff p)

end SourcePsiSquaredGapComplexExtension

/-- The removable extension on the canonical sheet. Its value at
the selected midpoint is the filled divided-difference value. -/
def sourceAngularCollapsedIntegrand (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  -dslope (fun w => sourcePsiCandidate n (w,(s n ψ : Coeff p)))
    (sourceStandardRootMidpoint hp hp1 ψ m) z /
      (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)

/-- Filling the divided difference makes the extension analytic
throughout the selected omitted-root domain, including its midpoint. -/
theorem sourceAngularCollapsedIntegrand_analyticOnNhd
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (hdata : SourceAngularEndpointSpectralData hp hp1 ψ m) :
    AnalyticOnNhd ℂ (sourceAngularCollapsedIntegrand hp hp1 n m s ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ m) := by
  let f : ℂ → ℂ := fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hd : Differentiable ℂ (dslope f τ) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope
      (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 τ)).mpr
        (differentiable_sourcePsiCandidate hp hp1 n (s n ψ : Coeff p)).differentiableOn)
  have ha := hd.differentiableOn.analyticOnNhd isOpen_univ
  intro z hz
  exact (ha z (mem_univ _)).neg.div
    (analyticAt_const.mul (hdata.analytic_omitted z hz))
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero)
      (sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m hz))

theorem sourceAngularCollapsedIntegrand_midpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) :
    sourceAngularCollapsedIntegrand hp hp1 n m s ψ (sourceStandardRootMidpoint hp hp1 ψ m) =
      -deriv (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p)))
        (sourceStandardRootMidpoint hp hp1 ψ m) /
          (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ (sourceStandardRootMidpoint hp hp1 ψ m)) := by
  simp only [sourceAngularCollapsedIntegrand,dslope_same]

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The extension agrees with the actual off-diagonal angular
integrand wherever the canonical spectral quotient is defined. -/
theorem angular_collapsed_integrand_eq_canonical
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n m : ℤ) (hmn : m ≠ n)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    sourceAngularIntegrand n s (fun t => sourceCanonicalRoot hp hp1 t.2 t.1) (z,ψ) =
      sourceAngularCollapsedIntegrand hp hp1 n m s ψ z := by
  let f : ℂ → ℂ := fun w => sourcePsiCandidate n (w,(s n ψ : Coeff p))
  let τ := sourceStandardRootMidpoint hp hp1 ψ m
  have hzero : f τ = 0 := hs.numerator_zero_at_collapsed_midpoint ψ hψ n m hmn hgap
  have hfactor : (z-τ)*dslope f τ z = f z := by
    simpa only [smul_eq_mul,hzero,sub_zero] using sub_smul_dslope f τ z
  have hzt : z ≠ τ := by
    intro he
    apply hz m
    rw [he]
    exact sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
  have hP := sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z m (fun k _ => hz k)
  have hgap' : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m = 0 := by
    simpa only [sourcePeriodicGapDisplacement_apply] using hgap
  have hR : sourceStandardRoot hp hp1 ψ m z = τ-z :=
    sourceStandardRoot_of_zeroGap hp hp1 ψ m z hgap'
  change f z / sourceCanonicalRoot hp hp1 ψ z =
    -dslope f τ z / (2*I*sourceStandardRootOmittedProduct hp hp1 m ψ z)
  rw [sourceCanonicalRoot_eq_omitted hp hp1 m ψ z,hR,← hfactor]
  field_simp [hP,I_ne_zero,sub_ne_zero.mpr hzt,sub_ne_zero.mpr hzt.symm]
  ring

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
