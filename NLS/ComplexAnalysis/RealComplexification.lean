import NLS.ComplexAnalysis.ContinuousRealFormIdentity

/-! # Continuous coordinates for an arbitrary real complexification

The real-linear homeomorphism (x,y) ↦ x+i*y records the complexification
without fixing a norm. Its inverse gives continuous real and imaginary
projections; they need not be contractions or have prescribed bounds.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

variable (R E : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

/-- A topological complexification of a real normed space, in continuous real coordinates. -/
structure RealComplexification where
  equiv : (R × R) ≃L[ℝ] E
  map_imaginary : ∀ x : R, equiv (0,x) = Complex.I • equiv (x,0)

namespace RealComplexification
variable {R E}

/-- The included real subspace of the complexification. -/
def realLocus (c : RealComplexification R E) : Set E := Set.range (fun x : R => c.equiv (x,0))

/-- The real part viewed as an element of the complexification. -/
def re (c : RealComplexification R E) (v : E) : E := c.equiv ((c.equiv.symm v).1,0)

/-- The imaginary part viewed as an element of the real subspace. -/
def im (c : RealComplexification R E) (v : E) : E := c.equiv ((c.equiv.symm v).2,0)

theorem re_mem (c : RealComplexification R E) (v : E) : c.re v ∈ c.realLocus := ⟨_,rfl⟩
theorem im_mem (c : RealComplexification R E) (v : E) : c.im v ∈ c.realLocus := ⟨_,rfl⟩

theorem decomp (c : RealComplexification R E) (v : E) : v = c.re v + Complex.I • c.im v := by
  rw [re,im,← c.map_imaginary,← map_add]
  simp

theorem continuous_re (c : RealComplexification R E) : Continuous c.re := by
  unfold re
  fun_prop

theorem continuous_im (c : RealComplexification R E) : Continuous c.im := by
  unfold im
  fun_prop

@[simp] theorem re_zero (c : RealComplexification R E) : c.re 0 = 0 := by simp [re]
@[simp] theorem im_zero (c : RealComplexification R E) : c.im 0 = 0 := by simp [im]

theorem add_mem (c : RealComplexification R E) {x y : E}
    (hx : x ∈ c.realLocus) (hy : y ∈ c.realLocus) : x+y ∈ c.realLocus := by
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  refine ⟨u+v,?_⟩
  simpa only [Prod.mk_add_mk,add_zero] using c.equiv.map_add (u,0) (v,0)

variable [IsScalarTower ℝ ℂ E] in
theorem real_smul_mem (c : RealComplexification R E) (t : ℝ) {x : E}
    (hx : x ∈ c.realLocus) : (t:ℂ) • x ∈ c.realLocus := by
  obtain ⟨u,rfl⟩ := hx
  refine ⟨t • u,?_⟩
  have ht (v : E) : (t:ℂ) • v = t • v := IsScalarTower.algebraMap_smul ℂ t v
  rw [ht]
  simpa only [Prod.smul_mk,smul_zero] using c.equiv.map_smul t (u,0)

end RealComplexification

/-- The usual scalar complexification of the real line. -/
def scalarRealComplexification : RealComplexification ℝ ℂ where
  equiv := Complex.equivRealProdCLM.symm
  map_imaginary x := by
    simp only [Complex.equivRealProdCLM_symm_apply,ofReal_zero,zero_add,zero_mul,add_zero,
      smul_eq_mul]
    ring

theorem scalarRealComplexification_realLocus : scalarRealComplexification.realLocus = {z : ℂ | z.im = 0} := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    simp [scalarRealComplexification,Complex.equivRealProdCLM_symm_apply]
  · intro hz
    refine ⟨z.re,?_⟩
    simp only [scalarRealComplexification,Complex.equivRealProdCLM_symm_apply,ofReal_zero,zero_mul,add_zero]
    exact Complex.ext (by simp) (by simpa using hz.symm)

end NLS.ComplexAnalysis
