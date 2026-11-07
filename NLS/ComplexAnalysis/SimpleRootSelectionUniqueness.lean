import NLS.ComplexAnalysis.BanachC1ImplicitRoot

/-! Simple-root uniqueness for continuously parameterized selections.
The equation has a complex Banach parameter, while the selection may
be defined on ANY topological space, such as the physical real form. -/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem scalar_partial_bijective_of_nonzero (A : (ℂ × E) →L[ℂ] ℂ) (hA : A (1,0) ≠ 0) :
    Function.Bijective (A.comp (ContinuousLinearMap.inl ℂ ℂ E)) := by
  have he (z : ℂ) : A (z,0) = z*A (1,0) := by
    have hvec : (z,(0:E)) = z • (1,(0:E)) := by ext <;> simp
    rw [hvec,map_smul,smul_eq_mul]
  constructor
  · intro z w h
    change A (z,0) = A (w,0) at h
    rw [he z,he w] at h
    exact mul_right_cancel₀ hA h
  · intro z
    refine ⟨z/A (1,0),?_⟩
    change A (z/A (1,0),0) = z
    rw [he,div_mul_cancel₀ _ hA]

theorem eventually_eq_of_continuous_simple_root_selections
    {X : Type*} [TopologicalSpace X]
    (F : ℂ × E → ℂ) (p : X → E) (a b : X → ℂ) (x : X)
    (hF : AnalyticAt ℂ F (a x,p x)) (hp : ContinuousAt p x)
    (ha : ContinuousAt a x) (hb : ContinuousAt b x) (heq : a x = b x)
    (hza : ∀ᶠ y in 𝓝 x, F (a y,p y) = 0)
    (hzb : ∀ᶠ y in 𝓝 x, F (b y,p y) = 0)
    (hd : (fderiv ℂ F (a x,p x)) (1,0) ≠ 0) : a =ᶠ[𝓝 x] b := by
  obtain ⟨s,V,hV,hpoint,_,_,hunique,_⟩ := exists_C1_implicitBanachRoot_unique
    F (a x) (p x) hF.contDiffAt hza.self_of_nhds
    (scalar_partial_bijective_of_nonzero _ hd)
  have hpointb : (b x,p x) ∈ V := by rw [← heq]; exact hpoint
  have hma := (ha.prodMk hp).eventually (hV.mem_nhds hpoint)
  have hmb := (hb.prodMk hp).eventually (hV.mem_nhds hpointb)
  filter_upwards [hma,hmb,hza,hzb] with y hay hby hfa hfb
  exact (hunique (a y) (p y) hay hfa).trans (hunique (b y) (p y) hby hfb).symm

end NLS.ComplexAnalysis
