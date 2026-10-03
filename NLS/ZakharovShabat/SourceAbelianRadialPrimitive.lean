import NLS.ZakharovShabat.SourceAbelianJointProperties
import NLS.ComplexAnalysis.ParametricSourceLogDomain
import NLS.ComplexAnalysis.ContinuousLogarithmUnique

/-! # Abelian continuation along straight source paths

Continue the actual primitive at a fixed real source by integrating the
Floquet logarithmic derivative along straight source segments. This
construction is analytic on its open segment domain and keeps the exact
joint differential. Uniform spectral-exterior products can lie in this
domain without a spectral compactness assumption.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceAbelianRadialDomain (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (W : Set (CoeffPair p)) : Set (ℂ × CoeffPair p) :=
  sourceSegmentDomain φ.val (sourceCanonicalRootJointDomain hp hp1 W)

/-- Continue the actual real-source normalization through the source
variable, retaining every signed-index additive constant. -/
def sourceAbelianRadialPrimitive (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (n : ℤ) (t : ℂ × CoeffPair p) : ℂ :=
  parametricSourceLogExtension (sourceFloquetJointMultiplier hp hp1) φ.val
    (sourceAbelianPrimitive hp hp1 φ.val φ.property) t+I*(Real.pi : ℂ)*n

@[simp] theorem sourceAbelianRadialPrimitive_base (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (z : ℂ) :
    sourceAbelianRadialPrimitive hp hp1 φ n (z,φ.val) =
      sourceAbelianPrimitive hp hp1 φ.val φ.property z+I*(Real.pi : ℂ)*n := by
  simp [sourceAbelianRadialPrimitive]

theorem sourceAbelianRadialPrimitive_analytic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) : AnalyticOnNhd ℂ (sourceAbelianRadialPrimitive hp hp1 φ n) (sourceAbelianRadialDomain hp hp1 φ W) := by
  apply (analyticOnNhd_parametricSourceLogExtension _ _ _ _ hD hM
    (fun t ht => sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2) ?_).add analyticOnNhd_const
  intro z hz
  exact sourceAbelianPrimitive_analytic hp hp1 φ.val φ.property z
    (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hz.2)

theorem sourceAbelianRadialPrimitive_exp (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianRadialDomain hp hp1 φ W) :
    exp (sourceAbelianRadialPrimitive hp hp1 φ n t) = exp (I*(Real.pi : ℂ)*n)*sourceFloquetJointMultiplier hp hp1 t := by
  rw [sourceAbelianRadialPrimitive,exp_add,mul_comm]
  congr 1
  exact exp_parametricSourceLogExtension _ _ _ _ hM
    (fun t ht => sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2)
    (fun z hz => sourceAbelianPrimitive_exp hp hp1 φ.val φ.property z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hz.2)) t ht

/-- Source transport gives the exact joint discriminant differential,
not only a source-direction derivative or a spectral primitive. -/
theorem sourceAbelianRadialPrimitive_hasFDerivAt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (W : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceAbelianRadialDomain hp hp1 φ W) :
    HasFDerivAt (sourceAbelianRadialPrimitive hp hp1 φ n)
      ((sourceCanonicalRoot hp hp1 t.2 t.1)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) t) t := by
  have hM := sourceFloquetJointMultiplier_analyticOnNhd hp hp1 W hroot
  have hF := hasFDerivAt_parametricSourceLogExtension (sourceFloquetJointMultiplier hp hp1) φ.val
    (sourceAbelianPrimitive hp hp1 φ.val φ.property) _ hD hM
    (fun t ht => sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 ht.2)
    (fun z hz => sourceAbelianPrimitive_analytic hp hp1 φ.val φ.property z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hz.2))
    (fun z hz => sourceAbelianPrimitive_exp hp hp1 φ.val φ.property z
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 φ.val hz.2)) t ht
  have htD := sourceSegmentDomain_end φ.val (sourceCanonicalRootJointDomain hp hp1 W) ht
  have hne : sourceFloquetJointMultiplier hp hp1 t ≠ 0 := sourceFloquetMultiplier_ne_zero hp hp1 t.2 t.1 htD.2
  have hlog : sourceFloquetJointMultiplier hp hp1 t/sourceFloquetJointMultiplier hp hp1 t ∈ slitPlane := by
    rw [div_self hne]
    simp
  have hlocal := normalizedLogChart_hasFDerivAt (sourceFloquetJointMultiplier hp hp1) t t 0 hne
    (hM t htD).differentiableAt hlog
  have hlocal' := normalizedLogChart_sourceFloquet_hasFDerivAt hp hp1 W hD hroot t t 0 htD htD hlog
  rw [hlocal.unique hlocal'] at hF
  exact hF.add_const (I*(Real.pi : ℂ)*n)

/-- On a convex neighborhood of real sources, continuation retains
the actual primitive at every real source, not just at its anchor. -/
theorem sourceAbelianRadialPrimitive_eq_real_on_convex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (W V : Set (CoeffPair p))
    (hD : IsOpen (sourceCanonicalRootJointDomain hp hp1 W))
    (hM : AnalyticOnNhd ℂ (sourceFloquetJointMultiplier hp hp1) (sourceCanonicalRootJointDomain hp hp1 W))
    (hcV : Convex ℝ V) (hφV : φ.val ∈ V) (z : ℂ)
    (hV : ∀ ψ ∈ V, (z,ψ) ∈ sourceAbelianRadialDomain hp hp1 φ W)
    (n : ℤ) (ψ : realTypeSourceSubmodule p) (hψ : ψ.val ∈ V) :
    sourceAbelianRadialPrimitive hp hp1 φ n (z,ψ.val) =
      sourceAbelianPrimitive hp hp1 ψ.val ψ.property z+I*(Real.pi : ℂ)*n := by
  let S : Set (realTypeSourceSubmodule p) := {χ | χ.val ∈ V}
  have hS : Convex ℝ S := hcV.linear_preimage (realTypeSourceSubmodule p).subtype
  let F : realTypeSourceSubmodule p → ℂ := fun χ => sourceAbelianRadialPrimitive hp hp1 φ n (z,χ.val)
  let G : realTypeSourceSubmodule p → ℂ := fun χ => sourceAbelianPrimitive hp hp1 χ.val χ.property z+I*(Real.pi : ℂ)*n
  have hroot (χ : realTypeSourceSubmodule p) (hχ : χ ∈ S) : z ∈ sourceCanonicalRootDomain hp hp1 χ.val :=
    (sourceSegmentDomain_end φ.val (sourceCanonicalRootJointDomain hp hp1 W) (hV χ.val hχ)).2
  have hF : ContinuousOn F S := by
    intro χ hχ
    have hm : Continuous (fun χ : realTypeSourceSubmodule p => (z,χ.val)) := continuous_const.prodMk continuous_subtype_val
    exact (((sourceAbelianRadialPrimitive_analytic hp hp1 φ W hD hM n (z,χ.val) (hV χ.val hχ)).continuousAt.comp
      (f := fun χ : realTypeSourceSubmodule p => (z,χ.val)) (hm.continuousAt (x := χ)))).continuousWithinAt
  have hG : ContinuousOn G S := fun χ hχ =>
    ((continuousAt_sourceAbelianPrimitive_source hp hp1 χ z (hroot χ hχ)).add continuousAt_const).continuousWithinAt
  apply continuousLogarithms_eqOn F G S hS.isPreconnected hF hG ?_ φ hφV ?_ hψ
  · intro χ hχ
    change exp (sourceAbelianRadialPrimitive hp hp1 φ n (z,χ.val)) = exp (sourceAbelianPrimitive hp hp1 χ.val χ.property z+I*(Real.pi : ℂ)*n)
    rw [sourceAbelianRadialPrimitive_exp hp hp1 φ W hM n (z,χ.val) (hV χ.val hχ),exp_add,
      sourceAbelianPrimitive_exp hp hp1 χ.val χ.property z
        (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 χ.val (hroot χ hχ))]
    exact mul_comm _ _
  · exact sourceAbelianRadialPrimitive_base hp hp1 φ n z

/-- Restricting the continuation's joint differential to potential
directions gives the gradient required in Lemma 19.1(i). -/
theorem sourceAbelianRadialPrimitive_source_fderiv (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (z : ℂ) (ψ h : CoeffPair p)
    (hjoint : HasFDerivAt (sourceAbelianRadialPrimitive hp hp1 φ n)
      ((sourceCanonicalRoot hp hp1 ψ z)⁻¹ •
        fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1) (z,ψ)) (z,ψ)) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceAbelianRadialPrimitive hp hp1 φ n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

end NLS.ZakharovShabat
