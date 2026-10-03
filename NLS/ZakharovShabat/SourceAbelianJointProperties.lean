import NLS.ZakharovShabat.SourceAbelianJointPrimitive

/-! # Differential formulas and compact product neighborhoods

The glued primitive has both coordinate derivatives required in
Lemma 19.1(i). Compact spectral subsets of a real-source cut complement
admit one common complex-source ball and an open spectral neighborhood.
This compact assertion does not supply the uniform neighborhood over
the unbounded spectral exterior required by the full lemma.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The potential derivative of the actual glued complex-source
primitive is precisely `partial Delta / canonicalRoot`. -/
theorem sourceAbelianJointPrimitive_source_fderiv (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (z : ℂ) (ψ h : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianJointDomain hp hp1) :
    (fderiv ℂ (fun χ : CoeffPair p => sourceAbelianJointPrimitive hp hp1 n (z,χ)) ψ) h =
      (fderiv ℂ (fun χ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential χ) z) ψ) h /
        sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianJointPrimitive_hasFDerivAt hp hp1 n (z,ψ) ht
  rw [fderiv_source_section_eq_joint _ z ψ hjoint.differentiableAt,hjoint.fderiv,
    fderiv_source_section_eq_joint _ z ψ
      (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,smul_eq_mul,div_eq_inv_mul]

/-- The spectral derivative of the same jointly analytic function is
the actual discriminant quotient at every complex source in its domain. -/
theorem sourceAbelianJointPrimitive_spectral_deriv (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (z : ℂ) (ψ : CoeffPair p) (ht : (z,ψ) ∈ sourceAbelianJointDomain hp hp1) :
    deriv (fun w : ℂ => sourceAbelianJointPrimitive hp hp1 n (w,ψ)) z =
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z := by
  have hjoint := sourceAbelianJointPrimitive_hasFDerivAt hp hp1 n (z,ψ) ht
  rw [deriv_spectral_section_eq_fderiv _ z ψ hjoint.differentiableAt,hjoint.fderiv]
  rw [deriv_spectral_section_eq_fderiv
    (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential u.2) u.1)
    z ψ (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,ψ) (mem_univ _)).differentiableAt]
  simp only [smul_apply,smul_eq_mul,div_eq_inv_mul]

/-- Every compact spectral subset off the cuts admits one complex-source
ball and an open spectral neighborhood contained in the glued domain.
Neither a finite spectral set nor a finite-gap source is assumed. -/
theorem exists_sourceAbelianJointDomain_compact_product
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (K : Set ℂ)
    (hK : IsCompact K) (hKroot : K ⊆ sourceCanonicalRootDomain hp hp1 φ.val) :
    ∃ (U : Set ℂ) (r : ℝ), IsOpen U ∧ K ⊆ U ∧ 0 < r ∧
      U ×ˢ Metric.ball φ.val r ⊆ sourceAbelianJointDomain hp hp1 := by
  have hsub : K ×ˢ {φ.val} ⊆ sourceAbelianJointDomain hp hp1 := by
    rintro ⟨z,ψ⟩ ⟨hz,hψ⟩
    obtain rfl := mem_singleton_iff.mp hψ
    exact (mem_sourceAbelianJointDomain_real_iff hp hp1 φ z).mpr (hKroot hz)
  obtain ⟨U,V,hU,hV,hKU,hφV,hUV⟩ := generalized_tube_lemma hK isCompact_singleton
    (isOpen_sourceAbelianJointDomain hp hp1) hsub
  obtain ⟨r,hr,hrV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hφV (mem_singleton _)))
  exact ⟨U,r,hU,hKU,hr,(prod_mono_right hrV).trans hUV⟩

/-- The free normalization is unchanged by complex-source gluing. -/
theorem sourceAbelianJointPrimitive_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 (0 : CoeffPair p)) :
    sourceAbelianJointPrimitive hp hp1 n (z,0) = -I*z+I*(Real.pi : ℂ)*n := by
  have h := sourceAbelianJointPrimitive_eq_real hp hp1 n (0 : realTypeSourceSubmodule p) z hz
  simpa only [ZeroMemClass.coe_zero,sourceAbelianPrimitive_zero] using h

end NLS.ZakharovShabat
