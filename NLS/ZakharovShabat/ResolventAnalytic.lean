import NLS.ZakharovShabat.ClosedOperator
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Analytic dependence of the resolvent

The full resolvent set consists of the parameters where the domain-to-base
spectral pencil is bijective. A fixed free inverse at `i` converts that pencil
into a bounded endomorphism, so Banach-algebra inversion gives a jointly
analytic resolvent in the potential and the spectral parameter. This supplies
the analytic-dependence assertion of Chapter 1, Corollary 3.3, printed page 24;
the sharp numerical region and discreteness of the spectrum are separate results.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Potential dependence is continuous linear in operator norm. -/
def potentialOperatorCLM (hp : p ≠ ⊤) :
    PairSpace p →L[ℂ] (Domain p →L[ℂ] PairSpace p) :=
  LinearMap.mkContinuous
    { toFun := potentialOperator hp
      map_add' := by
        intro φ ψ
        apply ContinuousLinearMap.ext
        intro f
        apply Prod.ext <;> simp [potentialOperator_apply, potentialMul]
      map_smul' := by
        intro c φ
        apply ContinuousLinearMap.ext
        intro f
        apply Prod.ext <;> simp [potentialOperator_apply, potentialMul] }
    (WeightedCoeff.sobolevEmbeddingConstant p hp)
    (fun φ => ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg φ))
      (norm_potentialOperator_le hp φ))

@[simp] theorem potentialOperatorCLM_apply (hp : p ≠ ⊤) (φ : PairSpace p) :
    potentialOperatorCLM hp φ = potentialOperator hp φ := rfl

/-- The spectral pencil is jointly entire in the potential and spectral parameter. -/
theorem analyticAt_spectralPencil (hp : p ≠ ⊤) (s : PairSpace p × ℂ) :
    AnalyticAt ℂ (fun t : PairSpace p × ℂ => spectralPencil hp t.1 t.2) s := by
  have hφ := ((potentialOperatorCLM hp).analyticAt s.1).comp analyticAt_fst
  exact (analyticAt_snd.smul analyticAt_const).sub (analyticAt_const.add hφ)

private theorem reference_off : Complex.I ∉ freeLattice :=
  notMem_freeLattice_of_im_ne_zero (by simp)

/-- Normalize by the fixed free inverse at `i`, obtaining an endomorphism of the
base space. The spectral parameter itself need not be outside the free lattice. -/
def normalizedPencil (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    PairSpace p →L[ℂ] PairSpace p :=
  (spectralPencil hp φ z).comp (freeResolventToDomain Complex.I reference_off)

/-- The complete resolvent set, defined by solvability of the spectral equation. -/
def resolventSet (hp : p ≠ ⊤) (φ : PairSpace p) : Set ℂ :=
  {z | Function.Bijective (spectralPencil hp φ z)}

/-- Normalization neither loses nor introduces invertible spectral parameters. -/
theorem mem_resolventSet_iff_isUnit (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    z ∈ resolventSet hp φ ↔ IsUnit (normalizedPencil hp φ z) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff (spectralPencil hp φ z)
    (freePencilEquiv (p := p) Complex.I reference_off).symm.bijective).symm

/-- The joint domain of the resolvent, allowing the potential to vary as well. -/
def resolventDomain (hp : p ≠ ⊤) : Set (PairSpace p × ℂ) :=
  {s | s.2 ∈ resolventSet hp s.1}

/-- The normalized pencil is jointly analytic in operator norm. -/
theorem analyticAt_normalizedPencil (hp : p ≠ ⊤) (s : PairSpace p × ℂ) :
    AnalyticAt ℂ (fun t : PairSpace p × ℂ => normalizedPencil hp t.1 t.2) s := by
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)).flip
    (freeResolventToDomain Complex.I reference_off)).analyticAt _ |>.comp
    (analyticAt_spectralPencil hp s)

/-- The joint resolvent domain is open. -/
theorem isOpen_resolventDomain (hp : p ≠ ⊤) : IsOpen (resolventDomain hp) := by
  have hcont : Continuous (fun t : PairSpace p × ℂ => normalizedPencil hp t.1 t.2) :=
    continuous_iff_continuousAt.mpr fun t => (analyticAt_normalizedPencil hp t).continuousAt
  have heq : resolventDomain hp =
      (fun t : PairSpace p × ℂ => normalizedPencil hp t.1 t.2) ⁻¹' {A | IsUnit A} := by
    ext t
    exact mem_resolventSet_iff_isUnit hp t.1 t.2
  rw [heq]
  exact Units.isOpen.preimage hcont

/-- The resolvent set is open for each fixed potential. -/
theorem isOpen_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p) :
    IsOpen (resolventSet hp φ) :=
  (isOpen_resolventDomain hp).preimage (continuous_const.prodMk continuous_id)

/-- The domain-valued inverse, extended by zero outside the resolvent set. -/
def resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    PairSpace p →L[ℂ] Domain p :=
  (freeResolventToDomain Complex.I reference_off).comp
    (Ring.inverse (normalizedPencil hp φ z))

/-- The full base-space resolvent, extended by zero outside its natural domain. -/
def resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    PairSpace p →L[ℂ] PairSpace p :=
  domainInclusion.comp (resolventToDomain hp φ z)

/-- Outside the resolvent set the totalized domain-valued function is zero. -/
theorem resolventToDomain_eq_zero_of_notMem (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ resolventSet hp φ) : resolventToDomain hp φ z = 0 := by
  have hnu : ¬ IsUnit (normalizedPencil hp φ z) :=
    fun h => hz ((mem_resolventSet_iff_isUnit hp φ z).mpr h)
  simp only [resolventToDomain, Ring.inverse_non_unit _ hnu, ContinuousLinearMap.comp_zero]

/-- Outside the resolvent set the totalized base-space function is zero. -/
theorem resolvent_eq_zero_of_notMem (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∉ resolventSet hp φ) : resolvent hp φ z = 0 := by
  rw [resolvent, resolventToDomain_eq_zero_of_notMem hp φ z hz, ContinuousLinearMap.comp_zero]

/-- The right inverse identity on the complete resolvent set. -/
theorem spectralPencil_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) (a : PairSpace p) :
    spectralPencil hp φ z (resolventToDomain hp φ z a) = a := by
  have h := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A a)
    (Ring.mul_inverse_cancel _ ((mem_resolventSet_iff_isUnit hp φ z).mp hz))
  exact h

/-- The left inverse identity on the complete resolvent set. -/
theorem resolventToDomain_spectralPencil (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) (f : Domain p) :
    resolventToDomain hp φ z (spectralPencil hp φ z f) = f := by
  apply hz.injective
  exact spectralPencil_resolventToDomain hp φ z hz _

/-- Every parameter admitted by the constructive Neumann condition belongs to
the full resolvent set. -/
theorem mem_resolventSet_of_neumannCondition (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    z ∈ resolventSet hp φ :=
  (spectralPencilEquiv hp φ z hz h).bijective

/-- Every finite-p potential has a nonempty resolvent set. -/
theorem resolventSet_nonempty (hp : p ≠ ⊤) (φ : PairSpace p) :
    (resolventSet hp φ).Nonempty := by
  obtain ⟨z, hz, h⟩ := exists_neumannParameter hp φ
  exact ⟨z, mem_resolventSet_of_neumannCondition hp φ z hz h⟩

/-- The global inverse agrees with the constructive Neumann inverse. -/
theorem resolventToDomain_eq_perturbed (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    resolventToDomain hp φ z = perturbedResolventToDomain hp φ z hz h := by
  apply ContinuousLinearMap.ext
  intro a
  have hmem := mem_resolventSet_of_neumannCondition hp φ z hz h
  apply hmem.injective
  rw [spectralPencil_resolventToDomain hp φ z hmem,
    spectralPencil_perturbedResolventToDomain]

/-- The base-space constructions agree on the Neumann region. -/
theorem resolvent_eq_perturbed (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (h : NeumannCondition hp φ z hz) :
    resolvent hp φ z = perturbedResolvent hp φ z hz h := by
  rw [resolvent, resolventToDomain_eq_perturbed hp φ z hz h,
    perturbedResolvent_eq_inclusion]

/-- Joint analyticity of the inverse into the one-derivative domain. -/
theorem analyticAt_resolventToDomain (hp : p ≠ ⊤) (s : PairSpace p × ℂ)
    (hs : s ∈ resolventDomain hp) :
    AnalyticAt ℂ (fun t : PairSpace p × ℂ => resolventToDomain hp t.1 t.2) s := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _
    ((mem_resolventSet_iff_isUnit hp s.1 s.2).mp hs)).comp
    (f := fun t : PairSpace p × ℂ => normalizedPencil hp t.1 t.2)
    (analyticAt_normalizedPencil hp s)
  exact ((ContinuousLinearMap.compL ℂ (PairSpace p) (PairSpace p) (Domain p))
    (freeResolventToDomain Complex.I reference_off)).analyticAt _ |>.comp hi

/-- Joint analyticity of the base-space resolvent in the potential and parameter. -/
theorem analyticAt_resolvent (hp : p ≠ ⊤) (s : PairSpace p × ℂ)
    (hs : s ∈ resolventDomain hp) :
    AnalyticAt ℂ (fun t : PairSpace p × ℂ => resolvent hp t.1 t.2) s :=
  ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p))
    domainInclusion).analyticAt _ |>.comp (analyticAt_resolventToDomain hp s hs)

/-- Joint analyticity throughout the open resolvent domain. -/
theorem analyticOnNhd_resolvent_joint (hp : p ≠ ⊤) :
    AnalyticOnNhd ℂ (fun s : PairSpace p × ℂ => resolvent hp s.1 s.2)
      (resolventDomain hp) :=
  analyticAt_resolvent hp

/-- Analyticity with respect to the potential at a fixed admissible parameter. -/
theorem analyticAt_resolvent_potential (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    AnalyticAt ℂ (fun ψ : PairSpace p => resolvent hp ψ z) φ :=
  (analyticAt_resolvent hp (φ, z) hz).comp (f := fun ψ : PairSpace p => (ψ, z))
    (analyticAt_id.prod analyticAt_const)

/-- Analyticity in the spectral parameter throughout the full resolvent set. -/
theorem analyticOnNhd_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) :
    AnalyticOnNhd ℂ (resolvent hp φ) (resolventSet hp φ) := by
  intro z hz
  exact (analyticAt_resolvent hp (φ, z) hz).comp (analyticAt_const.prod analyticAt_id)

/-- The full resolvent is compact at every resolvent parameter. Its totalized
value outside the resolvent set is zero and hence is compact as well. -/
theorem isCompactOperator_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    IsCompactOperator (resolvent hp φ z) := by
  have heq : resolvent hp φ z = (freeResolvent (p := p) Complex.I reference_off).comp
      (Ring.inverse (normalizedPencil hp φ z)) :=
    (ContinuousLinearMap.comp_assoc _ _ _).symm
  rw [heq]
  exact (isCompactOperator_freeResolvent (p := p) Complex.I reference_off).comp_clm _

end NLS.ZakharovShabat
