import NLS.ZakharovShabat.BoundaryOperators
import NLS.ZakharovShabat.ResolventContour

/-!
# Resolvents of the boundary restrictions

Chapter 1, §4, proof of Theorem 1.4. The boundary condition selects a closed
summand, in both the base and domain norms. Its resolvent set is defined by
bijectivity of the restricted pencil, not by membership in the periodic
resolvent set. The latter is a common subset of both boundary resolvent sets.
All potentials here are already Dirichlet-reflected coefficient potentials;
the period-one interval-extension map remains a separate obligation.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat

/-- The two boundary conditions in Section 4. -/
inductive BoundaryCondition | dirichlet | neumann

namespace BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The selected closed base subspace. -/
def space : BoundaryCondition → Submodule ℂ (PairSpace p)
  | .dirichlet => dirichletSubspace
  | .neumann => neumannSubspace

/-- The selected closed one-derivative domain. -/
def domain : BoundaryCondition → Submodule ℂ (Domain p)
  | .dirichlet => weightedDirichletSubspace 1
  | .neumann => weightedNeumannSubspace 1

def projection : BoundaryCondition → (PairSpace p →L[ℂ] PairSpace p)
  | .dirichlet => dirichletProjection
  | .neumann => neumannProjection

def domainProjection : BoundaryCondition → (Domain p →L[ℂ] Domain p)
  | .dirichlet => domainDirichletProjection
  | .neumann => domainNeumannProjection

variable (b : BoundaryCondition)

theorem isClosed_space : IsClosed (space (p := p) b : Set (PairSpace p)) := by
  cases b
  · exact isClosed_dirichletSubspace
  · exact isClosed_neumannSubspace

theorem isClosed_domain : IsClosed (domain (p := p) b : Set (Domain p)) := by
  cases b
  · exact isClosed_weightedDirichletSubspace 1
  · exact isClosed_weightedNeumannSubspace 1

instance : CompleteSpace ↥(space (p := p) b) := (isClosed_space b).completeSpace_coe
instance : CompleteSpace ↥(domain (p := p) b) := (isClosed_domain b).completeSpace_coe

theorem projection_mem (a : PairSpace p) : projection b a ∈ space b := by
  cases b
  · exact ReflectionSplit.positiveProjection_mem _ a
  · exact ReflectionSplit.negativeProjection_mem _ a

theorem domainProjection_mem (f : Domain p) : domainProjection b f ∈ domain b := by
  cases b
  · exact ReflectionSplit.positiveProjection_mem _ f
  · exact ReflectionSplit.negativeProjection_mem _ f

theorem projection_eq_self {a : PairSpace p} (ha : a ∈ space b) : projection b a = a := by
  cases b
  · exact ReflectionSplit.positiveProjection_eq_self _ ha
  · exact ReflectionSplit.negativeProjection_eq_self _ ha

theorem domainProjection_eq_self {f : Domain p} (hf : f ∈ domain b) :
    domainProjection b f = f := by
  cases b
  · exact ReflectionSplit.positiveProjection_eq_self _ hf
  · exact ReflectionSplit.negativeProjection_eq_self _ hf

theorem inclusion_mem (f : Domain p) : domainInclusion f ∈ space b ↔ f ∈ domain b := by
  cases b
  · exact domainInclusion_mem_dirichlet f
  · exact domainInclusion_mem_neumann f

theorem inclusion_projection (f : Domain p) :
    domainInclusion (domainProjection b f) = projection b (domainInclusion f) := by
  cases b
  · exact domainInclusion_dirichletProjection f
  · exact domainInclusion_neumannProjection f

theorem operator_mem (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (f : Domain p) (hf : f ∈ domain b) : operator hp φ f ∈ space b := by
  cases b
  · exact operator_mem_dirichlet hp φ hφ f hf
  · exact operator_mem_neumann hp φ hφ f hf

theorem operator_projection (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (f : Domain p) : projection b (operator hp φ f) = operator hp φ (domainProjection b f) := by
  cases b
  · exact operator_dirichletProjection hp φ hφ f
  · exact operator_neumannProjection hp φ hφ f

/-- Retraction onto the base summand, retaining its norm. -/
def retract : PairSpace p →L[ℂ] ↥(space (p := p) b) := (projection b).codRestrict _ (projection_mem b)

/-- Retraction onto the domain summand, retaining the stronger domain norm. -/
def domainRetract : Domain p →L[ℂ] ↥(domain (p := p) b) :=
  (domainProjection b).codRestrict _ (domainProjection_mem b)

/-- Inclusion of the restricted operator domain. -/
def inclusion : ↥(domain (p := p) b) →L[ℂ] ↥(space (p := p) b) :=
  (domainInclusion.comp (domain b).subtypeL).codRestrict _
    (fun f => (inclusion_mem b f.val).mpr f.property)

@[simp] theorem inclusion_apply (f : domain (p := p) b) :
    (inclusion b f).val = domainInclusion f.val := rfl

/-- The restriction of `z-L` to the chosen boundary condition. -/
def pencil (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    ↥(domain (p := p) b) →L[ℂ] ↥(space (p := p) b) :=
  ((spectralPencil hp φ z).comp (domain b).subtypeL).codRestrict _ (fun f =>
    (space b).sub_mem ((space b).smul_mem z ((inclusion_mem b f.val).mpr f.property))
      (operator_mem b hp φ hφ f.val f.property))

@[simp] theorem pencil_apply (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (z : ℂ) (f : domain (p := p) b) : (pencil b hp φ hφ z f).val = spectralPencil hp φ z f.val := rfl

/-- The actual resolvent set of the boundary restriction. -/
def resolventSet (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : Set ℂ :=
  {z | Function.Bijective (pencil b hp φ hφ z)}

theorem spectralPencil_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (f : Domain p) :
    spectralPencil hp φ z (domainProjection b f) = projection b (spectralPencil hp φ z f) := by
  simp only [spectralPencil_apply, inclusion_projection, ← operator_projection b hp φ hφ,
    map_sub, map_smul]

theorem fullResolventToDomain_projection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ)
    (a : PairSpace p) :
    ZakharovShabat.resolventToDomain hp φ z (projection b a) =
      domainProjection b (ZakharovShabat.resolventToDomain hp φ z a) := by
  apply hz.injective
  rw [spectralPencil_resolventToDomain hp φ z hz, spectralPencil_projection b hp φ hφ,
    spectralPencil_resolventToDomain hp φ z hz]

/-- Both boundary projections commute with the full periodic resolvent. -/
theorem projection_commute_fullResolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ) :
    Commute (projection b) (ZakharovShabat.resolvent hp φ z) := by
  apply ContinuousLinearMap.ext
  intro a
  change projection b (domainInclusion (ZakharovShabat.resolventToDomain hp φ z a)) =
    domainInclusion (ZakharovShabat.resolventToDomain hp φ z (projection b a))
  rw [← inclusion_projection, fullResolventToDomain_projection b hp φ hφ z hz]

/-- The Cauchy–Riesz projectors used in Theorem 1.4 preserve the boundary decomposition. -/
theorem projection_commute_contour (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ) :
    Commute (projection b) (resolventCircleIntegral hp φ c r) :=
  commute_resolventCircleIntegral hp φ c r hr hc _
    (fun z hz => projection_commute_fullResolvent b hp φ hφ z (hc hz))

theorem contour_mem (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hc : Metric.sphere c r ⊆ ZakharovShabat.resolventSet hp φ)
    (a : PairSpace p) (ha : a ∈ space b) : resolventCircleIntegral hp φ c r a ∈ space b := by
  have h := congrArg (fun T : PairSpace p →L[ℂ] PairSpace p => T a)
    (projection_commute_contour b hp φ hφ c r hr hc).eq
  change projection b (resolventCircleIntegral hp φ c r a) =
    resolventCircleIntegral hp φ c r (projection b a) at h
  rw [projection_eq_self b ha] at h
  rw [← h]
  exact projection_mem b _

/-- Restrict a periodic inverse to the boundary domain, using the fixed retractions. -/
def restrictedInverse (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    ↥(space (p := p) b) →L[ℂ] ↥(domain (p := p) b) :=
  (domainRetract b).comp ((ZakharovShabat.resolventToDomain hp φ z).comp (space b).subtypeL)

theorem pencil_restrictedInverse (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ)
    (a : space (p := p) b) : pencil b hp φ hφ z (restrictedInverse b hp φ z a) = a := by
  apply Subtype.ext
  change spectralPencil hp φ z (domainProjection b (ZakharovShabat.resolventToDomain hp φ z a.val)) = a.val
  rw [spectralPencil_projection b hp φ hφ, spectralPencil_resolventToDomain hp φ z hz,
    projection_eq_self b a.property]

theorem restrictedInverse_pencil (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ)
    (f : domain (p := p) b) : restrictedInverse b hp φ z (pencil b hp φ hφ z f) = f := by
  apply Subtype.ext
  change domainProjection b (ZakharovShabat.resolventToDomain hp φ z (spectralPencil hp φ z f.val)) = f.val
  rw [resolventToDomain_spectralPencil hp φ z hz, domainProjection_eq_self b f.property]

theorem mem_resolventSet_of_periodic (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ) :
    z ∈ resolventSet b hp φ hφ :=
  ⟨Function.LeftInverse.injective (restrictedInverse_pencil b hp φ hφ z hz),
    Function.RightInverse.surjective (pencil_restrictedInverse b hp φ hφ z hz)⟩

private theorem free_reference (hp : p ≠ ⊤) :
    Complex.I ∈ ZakharovShabat.resolventSet hp (0 : PairSpace p) :=
  mem_resolventSet_zero_of_notMem hp Complex.I (notMem_freeLattice_of_im_ne_zero (by simp))

/-- Normalization by the fixed free boundary inverse at `i`. -/
def normalizedPencil (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b) :=
  (pencil b hp φ hφ z).comp (restrictedInverse b hp 0 Complex.I)

theorem freeInverse_bijective (hp : p ≠ ⊤) :
    Function.Bijective (restrictedInverse (p := p) b hp 0 Complex.I) :=
  ⟨Function.LeftInverse.injective (pencil_restrictedInverse b hp 0 (by simp) _ (free_reference hp)),
    Function.RightInverse.surjective (restrictedInverse_pencil b hp 0 (by simp) _ (free_reference hp))⟩

theorem mem_resolventSet_iff_isUnit (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    z ∈ resolventSet b hp φ hφ ↔ IsUnit (normalizedPencil b hp φ hφ z) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff (pencil b hp φ hφ z) (freeInverse_bijective b hp)).symm

/-- The boundary inverse on its entire resolvent set, zero elsewhere. -/
def resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    ↥(space (p := p) b) →L[ℂ] ↥(domain (p := p) b) :=
  (restrictedInverse b hp 0 Complex.I).comp (Ring.inverse (normalizedPencil b hp φ hφ z))

/-- The base-space boundary resolvent. -/
def resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b) :=
  (inclusion b).comp (resolventToDomain b hp φ hφ z)

theorem pencil_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ resolventSet b hp φ hφ)
    (a : space (p := p) b) : pencil b hp φ hφ z (resolventToDomain b hp φ hφ z a) = a :=
  congrArg (fun A : ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b) => A a)
    (Ring.mul_inverse_cancel _ ((mem_resolventSet_iff_isUnit b hp φ hφ z).mp hz))

theorem resolventToDomain_pencil (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ resolventSet b hp φ hφ)
    (f : domain (p := p) b) : resolventToDomain b hp φ hφ z (pencil b hp φ hφ z f) = f := by
  apply hz.injective
  exact pencil_resolventToDomain b hp φ hφ z hz _

theorem resolventToDomain_eq_restrictedInverse (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∈ ZakharovShabat.resolventSet hp φ) :
    resolventToDomain b hp φ hφ z = restrictedInverse b hp φ z := by
  apply ContinuousLinearMap.ext
  intro a
  apply (mem_resolventSet_of_periodic b hp φ hφ z hz).injective
  rw [pencil_resolventToDomain b hp φ hφ z (mem_resolventSet_of_periodic b hp φ hφ z hz),
    pencil_restrictedInverse b hp φ hφ z hz]

theorem resolventToDomain_eq_zero_of_notMem (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) (hz : z ∉ resolventSet b hp φ hφ) :
    resolventToDomain b hp φ hφ z = 0 := by
  have hn := mt (mem_resolventSet_iff_isUnit b hp φ hφ z).mpr hz
  simp only [resolventToDomain, Ring.inverse_non_unit _ hn, ContinuousLinearMap.comp_zero]

/-- Retraction of the periodic base resolvent agrees with inclusion of the restricted inverse. -/
theorem inclusion_restrictedInverse (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    (inclusion b).comp (restrictedInverse b hp φ z) =
      (retract b).comp ((ZakharovShabat.resolvent hp φ z).comp (space b).subtypeL) := by
  apply ContinuousLinearMap.ext
  intro a
  apply Subtype.ext
  exact inclusion_projection b _

theorem isCompactOperator_restrictedInverse_base (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    IsCompactOperator ((inclusion b).comp (restrictedInverse b hp φ z)) := by
  rw [inclusion_restrictedInverse]
  exact ((isCompactOperator_resolvent hp φ z).comp_clm (space b).subtypeL).clm_comp (retract b)

/-- The boundary resolvent is compact, including its totalized zero values. -/
theorem isCompactOperator_resolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : IsCompactOperator (resolvent b hp φ hφ z) := by
  change IsCompactOperator ((inclusion b).comp ((restrictedInverse b hp 0 Complex.I).comp
    (Ring.inverse (normalizedPencil b hp φ hφ z))))
  rw [← ContinuousLinearMap.comp_assoc]
  exact (isCompactOperator_restrictedInverse_base b hp 0 Complex.I).comp_clm _

/-- The restricted pencil can be formed using fixed bounded maps on either side. -/
theorem pencil_eq_retract (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    pencil b hp φ hφ z = (retract b).comp ((spectralPencil hp φ z).comp (domain b).subtypeL) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  exact (projection_eq_self b (pencil b hp φ hφ z f).property).symm

/-- Joint analyticity on the space of already-reflected potentials. -/
theorem analyticAt_pencil (hp : p ≠ ⊤) (s : ↥(dirichletSubspace (p := p)) × ℂ) :
    AnalyticAt ℂ (fun t : ↥(dirichletSubspace (p := p)) × ℂ => pencil b hp t.1.val t.1.property t.2) s := by
  have hi := ((dirichletSubspace (p := p)).subtypeL.analyticAt s.1).comp analyticAt_fst
  have hP := (analyticAt_spectralPencil hp (s.1.val, s.2)).comp
    (f := fun t : ↥(dirichletSubspace (p := p)) × ℂ => (t.1.val, t.2)) (hi.prod analyticAt_snd)
  simp_rw [pencil_eq_retract]
  exact ((ContinuousLinearMap.compL ℂ ↥(domain (p := p) b) (PairSpace p) ↥(space (p := p) b)) (retract b)).analyticAt (𝕜 := ℂ) (E := (↥(domain (p := p) b) →L[ℂ] PairSpace p)) (F := (↥(domain (p := p) b) →L[ℂ] ↥(space (p := p) b))) _ |>.comp
    (((ContinuousLinearMap.compL ℂ ↥(domain (p := p) b) (Domain p) (PairSpace p)).flip (domain b).subtypeL).analyticAt (𝕜 := ℂ) (E := (Domain p →L[ℂ] PairSpace p)) (F := (↥(domain (p := p) b) →L[ℂ] PairSpace p)) _ |>.comp hP)

theorem analyticAt_normalizedPencil (hp : p ≠ ⊤) (s : ↥(dirichletSubspace (p := p)) × ℂ) :
    AnalyticAt ℂ (fun t : ↥(dirichletSubspace (p := p)) × ℂ =>
      normalizedPencil b hp t.1.val t.1.property t.2) s := by
  let C : (↥(domain (p := p) b) →L[ℂ] ↥(space (p := p) b)) →L[ℂ]
      (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b)) :=
    (ContinuousLinearMap.compL ℂ ↥(space (p := p) b) ↥(domain (p := p) b)
      ↥(space (p := p) b)).flip (restrictedInverse b hp 0 Complex.I)
  exact (C.analyticAt (𝕜 := ℂ) (E := (↥(domain (p := p) b) →L[ℂ] ↥(space (p := p) b))) (F := (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b))) _).comp
    (f := fun t : ↥(dirichletSubspace (p := p)) × ℂ => pencil b hp t.1.val t.1.property t.2)
    (analyticAt_pencil b hp s)

/-- The joint domain for the actual boundary resolvent. -/
def resolventDomain (hp : p ≠ ⊤) : Set (↥(dirichletSubspace (p := p)) × ℂ) :=
  {s | s.2 ∈ resolventSet b hp s.1.val s.1.property}

theorem isOpen_resolventDomain (hp : p ≠ ⊤) : IsOpen (resolventDomain (p := p) b hp) := by
  have hc : Continuous (fun t : ↥(dirichletSubspace (p := p)) × ℂ =>
      normalizedPencil b hp t.1.val t.1.property t.2) :=
    continuous_iff_continuousAt.mpr (fun t => (analyticAt_normalizedPencil b hp t).continuousAt)
  have heq : resolventDomain b hp =
      (fun t : ↥(dirichletSubspace (p := p)) × ℂ => normalizedPencil b hp t.1.val t.1.property t.2) ⁻¹'
        {A | IsUnit A} := by
    ext t
    exact mem_resolventSet_iff_isUnit b hp t.1.val t.1.property t.2
  rw [heq]
  exact (show IsOpen {A : ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b) | IsUnit A} from Units.isOpen (R := ↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b))).preimage hc

theorem isOpen_resolventSet (hp : p ≠ ⊤) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    IsOpen (resolventSet b hp φ hφ) :=
  (isOpen_resolventDomain b hp).preimage
    ((continuous_const (y := (⟨φ, hφ⟩ : ↥(dirichletSubspace (p := p))))).prodMk continuous_id)

theorem analyticAt_resolventToDomain (hp : p ≠ ⊤) (s : ↥(dirichletSubspace (p := p)) × ℂ)
    (hs : s ∈ resolventDomain b hp) :
    AnalyticAt ℂ (fun t : ↥(dirichletSubspace (p := p)) × ℂ =>
      resolventToDomain b hp t.1.val t.1.property t.2) s := by
  have hi := (analyticOnNhd_inverse (𝕜 := ℂ) _
    ((mem_resolventSet_iff_isUnit b hp s.1.val s.1.property s.2).mp hs)).comp
    (f := fun t : ↥(dirichletSubspace (p := p)) × ℂ => normalizedPencil b hp t.1.val t.1.property t.2)
    (analyticAt_normalizedPencil b hp s)
  exact ((ContinuousLinearMap.compL ℂ ↥(space (p := p) b) ↥(space (p := p) b) ↥(domain (p := p) b)) (restrictedInverse b hp 0 Complex.I)).analyticAt (𝕜 := ℂ) (E := (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b))) (F := (↥(space (p := p) b) →L[ℂ] ↥(domain (p := p) b))) _ |>.comp hi

theorem analyticAt_resolvent (hp : p ≠ ⊤) (s : ↥(dirichletSubspace (p := p)) × ℂ)
    (hs : s ∈ resolventDomain b hp) :
    AnalyticAt ℂ (fun t : ↥(dirichletSubspace (p := p)) × ℂ =>
      resolvent b hp t.1.val t.1.property t.2) s := by
  let C : (↥(space (p := p) b) →L[ℂ] ↥(domain (p := p) b)) →L[ℂ]
      (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b)) :=
    (ContinuousLinearMap.compL ℂ ↥(space (p := p) b) ↥(domain (p := p) b)
      ↥(space (p := p) b)) (inclusion b)
  exact (C.analyticAt (𝕜 := ℂ) (E := (↥(space (p := p) b) →L[ℂ] ↥(domain (p := p) b))) (F := (↥(space (p := p) b) →L[ℂ] ↥(space (p := p) b))) _).comp
    (f := fun t : ↥(dirichletSubspace (p := p)) × ℂ => resolventToDomain b hp t.1.val t.1.property t.2)
    (analyticAt_resolventToDomain b hp s hs)

end BoundaryCondition
end NLS.ZakharovShabat
