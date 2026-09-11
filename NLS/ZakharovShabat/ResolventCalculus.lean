import NLS.ZakharovShabat.ResolventAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Resolvent identities and differentiation

The inverse equations yield difference identities for arbitrary resolvent
parameters and potentials. Differentiating those equations gives the joint
Fréchet derivative, the spectral derivative `∂z R = -R²`, and the potential
variation `Dφ R[ψ] = R Φ(ψ) R`, with the inner inverse valued in the domain.
These are operator-norm statements for the coefficient-space realization.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inverse difference formula, with both inverses valued in the domain. -/
theorem resolventToDomain_difference (hp : p ≠ ⊤) (φ ψ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp ψ) :
    resolventToDomain hp φ z - resolventToDomain hp ψ w =
      (resolventToDomain hp φ z).comp
        ((spectralPencil hp ψ w - spectralPencil hp φ z).comp (resolventToDomain hp ψ w)) := by
  apply ContinuousLinearMap.ext
  intro a
  apply hz.injective
  simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    spectralPencil_resolventToDomain hp φ z hz, spectralPencil_resolventToDomain hp ψ w hw]

/-- The inverse difference formula on the base space, valid when both the
potential and the spectral parameter change. -/
theorem resolvent_difference (hp : p ≠ ⊤) (φ ψ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp ψ) :
    resolvent hp φ z - resolvent hp ψ w =
      (resolvent hp φ z).comp
        ((spectralPencil hp ψ w - spectralPencil hp φ z).comp (resolventToDomain hp ψ w)) := by
  have h := resolventToDomain_difference hp φ ψ z w hz hw
  apply ContinuousLinearMap.ext
  intro a
  have ha := congrArg (fun R : PairSpace p →L[ℂ] Domain p => domainInclusion (R a)) h
  simpa only [sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    resolvent] using ha

/-- The standard resolvent identity for the convention `R(z) = (z - L)⁻¹`. -/
theorem resolvent_identity (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp φ) :
    resolvent hp φ z - resolvent hp φ w =
      (w - z) • (resolvent hp φ z).comp (resolvent hp φ w) := by
  rw [resolvent_difference hp φ φ z w hz hw]
  apply ContinuousLinearMap.ext
  intro a
  change resolvent hp φ z
    (spectralPencil hp φ w (resolventToDomain hp φ w a) -
      spectralPencil hp φ z (resolventToDomain hp φ w a)) =
    (w - z) • resolvent hp φ z (resolvent hp φ w a)
  have heq (f : Domain p) : spectralPencil hp φ w f - spectralPencil hp φ z f =
      (w - z) • domainInclusion f := by
    simp only [spectralPencil_apply]
    module
  rw [heq, map_smul]
  rfl

/-- The resolvents at two parameters commute. -/
theorem resolvent_commute (hp : p ≠ ⊤) (φ : PairSpace p) (z w : ℂ)
    (hz : z ∈ resolventSet hp φ) (hw : w ∈ resolventSet hp φ) :
    (resolvent hp φ z).comp (resolvent hp φ w) =
      (resolvent hp φ w).comp (resolvent hp φ z) := by
  by_cases heq : z = w
  · subst w; rfl
  have hzw := resolvent_identity hp φ z w hz hw
  have hwz := resolvent_identity hp φ w z hw hz
  have h : (w - z) • (resolvent hp φ z).comp (resolvent hp φ w) =
      (w - z) • (resolvent hp φ w).comp (resolvent hp φ z) := by
    linear_combination (norm := module) -hzw -hwz
  exact (smul_right_injective _ (sub_ne_zero.mpr (Ne.symm heq))) h

/-- Resolvent difference under a change of potential. -/
theorem resolvent_potential_identity (hp : p ≠ ⊤) (φ ψ : PairSpace p) (z : ℂ)
    (hφ : z ∈ resolventSet hp φ) (hψ : z ∈ resolventSet hp ψ) :
    resolvent hp φ z - resolvent hp ψ z =
      (resolvent hp φ z).comp
        ((potentialOperator hp (φ - ψ)).comp (resolventToDomain hp ψ z)) := by
  rw [resolvent_difference hp φ ψ z z hφ hψ]
  have hpot : potentialOperator hp (φ - ψ) = potentialOperator hp φ - potentialOperator hp ψ :=
    map_sub (potentialOperatorCLM hp) φ ψ
  have hP : spectralPencil hp ψ z - spectralPencil hp φ z = potentialOperator hp (φ - ψ) := by
    rw [hpot]
    unfold spectralPencil operator
    abel
  rw [hP]

/-- The constant linear variation of the affine spectral pencil. -/
def pencilVariation (hp : p ≠ ⊤) :
    (PairSpace p × ℂ) →L[ℂ] (Domain p →L[ℂ] PairSpace p) :=
  (ContinuousLinearMap.snd ℂ (PairSpace p) ℂ).smulRight domainInclusion -
    (potentialOperatorCLM hp).comp (ContinuousLinearMap.fst ℂ (PairSpace p) ℂ)

@[simp] theorem pencilVariation_apply (hp : p ≠ ⊤) (d : PairSpace p × ℂ) :
    pencilVariation hp d = d.2 • domainInclusion - potentialOperator hp d.1 := rfl

/-- The spectral pencil is affine with this linear part. -/
theorem spectralPencil_eq_variation (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    spectralPencil hp φ z = pencilVariation hp (φ, z) - freeOperator := by
  rw [pencilVariation_apply]
  unfold spectralPencil operator
  abel

/-- The joint derivative of the spectral pencil. -/
theorem hasFDerivAt_spectralPencil (hp : p ≠ ⊤) (s : PairSpace p × ℂ) :
    HasFDerivAt (fun t : PairSpace p × ℂ => spectralPencil hp t.1 t.2) (pencilVariation hp) s := by
  simpa only [spectralPencil_eq_variation] using
    (pencilVariation hp).hasFDerivAt.sub_const freeOperator

/-- The joint inverse derivative, as a continuous linear map on increments
`(δφ,δz)`: `-R_D (δz inclusion - Φ(δφ)) R_D`. -/
def resolventToDomainDerivative (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    (PairSpace p × ℂ) →L[ℂ] (PairSpace p →L[ℂ] Domain p) :=
  -((ContinuousLinearMap.compL ℂ (PairSpace p) (PairSpace p) (Domain p))
    (resolventToDomain hp φ z)).comp
      (((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)).flip
        (resolventToDomain hp φ z)).comp (pencilVariation hp))

@[simp] theorem resolventToDomainDerivative_apply (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (d : PairSpace p × ℂ) (a : PairSpace p) :
    resolventToDomainDerivative hp φ z d a =
      -resolventToDomain hp φ z (pencilVariation hp d (resolventToDomain hp φ z a)) := rfl

/-- The explicit joint Fréchet derivative of the domain-valued inverse. -/
theorem hasFDerivAt_resolventToDomain (hp : p ≠ ⊤) (s : PairSpace p × ℂ)
    (hs : s ∈ resolventDomain hp) :
    HasFDerivAt (fun t : PairSpace p × ℂ => resolventToDomain hp t.1 t.2)
      (resolventToDomainDerivative hp s.1 s.2) s := by
  let R := fun t : PairSpace p × ℂ => resolventToDomain hp t.1 t.2
  have hR : DifferentiableAt ℂ R s := (analyticAt_resolventToDomain hp s hs).differentiableAt
  have hprod := (hasFDerivAt_spectralPencil hp s).clm_comp hR.hasFDerivAt
  have hevent : (fun t : PairSpace p × ℂ =>
      (spectralPencil hp t.1 t.2).comp (R t)) =ᶠ[nhds s] fun _ => 1 := by
    filter_upwards [(isOpen_resolventDomain hp).mem_nhds hs] with t ht
    apply ContinuousLinearMap.ext
    exact spectralPencil_resolventToDomain hp t.1 t.2 ht
  have hzero := (hasFDerivAt_const (𝕜 := ℂ) (1 : PairSpace p →L[ℂ] PairSpace p) s).congr_of_eventuallyEq
    hevent
  have heq := hprod.unique hzero
  have hD : fderiv ℂ R s = resolventToDomainDerivative hp s.1 s.2 := by
    apply ContinuousLinearMap.ext
    intro d
    apply ContinuousLinearMap.ext
    intro a
    have hd := congrArg (fun D : (PairSpace p × ℂ) →L[ℂ] (PairSpace p →L[ℂ] PairSpace p) =>
      D d a) heq
    change spectralPencil hp s.1 s.2 (fderiv ℂ R s d a) +
      pencilVariation hp d (R s a) = 0 at hd
    have hinv := congrArg (resolventToDomain hp s.1 s.2) hd
    rw [map_add, map_zero, resolventToDomain_spectralPencil hp s.1 s.2 hs] at hinv
    exact eq_neg_iff_add_eq_zero.mpr hinv
  rw [← hD]
  exact hR.hasFDerivAt

/-- The joint derivative after inclusion into the base space. -/
def resolventDerivative (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    (PairSpace p × ℂ) →L[ℂ] (PairSpace p →L[ℂ] PairSpace p) :=
  ((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p)) domainInclusion).comp
    (resolventToDomainDerivative hp φ z)

/-- The derivative splits into a potential term and a spectral-parameter term. -/
theorem resolventDerivative_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (d : PairSpace p × ℂ) (a : PairSpace p) :
    resolventDerivative hp φ z d a =
      resolvent hp φ z (potentialOperator hp d.1 (resolventToDomain hp φ z a)) -
        d.2 • resolvent hp φ z (resolvent hp φ z a) := by
  change domainInclusion (resolventToDomainDerivative hp φ z d a) = _
  rw [resolventToDomainDerivative_apply, map_neg, pencilVariation_apply,
    sub_apply, smul_apply, map_sub, map_smul,
    map_sub, map_smul]
  change -(d.2 • resolvent hp φ z (resolvent hp φ z a) -
    resolvent hp φ z (potentialOperator hp d.1 (resolventToDomain hp φ z a))) = _
  abel

/-- The explicit joint Fréchet derivative in base-space operator norm. -/
theorem hasFDerivAt_resolvent (hp : p ≠ ⊤) (s : PairSpace p × ℂ)
    (hs : s ∈ resolventDomain hp) :
    HasFDerivAt (fun t : PairSpace p × ℂ => resolvent hp t.1 t.2)
      (resolventDerivative hp s.1 s.2) s :=
  (((ContinuousLinearMap.compL ℂ (PairSpace p) (Domain p) (PairSpace p))
    domainInclusion).hasFDerivAt).comp s (hasFDerivAt_resolventToDomain hp s hs)

/-- The joint derivative as mathlib's `fderiv`. -/
theorem fderiv_resolvent (hp : p ≠ ⊤) (s : PairSpace p × ℂ)
    (hs : s ∈ resolventDomain hp) :
    fderiv ℂ (fun t : PairSpace p × ℂ => resolvent hp t.1 t.2) s =
      resolventDerivative hp s.1 s.2 :=
  (hasFDerivAt_resolvent hp s hs).fderiv

/-- The spectral derivative has the negative sign appropriate to `(z - L)⁻¹`. -/
theorem hasDerivAt_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    HasDerivAt (resolvent hp φ) (-(resolvent hp φ z).comp (resolvent hp φ z)) z := by
  have h : HasDerivAt (resolvent hp φ) (resolventDerivative hp φ z (0, 1)) z :=
    ((hasFDerivAt_resolvent hp (φ, z) hz).comp z
      (hasFDerivAt_prodMk_right φ z)).hasDerivAt
  have hzero : potentialOperator hp (0 : PairSpace p) = 0 := (potentialOperatorCLM hp).map_zero
  have heq : resolventDerivative hp φ z (0, 1) =
      -(resolvent hp φ z).comp (resolvent hp φ z) := by
    apply ContinuousLinearMap.ext
    intro a
    rw [resolventDerivative_apply]
    simp only [hzero, zero_apply,
      map_zero, one_smul, zero_sub, neg_apply, ContinuousLinearMap.comp_apply]
  exact heq ▸ h

/-- The spectral derivative as mathlib's `deriv`. -/
theorem deriv_resolvent (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    deriv (resolvent hp φ) z = -(resolvent hp φ z).comp (resolvent hp φ z) :=
  (hasDerivAt_resolvent hp φ z hz).deriv

/-- The derivative with respect to the potential alone. -/
def potentialResolventDerivative (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    PairSpace p →L[ℂ] (PairSpace p →L[ℂ] PairSpace p) :=
  (resolventDerivative hp φ z).comp (ContinuousLinearMap.inl ℂ (PairSpace p) ℂ)

/-- A potential variation `ψ` acts by `R Φ(ψ) R_D`, with a domain-valued inner inverse. -/
theorem potentialResolventDerivative_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (ψ a : PairSpace p) :
    potentialResolventDerivative hp φ z ψ a =
      resolvent hp φ z (potentialOperator hp ψ (resolventToDomain hp φ z a)) := by
  change resolventDerivative hp φ z (ψ, 0) a = _
  rw [resolventDerivative_apply]
  simp only [zero_smul, sub_zero]

/-- Fréchet differentiation of the resolvent with respect to the potential. -/
theorem hasFDerivAt_resolvent_potential (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    HasFDerivAt (fun ψ : PairSpace p => resolvent hp ψ z)
      (potentialResolventDerivative hp φ z) φ :=
  (hasFDerivAt_resolvent hp (φ, z) hz).comp φ
    (f := fun ψ : PairSpace p => (ψ, z)) (hasFDerivAt_prodMk_left (𝕜 := ℂ) φ z)

/-- The potential derivative as mathlib's `fderiv`. -/
theorem fderiv_resolvent_potential (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (hz : z ∈ resolventSet hp φ) :
    fderiv ℂ (fun ψ : PairSpace p => resolvent hp ψ z) φ = potentialResolventDerivative hp φ z :=
  (hasFDerivAt_resolvent_potential hp φ z hz).fderiv

/-- Every point outside the free lattice is in the full zero-potential resolvent set. -/
theorem mem_resolventSet_zero_of_notMem (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    z ∈ resolventSet (p := p) hp 0 :=
  mem_resolventSet_of_neumannCondition hp 0 z hz (neumannCondition_zero hp z hz)

/-- Compatibility of the full and free inverses into the one-derivative domain. -/
theorem resolventToDomain_zero_eq_free (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    resolventToDomain (p := p) hp 0 z = freeResolventToDomain z hz := by
  apply ContinuousLinearMap.ext
  intro a
  apply (freePencilEquiv z hz).injective
  change freePencil z (resolventToDomain hp 0 z a) = freePencil z (freeResolventToDomain z hz a)
  rw [freePencil_freeResolventToDomain]
  simpa only [spectralPencil, operator_zero, freePencil] using
    spectralPencil_resolventToDomain hp 0 z (mem_resolventSet_zero_of_notMem hp z hz) a

/-- Compatibility of the full and free base-space resolvents. -/
theorem resolvent_zero_eq_free (hp : p ≠ ⊤) (z : ℂ) (hz : z ∉ freeLattice) :
    resolvent (p := p) hp 0 z = freeResolvent z hz := by
  rw [resolvent, resolventToDomain_zero_eq_free hp z hz]
  rfl

/-- The resolvent identity used before the Neumann construction on printed
page 23: `Rφ(z) (I - Φ R₀(z)) = R₀(z)`. No Neumann smallness assumption is needed. -/
theorem resolvent_comp_one_sub_potentialFreeResolvent (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∉ freeLattice) (hφ : z ∈ resolventSet hp φ) :
    (resolvent hp φ z).comp (1 - potentialFreeResolvent hp φ z hz) = freeResolvent z hz := by
  have h := resolvent_potential_identity hp φ 0 z hφ (mem_resolventSet_zero_of_notMem hp z hz)
  rw [sub_zero, resolvent_zero_eq_free hp z hz, resolventToDomain_zero_eq_free hp z hz] at h
  apply ContinuousLinearMap.ext
  intro a
  have ha := congrArg (fun A : PairSpace p →L[ℂ] PairSpace p => A a) h
  change resolvent hp φ z a - freeResolvent z hz a =
    resolvent hp φ z (potentialFreeResolvent hp φ z hz a) at ha
  change resolvent hp φ z (a - potentialFreeResolvent hp φ z hz a) = freeResolvent z hz a
  rw [map_sub, ← ha]
  abel

end NLS.ZakharovShabat
