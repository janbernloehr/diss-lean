import NLS.ZakharovShabat.ResolventAnalytic
import NLS.FunctionalAnalysis.CompactSpectrum
import Mathlib.Topology.DiscreteSubset

/-!
# Discreteness of the periodic coefficient-space spectrum

At a fixed resolvent point `w`, spectral parameters `z ≠ w` correspond to
nonzero spectral values `(w-z)⁻¹` of the compact operator `R(w)`. Compact-operator
spectral finiteness therefore implies that every bounded portion of the periodic
spectrum is finite. This proves the discreteness conclusion of Chapter 1,
Corollary 3.3, printed page 24, for the coefficient-space realization.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The periodic coefficient-space spectrum is the complement of the full
resolvent set of the one-derivative-domain operator. -/
def periodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) : Set ℂ :=
  (resolventSet hp φ)ᶜ

/-- The periodic spectrum is closed. -/
theorem isClosed_periodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) :
    IsClosed (periodicSpectrum hp φ) :=
  (isOpen_resolventSet hp φ).isClosed_compl

/-- Factorization of a pencil at `z` through the inverse at `w`. -/
theorem spectralPencil_comp_resolventToDomain (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) :
    (spectralPencil hp φ z).comp (resolventToDomain hp φ w) =
      1 + (z - w) • resolvent hp φ w := by
  apply ContinuousLinearMap.ext
  intro a
  have h := spectralPencil_resolventToDomain hp φ w hw a
  simp only [spectralPencil_apply] at h
  change z • domainInclusion (resolventToDomain hp φ w a) -
      operator hp φ (resolventToDomain hp φ w a) =
    a + (z - w) • domainInclusion (resolventToDomain hp φ w a)
  conv_rhs => lhs; rw [← h]
  rw [sub_smul]
  abel

/-- Invertibility reduces to a scalar perturbation of the compact resolvent. -/
theorem mem_resolventSet_iff_shift_isUnit (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) :
    z ∈ resolventSet hp φ ↔ IsUnit (1 + (z - w) • resolvent hp φ w) := by
  have hR : Function.Bijective (resolventToDomain hp φ w) :=
    ⟨Function.LeftInverse.injective (spectralPencil_resolventToDomain hp φ w hw),
      Function.RightInverse.surjective (resolventToDomain_spectralPencil hp φ w hw)⟩
  rw [← spectralPencil_comp_resolventToDomain hp φ w z hw,
    ContinuousLinearMap.isUnit_iff_bijective]
  exact (Function.Bijective.of_comp_iff (spectralPencil hp φ z) hR).symm

/-- The spectral transformation to the nonzero spectrum of a compact resolvent. -/
theorem mem_periodicSpectrum_iff_resolvent_spectrum (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (hzw : z ≠ w) :
    z ∈ periodicSpectrum hp φ ↔ (w - z)⁻¹ ∈ spectrum ℂ (resolvent hp φ w) := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have heq : 1 + (z - w) • resolvent hp φ w =
      (Units.mk0 (w - z) hwz) •
        ((w - z)⁻¹ • (1 : PairSpace p →L[ℂ] PairSpace p) - resolvent hp φ w) := by
    rw [Units.smul_def, Units.val_mk0, smul_sub, smul_smul, mul_inv_cancel₀ hwz, one_smul]
    module
  change ¬ z ∈ resolventSet hp φ ↔ _
  rw [mem_resolventSet_iff_shift_isUnit hp φ w z hw, heq, isUnit_smul_iff,
    spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]

/-- Every bounded ball contains only finitely many periodic spectral parameters. -/
theorem finite_periodicSpectrum_inter_closedBall (hp : p ≠ ⊤) (φ : PairSpace p)
    (r : ℝ) : Set.Finite (periodicSpectrum hp φ ∩ Metric.closedBall 0 r) := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  let C : ℝ := ‖w‖ + |r| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfinite := NLS.CompactSpectrum.finite_spectrum_norm_ge (resolvent hp φ w)
    (isCompactOperator_resolvent hp φ w) (show 0 < C⁻¹ by positivity)
  apply Set.Finite.of_injOn (f := fun z : ℂ => (w - z)⁻¹) (t :=
    {μ : ℂ | μ ∈ spectrum ℂ (resolvent hp φ w) ∧ C⁻¹ ≤ ‖μ‖}) _ _ hfinite
  · intro z hz
    have hzw : z ≠ w := by rintro rfl; exact hz.1 hw
    refine ⟨(mem_periodicSpectrum_iff_resolvent_spectrum hp φ w z hw hzw).mp hz.1, ?_⟩
    have hzbound : ‖z‖ ≤ r := by simpa using hz.2
    have hden : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzw.symm)
    have hb : ‖w - z‖ ≤ C := (norm_sub_le w z).trans (by dsimp [C]; linarith [le_abs_self r])
    rw [norm_inv]
    exact inv_anti₀ hden hb
  · intro z hz z' hz' heq
    exact sub_right_inj.mp (inv_injective heq)

/-- Any bounded part of the periodic spectrum is finite. -/
theorem finite_periodicSpectrum_inter_of_isBounded (hp : p ≠ ⊤) (φ : PairSpace p)
    {K : Set ℂ} (hK : Bornology.IsBounded K) : Set.Finite (periodicSpectrum hp φ ∩ K) := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall (0 : ℂ)
  exact (finite_periodicSpectrum_inter_closedBall hp φ r).subset (Set.inter_subset_inter_right _ hr)

/-- The periodic spectrum carries the discrete subspace topology. -/
theorem discreteTopology_periodicSpectrum (hp : p ≠ ⊤) (φ : PairSpace p) :
    DiscreteTopology (periodicSpectrum hp φ) := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro K hK
  have hfin := finite_periodicSpectrum_inter_of_isBounded hp φ hK.isBounded
  exact Set.Finite.of_injOn
    (fun z hz => show (z : ℂ) ∈ periodicSpectrum hp φ ∩ K from ⟨z.property, hz⟩)
    (fun _ _ _ _ h => Subtype.ext h) hfin

/-- The eigenspace in the one-derivative domain. -/
def periodicEigenspace (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : Submodule ℂ (Domain p) :=
  (spectralPencil hp φ z).toLinearMap.ker

@[simp] theorem mem_periodicEigenspace (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ)
    (f : Domain p) :
    f ∈ periodicEigenspace hp φ z ↔ operator hp φ f = z • domainInclusion f := by
  change z • domainInclusion f - operator hp φ f = 0 ↔ _
  exact sub_eq_zero.trans eq_comm

/-- Domain eigenvectors become eigenvectors of the compact resolvent with the
reciprocal eigenvalue. This statement also permits the zero vector. -/
theorem inclusion_mem_resolvent_eigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (w z : ℂ) (hw : w ∈ resolventSet hp φ) (hzw : z ≠ w)
    (f : Domain p) (hf : f ∈ periodicEigenspace hp φ z) :
    domainInclusion f ∈ Module.End.eigenspace
      ((resolvent hp φ w).toLinearMap) (w - z)⁻¹ := by
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
  have hP : spectralPencil hp φ w f = (w - z) • domainInclusion f := by
    rw [spectralPencil_apply, (mem_periodicEigenspace hp φ z f).mp hf, sub_smul]
  have hR := resolventToDomain_spectralPencil hp φ w hw f
  rw [hP, map_smul] at hR
  have hinc := congrArg (domainInclusion (p := p)) hR
  rw [map_smul] at hinc
  apply Module.End.mem_eigenspace_iff.mpr
  change resolvent hp φ w (domainInclusion f) = (w - z)⁻¹ • domainInclusion f
  change (w - z) • resolvent hp φ w (domainInclusion f) = domainInclusion f at hinc
  calc
    resolvent hp φ w (domainInclusion f) =
        (w - z)⁻¹ • ((w - z) • resolvent hp φ w (domainInclusion f)) := by
      rw [inv_smul_smul₀ hwz]
    _ = _ := by rw [hinc]

/-- Every periodic spectral point is an eigenvalue, and conversely. -/
theorem mem_periodicSpectrum_iff_exists_eigenvector (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) : z ∈ periodicSpectrum hp φ ↔
      ∃ f : Domain p, f ≠ 0 ∧ operator hp φ f = z • domainInclusion f := by
  constructor
  · intro hz
    obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
    have hzw : z ≠ w := by rintro rfl; exact hz hw
    have hwz : w - z ≠ 0 := sub_ne_zero.mpr hzw.symm
    have hμ := (isCompactOperator_resolvent hp φ w).hasEigenvalue_iff_mem_spectrum
      (inv_ne_zero hwz)
    obtain ⟨a, ha⟩ := (hμ.mpr
      ((mem_periodicSpectrum_iff_resolvent_spectrum hp φ w z hw hzw).mp hz)).exists_hasEigenvector
    have heigen : resolvent hp φ w a = (w - z)⁻¹ • a := ha.apply_eq_smul
    refine ⟨resolventToDomain hp φ w a, ?_, ?_⟩
    · intro hzero
      have hP := spectralPencil_resolventToDomain hp φ w hw a
      rw [hzero, map_zero] at hP
      exact ha.2 hP.symm
    · have hP := spectralPencil_resolventToDomain hp φ w hw a
      rw [spectralPencil_apply] at hP
      have hinc : (w - z) • domainInclusion (resolventToDomain hp φ w a) = a := by
        change (w - z) • resolvent hp φ w a = a
        rw [heigen, smul_inv_smul₀ hwz]
      rw [sub_smul] at hinc
      exact sub_right_inj.mp (hP.trans hinc.symm)
  · rintro ⟨f, hf0, hf⟩ hz
    apply hf0
    apply hz.injective
    simp only [spectralPencil_apply, hf, sub_self, map_zero]

/-- Periodic eigenspaces have finite geometric multiplicity. Generalized
eigenspaces and algebraic multiplicities are separate constructions. -/
theorem finiteDimensional_periodicEigenspace (hp : p ≠ ⊤) (φ : PairSpace p)
    (z : ℂ) (hz : z ∈ periodicSpectrum hp φ) :
    FiniteDimensional ℂ (periodicEigenspace hp φ z) := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  have hzw : z ≠ w := by rintro rfl; exact hz hw
  let W := Module.End.eigenspace ((resolvent hp φ w).toLinearMap) (w - z)⁻¹
  let : FiniteDimensional ℂ W := NLS.CompactSpectrum.finiteDimensional_eigenspace
    (resolvent hp φ w) (isCompactOperator_resolvent hp φ w) (inv_ne_zero (sub_ne_zero.mpr hzw.symm))
  let F : periodicEigenspace hp φ z →ₗ[ℂ] W :=
    { toFun := fun f => ⟨domainInclusion f,
        inclusion_mem_resolvent_eigenspace hp φ w z hw hzw f f.property⟩
      map_add' := fun f g => Subtype.ext (map_add domainInclusion (f : Domain p) (g : Domain p))
      map_smul' := fun c f => Subtype.ext (map_smul domainInclusion c (f : Domain p)) }
  exact FiniteDimensional.of_injective F (fun f g h =>
    Subtype.ext (domainInclusion_injective (congrArg Subtype.val h)))

end NLS.ZakharovShabat
