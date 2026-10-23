import NLS.ZakharovShabat.SourceSpatialReflection
import NLS.ZakharovShabat.SourceSignedDirichletParametrization

/-! # Reflection symmetry and endpoint Dirichlet data

The actual reflection preserves every indexed periodic endpoint and every
ordinary boundary root, and reverses each Dirichlet sign. Signed Dirichlet
uniqueness then characterizes the symmetric slice by endpoint data. Every
choice of periodic endpoints has a unique symmetric Hilbert representative
in the original isospectral set.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source reflection restricted to the real-type locus. -/
def realSourceSpatialReflection (φ : realTypeSourceSubmodule p) : realTypeSourceSubmodule p :=
  ⟨sourceSpatialReflection φ.val,sourceSpatialReflection_realType φ.val φ.property⟩

@[simp] theorem realSourceSpatialReflection_val (φ : realTypeSourceSubmodule p) :
    (realSourceSpatialReflection φ).val = sourceSpatialReflection φ.val := rfl

@[simp] theorem realSourceSpatialReflection_involutive (φ : realTypeSourceSubmodule p) :
    realSourceSpatialReflection (realSourceSpatialReflection φ) = φ := by
  apply Subtype.ext
  exact sourceSpatialReflection_involutive φ.val

/-- Reflection preserves the actual periodic spectrum with algebraic multiplicities. -/
theorem realSourceSpatialReflection_mem_isospectralSet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    realSourceSpatialReflection φ ∈ sourceIsospectralSet hp φ := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ _).mpr
  funext z
  exact sourceDiscriminant_spatialReflection hp hp1 φ.val z

/-- Every signed-index periodic endpoint is unchanged by reflection. -/
theorem sourceCanonicalPeriodicEndpoints_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceSpatialReflection φ.val))
        (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceSpatialReflection φ.val))
        (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) := by
  have h := realSourceSpatialReflection_mem_isospectralSet hp hp1 φ
  exact canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 _ _
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2

/-- Both actual ordinary boundary sequences retain their original indices. -/
theorem sourceCanonicalBoundaryRoots_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 b (sourceSpatialReflection φ.val) n =
      canonicalPeriodOneBoundaryRoots hp hp1 b φ.val n := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 b (sourceSpatialReflection φ.val) n
  have hz : periodOneBoundaryCharacteristic hp hp1 b (sourceSpatialReflection φ.val) μ = 0 :=
    (periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b _ _).mpr
      ((canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b _ _).mpr ⟨n,rfl⟩)
  rw [sourceBoundaryCharacteristic_spatialReflection] at hz
  obtain ⟨k,hk⟩ := (canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ.val μ).mp
    ((periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b φ.val μ).mp hz)
  have hn := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b _
    (sourceSpatialReflection_realType φ.val φ.property) n
  have he := sourceCanonicalPeriodicEndpoints_spatialReflection hp hp1 φ
  rw [he.1,he.2] at hn
  have hm := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ.val φ.property k
  rw [hk] at hm
  have hkn : k = n := by
    rcases lt_trichotomy k n with h | h | h
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      exact False.elim ((not_lt_of_ge (hn.1.trans hm.2)) hs)
    · exact h
    · have hs := canonicalPeriodicRight_re_lt_left_of_lt hp hp1 _
        (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) h
      exact False.elim ((not_lt_of_ge (hm.1.trans hn.2)) hs)
  exact hk.symm.trans (congrArg (canonicalPeriodOneBoundaryRoots hp hp1 b φ.val) hkn)

/-- Reflection reverses the literal Dirichlet sign, including the zero endpoint sign. -/
theorem sourceDirichletSign_spatialReflection (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceDirichletSign hp hp1 (realSourceSpatialReflection φ) n =
      -sourceDirichletSign hp hp1 φ n := by
  simp only [sourceDirichletSign,realSourceSpatialReflection_val,
    sourceCanonicalBoundaryRoots_spatialReflection hp hp1 .dirichlet φ,
    sourceAntiDiscriminant_spatialReflection,neg_re]
  exact Left.sign_neg _

/-- The actual reflection-fixed slice is exactly the zero-sign Dirichlet locus. -/
theorem realSourceSpatialReflection_eq_self_iff_signs_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    realSourceSpatialReflection φ = φ ↔ ∀ n, sourceDirichletSign hp hp1 φ n = 0 := by
  constructor
  · intro h n
    have he := sourceDirichletSign_spatialReflection hp hp1 φ n
    rw [h] at he
    cases hs : sourceDirichletSign hp hp1 φ n <;> simp_all
  · intro h
    apply source_eq_of_isospectral_dirichlet_roots_signs hp hp1 φ _
      (realSourceSpatialReflection_mem_isospectralSet hp hp1 φ)
    · exact sourceCanonicalBoundaryRoots_spatialReflection hp hp1 .dirichlet φ
    · intro n
      rw [sourceDirichletSign_spatialReflection,h n,neg_zero]

/-- The literal zero sign occurs exactly when the actual Dirichlet root is at an endpoint. -/
theorem sourceDirichletSign_eq_zero_iff_endpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceDirichletSign hp hp1 φ n = 0 ↔
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n).re =
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re ∨
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n).re =
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
  exact sourceSignedDirichletSheet_sign_zero_iff_endpoint hp hp1 φ n
    (sourceDirichletSignedSheetHomeomorph hp hp1 φ n
      ⟨sourceDirichletTerminalData hp hp1 φ n,sourceDirichletTerminalData_mem_sheet hp hp1 φ n⟩)

/-- The symmetric source slice is characterized by endpoint Dirichlet roots at every index. -/
theorem realSourceSpatialReflection_eq_self_iff_endpoints (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) :
    realSourceSpatialReflection φ = φ ↔ ∀ n,
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n).re =
        (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re ∨
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val n).re =
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
  rw [realSourceSpatialReflection_eq_self_iff_signs_zero hp hp1]
  exact forall_congr' (sourceDirichletSign_eq_zero_iff_endpoint hp hp1 φ)

local instance sourceReflectionSymmetry_factTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- Every choice of actual periodic endpoints has a unique reflection-symmetric Hilbert
representative in the original isospectral set, with no finite-gap assumption. -/
theorem existsUnique_symmetric_source_with_endpoint_dirichletData
    (φ : realTypeSourceSubmodule 2) (μ : ℤ → ℝ)
    (hμ : ∀ n,
      μ n = (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re ∨
      μ n = (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re) :
    ∃! ψ : sourceIsospectralSet (by simp) φ,
      realSourceSpatialReflection ψ.val = ψ.val ∧ ∀ n,
        canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet ψ.val.val n = (μ n : ℂ) := by
  have hmem n : μ n ∈ Icc
      (canonicalPeriodicLeft (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
      (canonicalPeriodicRight (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n).re := by
    have h := canonicalPeriodOneBoundaryRoots_mem_gap (by simp) (by norm_num) .dirichlet φ.val φ.property n
    have hle := h.1.trans h.2
    rcases hμ n with he | he
    · simpa only [he] using (show _ ∈ Icc _ _ from ⟨le_rfl,hle⟩)
    · simpa only [he] using (show _ ∈ Icc _ _ from ⟨hle,le_rfl⟩)
  obtain ⟨ψ,hψ,huniq⟩ := existsUnique_isospectral_source_with_signed_dirichletData
    φ μ (fun _ => 0) hmem (fun n => ⟨fun _ => hμ n,fun _ => rfl⟩)
  refine ⟨ψ,⟨?_,fun n => (hψ n).1⟩,?_⟩
  · exact (realSourceSpatialReflection_eq_self_iff_signs_zero (by simp) (by norm_num) ψ.val).mpr
      (fun n => (hψ n).2)
  · intro χ hχ
    apply huniq χ
    intro n
    exact ⟨hχ.2 n,(realSourceSpatialReflection_eq_self_iff_signs_zero (by simp) (by norm_num) χ.val).mp hχ.1 n⟩

end NLS.ZakharovShabat
