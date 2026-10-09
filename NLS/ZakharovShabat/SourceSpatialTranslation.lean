import NLS.ZakharovShabat.PeriodicTranslation
import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness
import NLS.ZakharovShabat.SourceFiniteGap

/-! # Spatial translation preserves the actual indexed source gaps

The period-one translation group uses the original source pair norm. It
preserves real type and every canonical endpoint, with no relabeling or
change of cutoff. Thus an entire translation orbit stays in the same
finite-gap stratum.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation by `t` in the period-one source space, with its original norm. -/
def sourceSpatialTranslation (t : ℝ) : CoeffPair p ≃ₗᵢ[ℂ] CoeffPair p :=
  (Coeff.spatialTranslation (2*Real.pi) t).withLpProdCongr p
    (Coeff.spatialTranslation (2*Real.pi) t)

@[simp] theorem sourceSpatialTranslation_fst (t : ℝ) (φ : CoeffPair p) :
    (sourceSpatialTranslation t φ).fst = Coeff.spatialTranslation (2*Real.pi) t φ.fst := rfl

@[simp] theorem sourceSpatialTranslation_snd (t : ℝ) (φ : CoeffPair p) :
    (sourceSpatialTranslation t φ).snd = Coeff.spatialTranslation (2*Real.pi) t φ.snd := rfl

@[simp] theorem sourceSpatialTranslation_zero (φ : CoeffPair p) :
    sourceSpatialTranslation 0 φ = φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp

/-- Translation is a group action, including negative displacements. -/
theorem sourceSpatialTranslation_add (t s : ℝ) (φ : CoeffPair p) :
    sourceSpatialTranslation t (sourceSpatialTranslation s φ) =
      sourceSpatialTranslation (t+s) φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp [Coeff.spatialTranslation_add]

/-- Joint norm continuity holds at every finite source exponent. -/
theorem continuous_sourceSpatialTranslation (hp : p ≠ ⊤) :
    Continuous (fun x : ℝ × CoeffPair p => sourceSpatialTranslation x.1 x.2) := by
  exact (CoeffPair.toMax p).symm.continuous.comp
    (((Coeff.continuous_spatialTranslation hp (2*Real.pi)).comp
      (continuous_fst.prodMk ((WithLp.continuous_fst p _ _).comp continuous_snd))).prodMk
    ((Coeff.continuous_spatialTranslation hp (2*Real.pi)).comp
      (continuous_fst.prodMk ((WithLp.continuous_snd p _ _).comp continuous_snd))))

/-- The source and operator translations agree under the even-frequency embedding. -/
theorem periodOnePotential_spatialTranslation (t : ℝ) (φ : CoeffPair p) :
    periodOnePotential (sourceSpatialTranslation t φ) =
      pairSpatialTranslation t (periodOnePotential φ) := by
  apply Prod.ext <;> exact Coeff.periodDouble_spatialTranslation Real.pi t _

/-- Translation preserves the conjugate-reflection relation defining real type. -/
theorem sourceSpatialTranslation_realType (t : ℝ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (CoeffPair.toMax p (sourceSpatialTranslation t φ)) := by
  intro n
  change Complex.exp ((t*((2*Real.pi)*n) : ℝ)*Complex.I)*φ.snd n =
    conj (Complex.exp ((t*((2*Real.pi)*(-n : ℤ)) : ℝ)*Complex.I)*φ.fst (-n))
  have hn : φ.snd n = conj (φ.fst (-n)) := hφ n
  rw [hn, map_mul, ← Complex.exp_conj]
  simp [map_ofNat]

/-- The actual periodic source spectrum is invariant under spatial translation. -/
theorem sourcePeriodicSpectrum_spatialTranslation (hp : p ≠ ⊤)
    (t : ℝ) (φ : CoeffPair p) :
    periodicSpectrum hp (periodOnePotential (sourceSpatialTranslation t φ)) =
      periodicSpectrum hp (periodOnePotential φ) := by
  rw [periodOnePotential_spatialTranslation, periodicSpectrum_spatialTranslation]

/-- Translation preserves every source eigenvalue's actual algebraic multiplicity. -/
theorem sourcePeriodicAlgebraicMultiplicity_spatialTranslation (hp : p ≠ ⊤)
    (t : ℝ) (φ : CoeffPair p) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential (sourceSpatialTranslation t φ)) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential φ) z := by
  rw [periodOnePotential_spatialTranslation, periodicAlgebraicMultiplicity_spatialTranslation]

/-- Both complete canonical endpoint sequences are unchanged, with their original indices. -/
theorem sourceCanonicalPeriodicEndpoints_spatialTranslation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℝ) (φ : CoeffPair p) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential (sourceSpatialTranslation t φ))
        (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential (sourceSpatialTranslation t φ))
        (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) :=
  canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 _ _ _ _
    (sourcePeriodicSpectrum_spatialTranslation hp t φ)
    (sourcePeriodicAlgebraicMultiplicity_spatialTranslation hp t φ)

/-- Every actual indexed gap, including all central gaps, is translation invariant. -/
theorem sourceCanonicalPeriodicGap_spatialTranslation (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℝ) (φ : CoeffPair p) (n : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential (sourceSpatialTranslation t φ))
        (periodOnePotential_mem _) n =
      canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_spatialTranslation hp hp1 t φ
  simp only [canonicalPeriodicGap, hl, hr]

/-- A closed-gap tail keeps exactly the same cutoff throughout the translation orbit. -/
theorem sourceSpatialTranslation_closedGapTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℝ) (φ : CoeffPair p) (K : ℕ)
    (hclosed : ∀ n : ℤ, K ≤ n.natAbs → canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    ∀ n : ℤ, K ≤ n.natAbs → canonicalPeriodicGap hp hp1
      (periodOnePotential (sourceSpatialTranslation t φ)) (periodOnePotential_mem _) n = 0 := by
  intro n hn
  rw [sourceCanonicalPeriodicGap_spatialTranslation]
  exact hclosed n hn

/-- A real finite-gap source stays real finite-gap under every spatial translation. -/
theorem sourceSpatialTranslation_mem_sourceFiniteGapLocus (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℝ) (φ : realTypeSourceLocus p) (hφ : φ ∈ sourceFiniteGapLocus hp hp1) :
    (⟨sourceSpatialTranslation t φ.val, sourceSpatialTranslation_realType t φ.val φ.property⟩ :
      realTypeSourceLocus p) ∈ sourceFiniteGapLocus hp hp1 := by
  simpa only [sourceFiniteGapLocus, Set.mem_ofPred_eq,
    sourceCanonicalPeriodicGap_spatialTranslation] using hφ

end NLS.ZakharovShabat
