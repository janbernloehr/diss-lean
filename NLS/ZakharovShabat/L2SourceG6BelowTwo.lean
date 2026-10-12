import NLS.ZakharovShabat.L2AntiDiscriminantBelowTwo

/-! # Physical G.6 errors at both boundary sequences below two

Complex H1 sources have summable actual anti-discriminant gradient errors
in the original conjugate pair norm. Both boundary conditions and every
signed index are included, with no reality or simplicity premise.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restricting the Hilbert estimate works for complex H1 sources as well. -/
theorem memlp_source_antiDiscriminantCotangent_error_below_two_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ) = domainInclusion a)
    (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => sourceAntiDiscriminantCotangent hp hp1
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ-
      sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := memlp_hilbert_antiDiscriminantCotangent_error_outer p.toReal hs
    (CoeffPair.exponentInclusion hp2 φ) a ha b
  rw [ENNReal.ofReal_toReal hp] at h
  have hr := memlp_cotangent_exponent_restriction hp2 _ h
  convert hr using 1
  funext n
  rw [sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2,
    sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2,
    canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 b φ,map_zero]
  rfl

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [q.HolderConjugate p]

/-- Both boundary sequences have outer-lp physical G.6 coefficients in the
original source's finite conjugate norm, including the finite spectral head. -/
theorem sourceG6_below_two_physical_complex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ) = domainInclusion a)
    (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => sourceG6AntiDiscriminantCotangentCoefficients (q := q) hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ((Real.pi : ℂ)*n)) p ∧ ∀ n : ℤ,
      L2GradientFourierRealizes
        (l2AntiDiscriminantGradientRemainder (sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ))
          (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ((Real.pi : ℂ)*n))
        (sourceG6AntiDiscriminantCotangentCoefficients (q := q) hp hp1 φ
          (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ((Real.pi : ℂ)*n)) := by
  refine ⟨?_,fun n => sourceG6AntiDiscriminantCotangentCoefficients_realizes_below_two hp hp1 hp2 φ _ _⟩
  have hq : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).mpr hp1.ne'
  have h := CoeffPair.memlp_conjugateGradient (q := q) hp hq _
    (memlp_source_antiDiscriminantCotangent_error_below_two_complex hp hp1 hp2 φ a ha b)
  apply Memℓp.of_norm
  simpa only [norm_sourceG6AntiDiscriminantCotangentCoefficients] using h.norm

/-- On an H1 source the actual cotangent vector equals the already constructed
G.6 physical coefficient vector, not merely a sequence with the same bound. -/
theorem sourceG6AntiDiscriminantCotangentCoefficients_eq_sobolev
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ) = domainInclusion a) (z w : ℂ) :
    sourceG6AntiDiscriminantCotangentCoefficients (q := q) hp hp1 φ z w =
      sourceG6AntiDiscriminantCoefficients
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top) (classicalSobolevPotential a) z w := by
  have hΦ : sourcePhysicalL2 (CoeffPair.exponentInclusion hp2 φ) =
      continuousPotentialL2Class (classicalSobolevPotential a) :=
    physicalRestrictionL2_of_continuous _ _
      (physicalBase_source_sobolev_compatibility _ a ha)
  have h := sourceG6AntiDiscriminantCotangentCoefficients_realizes_below_two (q := q) hp hp1 hp2 φ z w
  rw [hΦ] at h
  exact h.unique (sourceG6AntiDiscriminantCoefficients_realizes_l2 _ _ _ _)

end NLS.ZakharovShabat
