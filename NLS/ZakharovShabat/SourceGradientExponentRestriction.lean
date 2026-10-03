import NLS.ZakharovShabat.SourceHilbertGradientOuterSummability
import NLS.ZakharovShabat.SourceAngularEtaPhaseExponent

/-! # Restricting actual gradient estimates below the Hilbert exponent

Coefficient inclusion preserves the midpoint, boundary roots, and fixed
spectral anti-discriminant. Differentiating these identities restricts the
full cotangents. Independent outer Hilbert estimates then give G.6 and G.7
in each finite source space with exponent strictly between one and two.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The free half-wave functional restricts without changing coefficients. -/
theorem sourceFreeDirichletCotangent_exponent (hpq : p ≤ q) (n : ℤ) :
    sourceFreeDirichletCotangent p n =
      (sourceFreeDirichletCotangent q n).comp (CoeffPair.exponentInclusion hpq) := by
  ext h
  rfl

/-- Actual canonical midpoint derivatives restrict across finite exponents. -/
theorem fderiv_canonicalPeriodicMidpoint_source_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (φ : realTypeSourceLocus p) (n : ℤ) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ.val =
    (fderiv ℂ (fun ψ : CoeffPair q => canonicalPeriodicMidpoint hq hq1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
      (CoeffPair.exponentInclusion hpq φ.val)).comp (CoeffPair.exponentInclusion hpq) := by
  have heq : (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) =
      (fun ψ : CoeffPair q => canonicalPeriodicMidpoint hq hq1
        (periodOnePotential ψ) (periodOnePotential_mem ψ) n) ∘ CoeffPair.exponentInclusion hpq := by
    funext ψ
    exact canonicalPeriodicMidpoint_source_exponent hp hq hp1 hq1 hpq ψ n
  obtain ⟨W,_,_,hreal,hAn⟩ := exists_global_source_analytic_midpoint_squaredGap hq hq1
  rw [heq,fderiv_comp φ.val
    (hAn _ (hreal (realTypeSourceExponentInclusion hpq φ).property) n).1.differentiableAt
    (CoeffPair.exponentInclusion hpq).differentiableAt,ContinuousLinearMap.fderiv]

/-- Restriction by a fixed bounded inclusion preserves any outer summability exponent. -/
theorem memlp_cotangent_exponent_restriction {r : ℝ≥0∞} (hpq : p ≤ q)
    (L : ℤ → CoeffPair q →L[ℂ] ℂ) (hL : Memℓp L r) :
    Memℓp (fun n => (L n).comp (CoeffPair.exponentInclusion hpq)) r := by
  apply (hL.norm.const_mul ‖CoeffPair.exponentInclusion hpq‖).mono
  intro n
  simpa only [mul_comm] using (L n).opNorm_comp_le (CoeffPair.exponentInclusion hpq)

/-- G.7 for actual midpoint derivatives below the Hilbert exponent. -/
theorem memlp_source_midpoint_fderiv_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) φ.val) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := memlp_hilbert_midpoint_fderiv_outer p.toReal hs
    (CoeffPair.exponentInclusion hp2 φ.val) (realTypeSourceExponentInclusion hp2 φ).property a ha
  rw [ENNReal.ofReal_toReal hp] at h
  have hr := memlp_cotangent_exponent_restriction hp2 _ h
  convert hr using 1
  funext n
  exact fderiv_canonicalPeriodicMidpoint_source_exponent hp (by simp) hp1 (by norm_num) hp2 φ n

/-- G.7 for actual Dirichlet derivative errors below the Hilbert exponent. -/
theorem memlp_source_dirichlet_fderiv_error_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a) :
    Memℓp (fun n : ℤ => fderiv ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) φ.val-
      sourceFreeDirichletCotangent p n) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := memlp_hilbert_dirichlet_fderiv_error_outer p.toReal hs
    (CoeffPair.exponentInclusion hp2 φ.val) (realTypeSourceExponentInclusion hp2 φ).property a ha
  rw [ENNReal.ofReal_toReal hp] at h
  have hr := memlp_cotangent_exponent_restriction hp2 _ h
  convert hr using 1
  funext n
  rw [fderiv_canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 .dirichlet n φ,
    sourceFreeDirichletCotangent_exponent hp2]
  rfl

/-- G.6 at either actual boundary sequence below the Hilbert exponent. -/
theorem memlp_source_antiDiscriminantCotangent_error_below_two
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : realTypeSourceLocus p) (a : Domain 2)
    (ha : periodOnePotential (CoeffPair.exponentInclusion hp2 φ.val) = domainInclusion a)
    (b : BoundaryCondition) :
    Memℓp (fun n : ℤ => sourceAntiDiscriminantCotangent hp hp1
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ.val n) φ.val-
      sourceAntiDiscriminantCotangent hp hp1 ((Real.pi : ℂ)*n) 0) p := by
  have hs : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have h := memlp_hilbert_antiDiscriminantCotangent_error_outer p.toReal hs
    (CoeffPair.exponentInclusion hp2 φ.val) a ha b
  rw [ENNReal.ofReal_toReal hp] at h
  have hr := memlp_cotangent_exponent_restriction hp2 _ h
  convert hr using 1
  funext n
  rw [sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2,
    sourceAntiDiscriminantCotangent_exponent hp (by simp) hp1 (by norm_num) hp2,
    canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) hp2 b φ.val,map_zero]
  rfl

end NLS.ZakharovShabat
