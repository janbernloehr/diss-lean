import NLS.ZakharovShabat.SourceBirkhoffCoordinateDifferential
import NLS.ZakharovShabat.SourceCorollary13_2Regular
import NLS.Poisson.RegularSourceCotangentAlgebra

/-! # Regular cotangents of the actual rectangular coordinates

At an open real gap, the action-angle derivative formulas construct
square-summable Fourier coefficients of each rectangular cotangent.
This is valid throughout the finite exponent range, including below two.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Full rectangular source derivatives on the actual open-gap domain. -/
theorem birkhoffXY_fderiv
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val =
      (sourceBirkhoffX hp hp1 n s φ.val / (2*sourceComplexAction hp hp1 n φ.val)) •
        fderiv ℂ (sourceComplexAction hp hp1 n) φ.val +
          (-sourceBirkhoffY hp hp1 n s φ.val) • sourceAngularThetaDifferential hp hp1 n s φ.val ∧
    fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val =
      (sourceBirkhoffY hp hp1 n s φ.val / (2*sourceComplexAction hp hp1 n φ.val)) •
        fderiv ℂ (sourceComplexAction hp hp1 n) φ.val +
          sourceBirkhoffX hp hp1 n s φ.val • sourceAngularThetaDifferential hp hp1 n s φ.val := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,E⟩ := D.local_charts n φ.val (D.real_subset φ.property) hn
  exact E.birkhoffXY_fderiv_of_realType
    ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)) φ.val hφU φ.property

/-- Regular cotangent of the actual `x` coordinate at an open real gap. -/
def birkhoffXRegularCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    RegularSourceCotangent p :=
  ((sourceActionRegularCotangent hp hp1 n φ).smul
    (sourceBirkhoffX hp hp1 n s φ.val / (2*sourceComplexAction hp hp1 n φ.val))).add
      ((D.thetaRegularCotangent n φ hn).smul (-sourceBirkhoffY hp hp1 n s φ.val))

/-- Regular cotangent of the actual `y` coordinate at an open real gap. -/
def birkhoffYRegularCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    RegularSourceCotangent p :=
  ((sourceActionRegularCotangent hp hp1 n φ).smul
    (sourceBirkhoffY hp hp1 n s φ.val / (2*sourceComplexAction hp hp1 n φ.val))).add
      ((D.thetaRegularCotangent n φ hn).smul (sourceBirkhoffX hp hp1 n s φ.val))

@[simp] theorem birkhoffXRegularCotangent_toCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (D.birkhoffXRegularCotangent n φ hn).toCotangent = fderiv ℂ (sourceBirkhoffX hp hp1 n s) φ.val := by
  simp only [birkhoffXRegularCotangent,RegularSourceCotangent.add,RegularSourceCotangent.smul,
    sourceActionRegularCotangent_toCotangent,D.thetaRegularCotangent_toCotangent]
  exact (D.birkhoffXY_fderiv n φ hn).1.symm

@[simp] theorem birkhoffYRegularCotangent_toCotangent
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    (D.birkhoffYRegularCotangent n φ hn).toCotangent = fderiv ℂ (sourceBirkhoffY hp hp1 n s) φ.val := by
  simp only [birkhoffYRegularCotangent,RegularSourceCotangent.add,RegularSourceCotangent.smul,
    sourceActionRegularCotangent_toCotangent,D.thetaRegularCotangent_toCotangent]
  exact (D.birkhoffXY_fderiv n φ hn).2.symm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
