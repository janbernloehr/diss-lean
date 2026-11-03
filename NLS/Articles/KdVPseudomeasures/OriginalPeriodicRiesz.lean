import NLS.Articles.KdVPseudomeasures.OriginalComplexDirichletMultiplicity
import NLS.KdV.SingularHillRieszContinuous
import NLS.KdV.SingularHillRieszBilinear
import NLS.KdV.SingularHillRieszPhysicalGreen

/-! The original periodic projection P_(n,q), on the literal source circle
and the full source-normalized periodic L2 space. Its algebraic range includes
all complex associated vectors. Circle validity, high-energy rank two and
quantitative source C.4 convergence remain separate proof obligations. -/
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Actual periodic source projection, retaining the original complex distribution. -/
def originalPeriodicRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    CircleL2 →L[ℂ] CircleL2 :=
  singularHillL2RieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- The same source contour, with continuous representatives. -/
def originalPeriodicContinuousRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    CircleL2 →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  singularHillContinuousRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- The same actual source projection into the physical essential-supremum space. -/
def originalPeriodicLinfRieszProjection (q : OriginalComplexHminusOnePotential) (n : ℕ+) :
    CircleL2 →L[ℂ] Lp ℂ ⊤ (AddCircle.haarAddCircle (T := (2:ℝ))) :=
  singularHillLinfRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)

/-- Source P_(n,q) is an actual bounded idempotent on every valid literal circle. -/
theorem isIdempotentElem_originalPeriodicRieszProjection
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet q.val) :
    IsIdempotentElem (originalPeriodicRieszProjection q n) :=
  isIdempotentElem_singularHillL2RieszProjection q.val _ _
    (by exact_mod_cast n.property) hc

/-- Every valid original source contour has a finite-dimensional physical range. -/
theorem finiteDimensional_originalPeriodicRieszProjection_range
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet q.val) :
    FiniteDimensional ℂ (originalPeriodicRieszProjection q n).range :=
  finiteDimensional_singularHillL2RieszProjection_range q.val _ _
    (by exact_mod_cast n.property) hc

/-- Its physical range has exactly the native algebraic rank. -/
theorem finrank_originalPeriodicRieszProjection_range
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet q.val) :
    Module.finrank ℂ (originalPeriodicRieszProjection q n).range =
      Module.finrank ℂ (singularHillRieszProjection q.val (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)).range :=
  finrank_singularHillL2RieszProjection_range q.val _ _
    (by exact_mod_cast n.property) hc

/-- The entire physical range maps to ALL enclosed original algebraic root spaces. -/
theorem originalPeriodicRieszProjection_range_roots
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet q.val) :
    Submodule.map singularHillL2BaseInclusion.toLinearMap (originalPeriodicRieszProjection q n).range =
      ⨆ z : ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ), singularHillRootSpaceTop q.val z.val :=
  singularHillL2RieszProjection_range_roots q.val _ _
    (by exact_mod_cast n.property) hc

/-- Actual source L-infinity and L2 projection outputs coincide almost everywhere. -/
theorem originalPeriodicLinfRieszProjection_same_ae
    (q : OriginalComplexHminusOnePotential) (n : ℕ+) (F : CircleL2) :
    originalPeriodicLinfRieszProjection q n F =ᵐ[AddCircle.haarAddCircle]
      originalPeriodicRieszProjection q n F :=
  singularHillLinfRieszProjection_same_ae q.val _ _ F

/-- The original continuous projection has exactly the original physical L2 class. -/
theorem originalPeriodicContinuousRieszProjection_toLp
    (q : OriginalComplexHminusOnePotential) (n : ℕ+) (F : CircleL2) :
    circleContinuousToLp 2 (originalPeriodicContinuousRieszProjection q n F) =
      originalPeriodicRieszProjection q n F :=
  singularHillContinuousRieszProjection_toLp q.val _ _ F

/-- The actual periodic source projection has complex bilinear Green symmetry
on the entire source-normalized L2 space, using literal physical integrals. -/
theorem originalPeriodicRieszProjection_physical_bilinear
    (q : OriginalComplexHminusOnePotential) (n : ℕ+)
    (hc : sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ⊆ singularHillResolventSet q.val)
    (F G : CircleL2) :
    (∫ x in (0:ℝ)..2, circlePullback F x *
      circlePullback (originalPeriodicRieszProjection q n G) x) =
    ∫ x in (0:ℝ)..2, circlePullback (originalPeriodicRieszProjection q n F) x *
      circlePullback G x :=
  singularHillL2RieszProjection_physical_bilinear q.val _ _
    (by exact_mod_cast n.property.le) hc F G

end NLS.Articles.KdVPseudomeasures
