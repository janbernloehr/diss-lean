import NLS.ZakharovShabat.ClassicalSeparatedCanonicalIdentity

open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z =
      analyticOrderAt (b.characteristic (by simp)
        (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
        (intervalPotentialCoefficients_mem _)) z :=
  analyticOrderAt_classicalSeparated_eq_characteristic b Φ hΦ z

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    b.characteristic (by simp)
      (intervalPotentialCoefficients (intervalL2OfFunction (extend Φ) hΦ))
      (intervalPotentialCoefficients_mem _) z =
        classicalSeparatedCharacteristic b Φ z :=
  characteristic_eq_classicalSeparated b Φ hΦ z

end NLS.ZakharovShabat
