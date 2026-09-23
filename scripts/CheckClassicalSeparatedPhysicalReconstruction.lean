import NLS.ZakharovShabat.ClassicalSeparatedPhysicalReconstruction

open Set Complex MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
open BoundaryCondition

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ)
    (n : ℕ) (x : IntervalPairL2)
    (hx : x ∈ b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (n+1)) :
    ∃ v : ℕ → ℂ × ℂ,
      (∀ j ≤ n, separatedEndpointDefectCLM b (v j) = 0) ∧
      (∀ j ≤ n, separatedEndpointDefectCLM b
        (classicalJetCurve Φ z v j ⟨1,by norm_num⟩) = 0) ∧
      classicalJetPhysical Φ z v n = x :=
  exists_classicalJet_of_mem_classicalRootSpace b Φ hΦ z n x hx

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (n : ℕ) :
    Function.Surjective (classicalSeparatedJetRootMap b Φ hΦ z n) :=
  classicalSeparatedJetRootMap_surjective b Φ hΦ z n

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (m n : ℕ)
    (hm : analyticOrderAt (classicalSeparatedCharacteristic b Φ) z = m) :
    Module.finrank ℂ
      (b.classicalRootSpace (intervalL2OfFunction (extend Φ) hΦ) z (n+1)) =
        min (n+1) m :=
  finrank_classicalRootSpace_eq_min_analyticOrder b Φ hΦ z m n hm

example (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ))
    (hΦ : MemLp (extend Φ) 2 (volume.restrict (Ioc 0 1))) (z : ℂ) :
    analyticOrderAt (classicalSeparatedCharacteristic b Φ) z =
      (b.classicalAlgebraicMultiplicity
        (intervalL2OfFunction (extend Φ) hΦ) z : ℕ∞) :=
  analyticOrderAt_classicalSeparated_eq_physicalMultiplicity b Φ hΦ z

end NLS.ZakharovShabat
