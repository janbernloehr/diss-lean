import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Bianalytic equivalences transported through bounded linear
coordinate identities on the source and target. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {𝕜 E F G H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

def linearTransportEquiv (A : E ≃L[𝕜] F) (e : F ≃ G) (B : G ≃L[𝕜] H) : E ≃ H :=
  A.toEquiv.trans (e.trans B.toEquiv)

theorem analyticAt_linearTransportEquiv (A : E ≃L[𝕜] F) (e : F ≃ G) (B : G ≃L[𝕜] H)
    (he : ∀ x, AnalyticAt 𝕜 e x) (x : E) :
    AnalyticAt 𝕜 (linearTransportEquiv A e B) x :=
  (B.analyticAt _).comp (f := fun y => e (A y))
    ((he _).comp (f := fun y => A y) (A.analyticAt x))

theorem analyticAt_linearTransportEquiv_symm (A : E ≃L[𝕜] F) (e : F ≃ G) (B : G ≃L[𝕜] H)
    (he : ∀ z, AnalyticAt 𝕜 e.symm z) (z : H) :
    AnalyticAt 𝕜 (linearTransportEquiv A e B).symm z :=
  (A.symm.analyticAt _).comp (f := fun y => e.symm (B.symm y))
    ((he _).comp (f := fun y => B.symm y) (B.symm.analyticAt z))

end NLS.FunctionalAnalysis
