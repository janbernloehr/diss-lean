import NLS.ZakharovShabat.SymmetricDirichletDerivative
import NLS.ZakharovShabat.SymmetricSourceCoordinates
import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! # Analytic local Dirichlet coordinates at every symmetric Hilbert source

The full actual Dirichlet displacement map on the symmetric complex slice
has a two-sided analytic local inverse at every real source in that slice.
These are local coordinates near each source; no global inverse statement
or signed-gap uniqueness theorem is inferred.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

@[simp] theorem sourceSpatialReflection_complexSymmetricSourceCoefficients
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (a : Coeff p) :
    sourceSpatialReflection (complexSymmetricSourceCoefficients p a) =
      complexSymmetricSourceCoefficients p a := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> ext n
  · change a (-n) = a (-n)
    rfl
  · change a (-(-n)) = a n
    rw [neg_neg]

/-- The complex parametrization extends the actual real Fourier parametrization. -/
theorem complexSymmetricSourceCoefficients_realCoeff (a : RealCoeff 2) :
    complexSymmetricSourceCoefficients 2 (RealCoeff.complexCLM 2 a) =
      symmetricSourceCoefficients 2 a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n <;> rfl

/-- Actual indexed Dirichlet displacements in symmetric complex Fourier coordinates. -/
def symmetricSourceDirichletMap : Coeff 2 → Coeff 2 :=
  sourceBoundaryDisplacement (by simp) (by norm_num) .dirichlet ∘
    complexSymmetricSourceCoefficients 2

theorem analyticAt_symmetricSourceDirichletMap (a : Coeff 2)
    (ha : IsRealType (CoeffPair.toMax 2 (complexSymmetricSourceCoefficients 2 a))) :
    AnalyticAt ℂ symmetricSourceDirichletMap a := by
  obtain ⟨_,_,hr,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  exact (hD .dirichlet _ (hr ha)).comp ((complexSymmetricSourceCoefficients 2).analyticAt a)

theorem fderiv_symmetricSourceDirichletMap (a : Coeff 2)
    (ha : IsRealType (CoeffPair.toMax 2 (complexSymmetricSourceCoefficients 2 a))) :
    fderiv ℂ symmetricSourceDirichletMap a =
      symmetricDirichletDerivative (complexSymmetricSourceCoefficients 2 a) := by
  obtain ⟨_,_,hr,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  exact ((hD .dirichlet _ (hr ha)).differentiableAt.hasFDerivAt.comp a
    (complexSymmetricSourceCoefficients 2).hasFDerivAt).fderiv

/-- At every real point of the symmetric slice, the actual full Dirichlet
displacement has an analytic local inverse with both inverse identities. -/
theorem exists_symmetricSourceDirichlet_localInverse (a : Coeff 2)
    (ha : IsRealType (CoeffPair.toMax 2 (complexSymmetricSourceCoefficients 2 a))) :
    ∃ G : Coeff 2 → Coeff 2, AnalyticAt ℂ G (symmetricSourceDirichletMap a) ∧
      G (symmetricSourceDirichletMap a) = a ∧
      (∀ᶠ b in 𝓝 a, G (symmetricSourceDirichletMap b) = b) ∧
      (∀ᶠ d in 𝓝 (symmetricSourceDirichletMap a), symmetricSourceDirichletMap (G d) = d) ∧
      fderiv ℂ G (symmetricSourceDirichletMap a) =
        Ring.inverse (symmetricDirichletDerivative (complexSymmetricSourceCoefficients 2 a)) := by
  have hb := bijective_symmetricDirichletDerivative
    (complexSymmetricSourceCoefficients 2 a) ha
    (sourceSpatialReflection_complexSymmetricSourceCoefficients a)
  have hu : IsUnit (fderiv ℂ symmetricSourceDirichletMap a) := by
    rw [fderiv_symmetricSourceDirichletMap a ha, ContinuousLinearMap.isUnit_iff_bijective]
    exact hb
  simpa only [fderiv_symmetricSourceDirichletMap a ha] using
    NLS.ComplexAnalysis.exists_localInverse_of_isUnit_fderiv
      (analyticAt_symmetricSourceDirichletMap a ha) hu

/-- In particular, the actual Dirichlet map is one-to-one on a neighborhood
of every real symmetric Fourier coordinate. -/
theorem exists_nhds_injOn_symmetricSourceDirichletMap (a : RealCoeff 2) :
    ∃ U ∈ 𝓝 (RealCoeff.complexCLM 2 a), Set.InjOn symmetricSourceDirichletMap U := by
  have ha : IsRealType (CoeffPair.toMax 2
      (complexSymmetricSourceCoefficients 2 (RealCoeff.complexCLM 2 a))) := by
    rw [complexSymmetricSourceCoefficients_realCoeff]
    exact symmetricSourceCoefficients_realType a
  obtain ⟨G,_,_,hl,_,_⟩ := exists_symmetricSourceDirichlet_localInverse _ ha
  refine ⟨{b | G (symmetricSourceDirichletMap b) = b}, hl, ?_⟩
  intro b hb c hc he
  exact hb.symm.trans ((congrArg G he).trans hc)

end NLS.ZakharovShabat
