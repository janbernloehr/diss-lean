import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.KdV.HillHminusSobolevAbelianCompact

/-! # Full actual Abelian symbol times the exact native Fourier principal -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

/-- The literal full-symbol principal of the actual weighted rough packet. -/
def nativeAbelianFourierPrincipal (P : HillHminusPsiChart)
    (σ : PeriodOneHminusOne → Coeff ⊤) (t : ℝ) (ht : 0≤t)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] Coeff 2 :=
  (Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht q))).comp
    (((Coeff.holderProduct (q := 2)
      (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) P.family.roots 1
        (P.dirichletSource (periodOneSobolevImageInclusion t ht q)))).comp
      ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)).comp
        (periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap)

private theorem compact_principal_transitive
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A : E →L[ℂ] G) (M : F →L[ℂ] G) (B Q : E →L[ℂ] F)
    (hA : IsCompactOperator (A-M.comp B)) (hB : IsCompactOperator (B-Q)) :
    IsCompactOperator (A-M.comp Q) := by
  have he : A-M.comp Q=(A-M.comp B)+M.comp (B-Q) := by
    ext x
    change A x-M (Q x)=(A x-M (B x))+M (B x-Q x)
    rw [map_sub]
    abel
  rw [he]
  exact hA.add (hB.clm_comp M)

/-- The compact full-symbol derivative remainder and ACTUAL eta Fourier
comparison combine for the SAME supplied native packet at each real base. -/
theorem isCompactOperator_native_abelian_derivative_sub_fourier
    (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (σ : PeriodOneHminusOne → Coeff ⊤) (t : ℝ) (ht : 0≤t)
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V)
    (F E : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hF : ∀ p∈V, periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧
      ∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (hq : q∈V)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion t ht q))=
      P.miura.lift (periodOneSobolevImageInclusion t ht q))
    (hE : IsCompactOperator (fderiv ℂ E q-
      (Coeff.holderProduct (q := 2) (σ (periodOneSobolevImageInclusion t ht q))).comp (fderiv ℂ F q))) :
    IsCompactOperator (fderiv ℂ E q-P.nativeAbelianFourierPrincipal σ t ht q) := by
  exact compact_principal_transitive _ _ _ _ hE
    (P.isCompactOperator_native_eta_sub_fourier_of_retained H hstrong t ht V hV F hF q hq hr)

end NLS.KdV.HillHminusPsiChart
