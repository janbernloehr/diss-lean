import NLS.KdV.HillHminusSobolevEtaGerms
import NLS.KdV.HillHminusSobolevMiuraCompactDerivative
import NLS.KdV.HillMiuraSobolevEtaCompactDerivative

/-! # Fourier principal of the SAME actual rough Hill eta germ

Any genuine native realization of the original eta coefficients has the
same compact derivative comparison. The actual chart, root family,
Dirichlet phase, weights and free mass inverse are retained literally.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

private theorem compact_composition_remainders
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (A Q : F →L[ℂ] G) (B R : E →L[ℂ] F)
    (hA : IsCompactOperator (A-Q)) (hB : IsCompactOperator (B-R)) :
    IsCompactOperator (A.comp B-Q.comp R) := by
  have he : A.comp B-Q.comp R=(A-Q).comp B+Q.comp (B-R) := by
    ext x
    change A (B x)-Q (R x)=(A (B x)-Q (B x))+Q (B x-R x)
    rw [map_sub]
    abel
  rw [he]
  exact (hA.comp_clm B).add (hB.clm_comp Q)

private theorem compact_fderiv_composition_remainders
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (f : E → G) (g : E → F) (e : F → G) (q : E)
    (Q : F →L[ℂ] G) (R : E →L[ℂ] F)
    (he : f =ᶠ[𝓝 q] (fun p => e (g p)))
    (hea : DifferentiableAt ℂ e (g q)) (hga : DifferentiableAt ℂ g q)
    (hec : IsCompactOperator (fderiv ℂ e (g q)-Q))
    (hgc : IsCompactOperator (fderiv ℂ g q-R)) :
    IsCompactOperator (fderiv ℂ f q-Q.comp R) := by
  have hd : fderiv ℂ (fun p => e (g p)) q=
      (fderiv ℂ e (g q)).comp (fderiv ℂ g q) :=
    (hea.hasFDerivAt.comp q hga.hasFDerivAt).fderiv
  rw [he.fderiv_eq,hd]
  exact compact_composition_remainders _ _ _ _ hec hgc

private theorem eventuallyEq_sequence_pullback
    {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E → P) (w : ℤ → ℂ) (R : P → ℤ → ℂ)
    (f : E → Coeff 2) (g : E → F) (e : F → Coeff 2) (q : E)
    (U V : Set E) (hU : IsOpen U) (hV : IsOpen V) (hqU : q∈U) (hqV : q∈V)
    (hga : ContinuousAt g q) (A : Set F) (hA : IsOpen A) (hgqA : g q∈A)
    (hf : ∀ p∈V, ∀ n, f p n=w n*R (L p) n)
    (he : ∀ p∈U, p∈V → g p∈A → ∀ n, e (g p) n=w n*R (L p) n) :
    f =ᶠ[𝓝 q] (fun p => e (g p)) := by
  have hAev : ∀ᶠ p in 𝓝 q, g p∈A := hga (hA.mem_nhds hgqA)
  filter_upwards [hU.mem_nhds hqU,hV.mem_nhds hqV,hAev] with p hpU hpV hpA
  ext n
  exact (hf p hpV n).trans (he p hpU hpV hpA n).symm

/-- EVERY actual native eta germ has the full literal Fourier principal
plus compact at the eligible real base. This uses the SAME actual native
Miura germ, rather than choosing a new coordinate map or right inverse. -/
theorem isCompactOperator_native_eta_derivative_sub_principal
    (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (t : ℝ) (ht : 0≤t)
    (U : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hU : IsOpen U)
    (g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2)
    (hga : AnalyticOnNhd ℂ g U)
    (hg : ∀ p∈U, periodOneSobolevImageInclusion t ht p∈P.miura.domain ∧
      WeightedCoeff.sobolevToL2 ht (g p)=P.miura.lift (periodOneSobolevImageInclusion t ht p))
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V)
    (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hF : ∀ p∈V, periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧
      ∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*
        P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (hqU : q∈U) (hqV : q∈V)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion t ht q))=
      P.miura.lift (periodOneSobolevImageInclusion t ht q)) :
    IsCompactOperator (fderiv ℂ F q-
      ((Coeff.holderProduct (q := 2)
        (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) P.family.roots 1
          (sourcePhase (hillMiuraDiagonal (P.miura.lift (periodOneSobolevImageInclusion t ht q)))))).comp
        ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap) := by
  have hreal : periodOneL2Conjugation (WeightedCoeff.sobolevToL2 ht (g q))=
      WeightedCoeff.sobolevToL2 ht (g q) := by rw [(hg q hqU).2];exact hr
  obtain ⟨A,hA,hgqA,_M,_hM,hEta⟩ := exists_hillMiuraSobolevEtaSequence_analytic H t ht (g q) hreal
  let E := hillMiuraSobolevEtaSequence P.family.roots t ht 1
  have hEa : DifferentiableAt ℂ E (g q) := ((hEta 1 (Or.inl rfl)).1 (g q) hgqA).differentiableAt
  have he : F =ᶠ[𝓝 q] (fun p => E (g p)) := by
    apply eventuallyEq_sequence_pullback (periodOneSobolevImageInclusion t ht)
      (fun n => (Weight.sobolev t n : ℂ)) (fun p n => P.sourceEtaSequence p n) F g E q
      U V hU hV hqU hqV (hga q hqU).continuousAt A hA hgqA
      (fun p hp => (hF p hp).2)
    intro p hpU hpV hpA n
    rw [P.sourceEtaSequence_apply H _ (hF p hpV).1 n]
    have hx := ((hEta 1 (Or.inl rfl)).2 (g p) hpA).2 n
    rw [(hg p hpU).2] at hx
    exact hx
  apply compact_fderiv_composition_remainders F g E q _ _ he hEa (hga q hqU).differentiableAt
  · have hc := isCompactOperator_fderiv_hillMiuraSobolevEta_sub_principal H t ht (g q) hreal
    rw [(hg q hqU).2] at hc
    exact hc
  · exact P.miura.isCompactOperator_native_lift_derivative_sub_free t ht U hU g hga hg q hqU

end NLS.KdV.HillHminusPsiChart
