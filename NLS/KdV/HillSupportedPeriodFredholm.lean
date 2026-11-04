import NLS.KdV.HillMixedPeriodCompactError
import NLS.KdV.HillMixedPeriodAnalyticInjectiveChart
import NLS.SequenceSpaces.CompactIdentityFredholm

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem isCompactOperator_fderiv_hillMixedSupportedPeriodMap_add_id
    (N n : ℕ) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (a p : Coeff 2) (hp : ‖p‖ ≤ B)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) univ) :
    IsCompactOperator (fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0+
        ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))) := by
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let P := Coeff.positiveDeletedProjectionTo 2 (n : ℤ)
  let T := fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a
  have hinc : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) inc 0 :=
    inc.hasFDerivAt.const_add a
  have hG : HasFDerivAt (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) T
      (a+((0 : PositiveDeletedCoeff 2 (n : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using (hF a (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := P.hasFDerivAt.comp (0 : PositiveDeletedCoeff 2 (n : ℤ))
    (hG.comp (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) 0 hinc)
  have hder : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0 =
        P.comp (T.comp inc) := by
    convert! hd.fderiv using 1
  have hcompact := isCompactOperator_fderiv_hillMixedPeriod_add_projection q hq hr h0q h0r N n hn B D hD hc a p hp hF
  have hc' : IsCompactOperator (P.comp ((T+Coeff.positiveDeletedProjection 2 (n : ℤ)).comp inc)) := by
    exact (hcompact.comp_clm inc).clm_comp P
  have he : fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a (b,p)) 0+
        ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)) =
      P.comp ((T+Coeff.positiveDeletedProjection 2 (n : ℤ)).comp inc) := by
    rw [hder]
    apply ContinuousLinearMap.ext
    intro b
    apply Subtype.ext
    change Coeff.positiveDeletedProjection 2 (n : ℤ) (T (b : Coeff 2))+(b : Coeff 2) =
      Coeff.positiveDeletedProjection 2 (n : ℤ) (T (b : Coeff 2)+Coeff.positiveDeletedProjection 2 (n : ℤ) b)
    rw [map_add,Coeff.positiveDeletedProjection_idempotent,Coeff.positiveDeleted_fixed]
  rw [he]
  exact hc'

theorem hillMixedSupportedPeriodMap_root_derivative_bijective
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ) (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hF : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n
      (b,SpectralWeight.one.toCoeff q)) univ) :
    Function.Bijective (fderiv ℂ
      (fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillGapRootHilbertCoordinates q hq hr roots hroots) (b,SpectralWeight.one.toCoeff q)) 0) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let G := fun b : PositiveDeletedCoeff 2 (n : ℤ) => hillMixedSupportedPeriodMap q hq hr h0q h0r N n a
    (b,SpectralWeight.one.toCoeff q)
  let T := fderiv ℂ G 0
  have hcompact : IsCompactOperator (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))) :=
    isCompactOperator_fderiv_hillMixedSupportedPeriodMap_add_id q hq hr h0q h0r N n hn B D hD hc a _ hp hF
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  have hinc : AnalyticAt ℂ (fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) 0 :=
    analyticAt_const.add (inc.analyticAt 0)
  have hGa : AnalyticAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n
      (b,SpectralWeight.one.toCoeff q)) (a+((0 : PositiveDeletedCoeff 2 (n : ℤ)) : Coeff 2)) := by
    simpa only [ZeroMemClass.coe_zero,add_zero] using hF a (mem_univ _)
  have hG : AnalyticAt ℂ G 0 := ((Coeff.positiveDeletedProjectionTo 2 (n : ℤ)).analyticAt _).comp
    (hGa.comp (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => a+(b : Coeff 2)) hinc)
  have hinj : Function.Injective T := hillMixedSupportedPeriodMap_root_derivative_injective q hq hr h0q h0r
    N n hN hn B D hc hp roots hroots hperiods hG.differentiableAt
  have he : -(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)))+
      (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))) = T := by abel
  have hbijD : Function.Bijective (-(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ)))) := by
    change Function.Bijective (fun b : PositiveDeletedCoeff 2 (n : ℤ) => -b)
    exact neg_bijective
  have hbij := Coeff.bijective_add_compact_of_bijective_of_injective
    (-(ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))))
    (T+ContinuousLinearMap.id ℂ (PositiveDeletedCoeff 2 (n : ℤ))) hbijD hcompact
    (by rw [he];exact hinj)
  rw [he] at hbij
  exact hbij

theorem hillMixedSupportedPeriodMap_partial_derivative_bijective
    (N n : ℕ) (hN : 1 ≤ N) (hn : 1 ≤ n) (B D : ℝ)
    (hD : 0 ≤ D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖ ≤ B)
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (hperiods : ∀ k : ℕ, 1 ≤ k → k ≠ n → hillAbelianCandidatePeriod q hq hr roots n k = 0)
    (hF : AnalyticAt ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q))
    (hsec : AnalyticOnNhd ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n
      (b,SpectralWeight.one.toCoeff q)) univ) :
    Function.Bijective ((fderiv ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillGapRootHilbertCoordinates q hq hr roots hroots)) (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) := by
  let F := hillMixedSupportedPeriodMap q hq hr h0q h0r N n (hillGapRootHilbertCoordinates q hq hr roots hroots)
  have hi : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2)) 0 :=
    hasFDerivAt_prodMk_left (0 : PositiveDeletedCoeff 2 (n : ℤ)) (SpectralWeight.one.toCoeff q)
  have hd : HasFDerivAt (fun b : PositiveDeletedCoeff 2 (n : ℤ) => F (b,SpectralWeight.one.toCoeff q))
      ((fderiv ℂ F (0,SpectralWeight.one.toCoeff q)).comp
        (ContinuousLinearMap.inl ℂ (PositiveDeletedCoeff 2 (n : ℤ)) (Coeff 2))) 0 := by
    convert! hF.differentiableAt.hasFDerivAt.comp
      (f := fun b : PositiveDeletedCoeff 2 (n : ℤ) => (b,SpectralWeight.one.toCoeff q))
      (0 : PositiveDeletedCoeff 2 (n : ℤ)) hi using 1
  rw [← hd.fderiv]
  exact hillMixedSupportedPeriodMap_root_derivative_bijective q hq hr h0q h0r N n hN hn B D hD hc hp
    roots hroots hperiods hsec

end NLS.KdV
