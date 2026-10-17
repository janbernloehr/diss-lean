import NLS.ZakharovShabat.WeightedSignedBlockLift
import NLS.ZakharovShabat.NormalizedWeightedClosingDerivativeEquiv
import NLS.ZakharovShabat.NormalizedWeightedBirkhoffJacobian
import NLS.ZakharovShabat.SourceBirkhoffFiniteGapAdaptedDerivative

/-! # Compact weighted Birkhoff remainder at finite-gap sources

Construct one common cutoff for the actual adapted inverse and both
derivative equivalences. In this chart, the original Fourier remainder
has exact signed blocks and is compact. Compatibility transfers it to
the weighted derivative. Composing back with the adapted derivative,
which differs compactly from the identity, gives the claimed remainder.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
open Metric
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem fderiv_inverse_germ_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E ≃L[ℂ] E) (F g : E → E) (a b : E)
    (hF : AnalyticAt ℂ F a) (hg : AnalyticAt ℂ g b) (hgb : g b = a)
    (hA : A.toContinuousLinearMap = fderiv ℂ F a)
    (hinv : (fun y => F (g y)) =ᶠ[𝓝 b] id) :
    fderiv ℂ g b = A.symm.toContinuousLinearMap := by
  have hFa : HasFDerivAt F A.toContinuousLinearMap (g b) := by
    rw [hgb,hA]
    exact hF.differentiableAt.hasFDerivAt
  have he : A.toContinuousLinearMap.comp (fderiv ℂ g b) = ContinuousLinearMap.id ℂ E :=
    ((hFa.comp b hg.differentiableAt.hasFDerivAt).congr_of_eventuallyEq hinv.symm).unique (hasFDerivAt_id b)
  apply ContinuousLinearMap.ext
  intro v
  apply A.injective
  have hv := congrArg (fun L => L v) he
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv

private theorem fourier_signed_rows (a : CoeffPair p) (n : ℤ) :
    (sourceBirkhoffFourier a).1 n =
      a.fst (-n)*(sourceBirkhoffFourier (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n+
      a.snd n*(sourceBirkhoffFourier (CoeffPair.inrCLM (lp.single p n 1))).1 n ∧
    (sourceBirkhoffFourier a).2 n =
      a.fst (-n)*(sourceBirkhoffFourier (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n+
      a.snd n*(sourceBirkhoffFourier (CoeffPair.inrCLM (lp.single p n 1))).2 n := by
  constructor <;> simp [div_eq_mul_inv] <;> ring

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- At a finite-gap real source, the normalized weighted Jacobian has compact Fourier remainder. -/
theorem isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w)
    (hfinite : originalWeightedRealSource w a ∈ sourceFiniteGapLocus hp hp1) :
    IsCompactOperator (normalizedWeightedBirkhoffJacobian hp hp1 s w a.val-sourceBirkhoffFourier (p := p)) := by
  let φ := sourcePairWeightCoordinates w a.val
  let ψ := originalWeightedRealSource w a
  obtain ⟨Nc,hNc,hC⟩ := exists_uniform_normalizedWeightedClosingMap_derivative_equivs hp hp1 w φ
  obtain ⟨r,hr,Nw,_,hW⟩ := exists_uniform_compact_normalizedWeightedClosingMap_derivative hp hp1 w φ
  obtain ⟨Ni,_,hI⟩ := D.exists_uniform_finiteGap_adapted_derivative_blocks ψ hfinite
  let N := max Nc (max Nw Ni)
  obtain ⟨hAw,hAu,A,U,hA,hU,hAb,hUb,hcomm,hcommInv⟩ := hC N (by dsimp [N]; omega)
  obtain ⟨δ,hδ,g,hg,hgψ,hdata,hR,hrows⟩ := hI N (by dsimp [N]; omega)
  let b := sourceAdaptedClosingMap hp ψ.val N
  have hb : b ∈ ball b δ := mem_ball_self hδ
  have hJφ : normalizedWeightedSource w φ = ψ.val := rfl
  have hAu' : AnalyticAt ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ.val := by
    simpa only [hJφ] using hAu
  have hU' : U.toContinuousLinearMap = fderiv ℂ (fun χ => sourceAdaptedClosingMap hp χ N) ψ.val := by
    simpa only [hJφ] using hU
  have hgder : fderiv ℂ g b = U.symm.toContinuousLinearMap := by
    apply fderiv_inverse_germ_eq U (fun χ => sourceAdaptedClosingMap hp χ N) g ψ.val b hAu'
      (hg b hb) hgψ hU'
    filter_upwards [ball_mem_nhds b hδ] with y hy
    exact (hdata y hy).2
  let L := fderiv ℂ (fun y => sourceBirkhoffMap hp hp1 s (g y)) b
  have hFg : HasFDerivAt (sourceBirkhoffMap hp hp1 s) (sourceBirkhoffJacobian hp hp1 s ψ.val) (g b) := by
    rw [hgψ]
    exact (D.analytic ψ.val (D.real_subset ψ.property)).differentiableAt.hasFDerivAt
  have hL : L = (sourceBirkhoffJacobian hp hp1 s ψ.val).comp U.symm.toContinuousLinearMap := by
    have hd : L = (sourceBirkhoffJacobian hp hp1 s ψ.val).comp (fderiv ℂ g b) :=
      (hFg.comp b (hg b hb).differentiableAt.hasFDerivAt).fderiv
    rwa [hgder] at hd
  let T := (normalizedWeightedBirkhoffJacobian hp hp1 s w a.val).comp A.symm.toContinuousLinearMap
  have hT : IsCompactOperator (T-sourceBirkhoffFourier (p := p)) := by
    obtain ⟨K,_,hK⟩ := hrows 1 (by norm_num)
    apply isCompactOperator_of_weighted_signed_block_lift hp w _ (L-sourceBirkhoffFourier (p := p)) hR K
    · intro n hn v
      have hLv := (hK n hn).1 v
      have hQv := fourier_signed_rows v n
      constructor
      · change (L v).1 n-(sourceBirkhoffFourier v).1 n = _
        rw [hLv.1,hQv.1]
        change _ = v.fst (-n)*((L (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n-
          (sourceBirkhoffFourier (CoeffPair.inlCLM (lp.single p (-n) 1))).1 n)+
          v.snd n*((L (CoeffPair.inrCLM (lp.single p n 1))).1 n-
          (sourceBirkhoffFourier (CoeffPair.inrCLM (lp.single p n 1))).1 n)
        ring
      · change (L v).2 n-(sourceBirkhoffFourier v).2 n = _
        rw [hLv.2,hQv.2]
        change _ = v.fst (-n)*((L (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n-
          (sourceBirkhoffFourier (CoeffPair.inlCLM (lp.single p (-n) 1))).2 n)+
          v.snd n*((L (CoeffPair.inrCLM (lp.single p n 1))).2 n-
          (sourceBirkhoffFourier (CoeffPair.inrCLM (lp.single p n 1))).2 n)
        ring
    · intro v n
      have hnorm := D.normalizedWeightedBirkhoffJacobian_decode w a.val
        ((D.originalWeightedComplexDomain_spec w).2.1 a) (A.symm v) n
      have hi := congrArg (fun M => M v) hcommInv
      change normalizedWeightedSource w (A.symm v) = U.symm (normalizedWeightedSource w v) at hi
      constructor
      · change ((normalizedWeightedBirkhoffJacobian hp hp1 s w a.val (A.symm v)).1 n-
          (sourceBirkhoffFourier v).1 n)/(w (2*n) : ℂ) = (L (normalizedWeightedSource w v)).1 n-
            (sourceBirkhoffFourier (normalizedWeightedSource w v)).1 n
        rw [sub_div,hnorm.1,(sourceBirkhoffFourier_decode w v n).1,hi,hL]
        rfl
      · change ((normalizedWeightedBirkhoffJacobian hp hp1 s w a.val (A.symm v)).2 n-
          (sourceBirkhoffFourier v).2 n)/(w (2*n) : ℂ) = (L (normalizedWeightedSource w v)).2 n-
            (sourceBirkhoffFourier (normalizedWeightedSource w v)).2 n
        rw [sub_div,hnorm.2,(sourceBirkhoffFourier_decode w v n).2,hi,hL]
        rfl
  have hAc : IsCompactOperator (A.toContinuousLinearMap-ContinuousLinearMap.id ℂ (CoeffPair p)) := by
    rw [hA]
    exact (hW N (by dsimp [N]; omega)).2 φ (mem_ball_self hr)
  have hfinal := isCompactOperator_comp_sub_of_compact_remainders T sourceBirkhoffFourier
    A.toContinuousLinearMap hT hAc
  have he : T.comp A.toContinuousLinearMap = normalizedWeightedBirkhoffJacobian hp hp1 s w a.val := by
    apply ContinuousLinearMap.ext
    intro v
    change normalizedWeightedBirkhoffJacobian hp hp1 s w a.val (A.symm (A v)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
  simpa only [he] using hfinal
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
