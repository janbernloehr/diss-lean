import NLS.ZakharovShabat.SourcePsiFreeEquationFactorization
import NLS.ZakharovShabat.SourceSingleRootQuotientAsymptoticDiscSup

/-!
# Quantitative free-source quotient tail

At zero source the standard gaps collapse, so the squared-gap
correction in Lemma 10.8 vanishes. The remaining quotient error on
all distant free centers has an `ℓᵖ` majorant whose norm is
`O(‖a‖)+O(‖a‖² exp(O(‖a‖)))`.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The source squared-gap sequence vanishes at the free potential. -/
theorem sourcePeriodicSquaredGapCoeff_zero_source
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourcePeriodicSquaredGapCoeff hp hp1 (0 : CoeffPair p) = 0 := by
  ext m
  rw [sourcePeriodicSquaredGapCoeff_apply]
  simp only [sourcePeriodicGapDisplacement_apply, map_zero, lp.coeFn_zero,
    Pi.zero_apply, canonicalPeriodicGap_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/-- The free-source quotient error has a distant-index majorant with
a norm bound that vanishes as the root displacement tends to zero. -/
theorem exists_sourcePsiQuotient_freeCenter_tailMajorant_norm
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ K : ℕ, ∃ A D : ℝ,
      ∀ a : Coeff p, ∃ B : Coeff p,
        (∀ m : ℤ, K ≤ m.natAbs →
          ‖sourceSingleRootQuotientJointProduct hp hp1 m
            (((Real.pi : ℂ)*m),(a,(0 : CoeffPair p)))-1‖ ≤ ‖B m‖) ∧
        ‖B‖ ≤ A*‖a‖ + Real.exp (D*‖a‖)*(D*‖a‖)^2 := by
  obtain ⟨N,ε,hε,_,V,_,_,hzero,C,R,_,hC,hR,_,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1
      (0 : CoeffPair p) (by simp)
  let A : ℝ := Real.pi⁻¹*(Fourier.hilbertTransformBound hp1 hp+
    ‖Fourier.hilbertSquareCoeffs‖)+C*R*‖Fourier.hilbertSquareCoeffs‖
  let D : ℝ := (C/2)*Fourier.absoluteSampledRowConstant hp
  refine ⟨max (N+1) K,A,D,?_⟩
  intro a
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1
          (periodOnePotential (0 : CoeffPair p))
          (periodOnePotential_mem (0 : CoeffPair p)) m = a m := by
    simp only [displacedRoots, map_zero, canonicalPeriodicMidpoint_zero]
    ring
  obtain ⟨hdisp,_,hsep,hsmall,hdom⟩ := hdata 0 hzero
  obtain ⟨B,Bg,hpoint,hB,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants
      hp hp1 hp1 hp (0 : CoeffPair p) (0 : CoeffPair p) a a hα
      N K ε C R hC hR hdisp hsep (hdom a) hsmall
  have hBgzero : Bg = 0 := by
    have hz : ‖Bg‖ ≤ 0 := by
      simpa [sourcePeriodicSquaredGapCoeff_zero_source hp hp1] using hBg
    apply lp.norm_eq_zero_iff.mp
    exact le_antisymm hz (lp.norm_nonneg' Bg)
  refine ⟨B,?_,?_⟩
  · intro m hm
    have hzdisc : (Real.pi : ℂ)*m ∈
        sourceIsolatingDisc hp hp1 (0 : CoeffPair p) N ε m := by
      have hN : ¬m.natAbs ≤ N := by omega
      have hcenter : (Real.pi : ℂ)*m ∈ refinedResonantDisk m :=
        mem_ball_self (by positivity)
      simpa only [sourceIsolatingDisc,if_neg hN] using hcenter
    simpa [hBgzero] using hpoint m hm ((Real.pi : ℂ)*m) hzdisc
  · simpa only [A,D] using hB

end NLS.ZakharovShabat
