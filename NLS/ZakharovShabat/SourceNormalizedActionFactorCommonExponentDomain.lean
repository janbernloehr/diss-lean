import NLS.ZakharovShabat.SourceNormalizedActionFactorDiscMajorants
import NLS.ZakharovShabat.SourceSingleRootQuotientCommonExponentDomain

/-!
# A common domain for all deleted-factor exponents

For `1 < p ≤ 2`, the critical-to-midpoint offset is an `ℓ¹`
sequence. The endpoint quotient-disc estimate therefore supplies
deleted-factor majorants in every finite `ℓq`, `q > 1`, on a single
complex source neighborhood with a single tail cutoff.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source neighborhood and tail cutoff for the deleted-factor
disc majorants are independent of the target exponent `q > 1` when
`p ≤ 2`. -/
theorem exists_local_sourceNormalizedAction_factor_disc_allExponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ,
        ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (_hq1 : 1 < q) (_hq : q ≠ ⊤),
          ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
            ∃ Bq : Coeff q,
              ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
                (∀ n : ℤ, K ≤ n.natAbs →
                  ∀ z ∈ refinedResonantDisk n,
                    ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤
                      ‖Bq n‖ + ‖Bg n‖) ∧
                ‖Bq‖ ≤ Lq ∧ ‖Bg‖ ≤ Lg := by
  obtain ⟨N,ε,_,_,V₁,hV₁open,_,hφV₁,C,R,H,hC,hR,hH,K,hNK,hmajor⟩ :=
    exists_local_sourceSingleRootQuotientDiscMajorants_one_allExponents
      hp hp1 φ hφ
  obtain ⟨V₂,hV₂open,hφV₂,A,hA,hα⟩ :=
    exists_local_sourceCriticalMidpointOffset_one_bound hp hp1 hp2 φ hφ
  let V := V₁ ∩ V₂
  refine ⟨V,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,K,?_⟩
  intro q hqFact hq1 hq
  let u : ℝ := Real.pi⁻¹ *
    (Fourier.hilbertTransformBound hq1 hq + ‖Fourier.hilbertSquareCoeffs‖) +
      C*R*‖Fourier.hilbertSquareCoeffs‖
  let d : ℝ := (C/2) * Fourier.absoluteSampledRowConstant hq
  let v : ℝ := ‖Coeff.puncturedLattice
    (1:ℝ≥0∞).conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt (1:ℝ≥0∞)
      (1:ℝ≥0∞).conjExponent).mp (by norm_num : (1:ℝ≥0∞) < ⊤))‖
  have hpr : 1 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let w : ℝ := ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by linarith))‖
  let Lq : ℝ := u*A + Real.exp (d*A)*(d*A)^2
  let Lg : ℝ := (Real.exp (C*A*v)*C^2)*(H^2*w)
  have hu : 0 ≤ u := by
    dsimp [u]
    have := Fourier.hilbertTransformBound_nonneg hq1 hq
    positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    have := Fourier.absoluteSampledRowConstant_nonneg hq
    positivity
  have hv : 0 ≤ v := lp.norm_nonneg' _
  have hw : 0 ≤ w := lp.norm_nonneg' _
  refine ⟨Lq,Lg,?_⟩
  intro ψ hψ
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let α : Coeff 1 := sourceCriticalMidpointOffsetAtExponent
    hp hp1 (source_half_le_one hp hp2) ψ
  have hαeq (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m := by
    have hcrit : displacedRoots a m =
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m := by
      simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
      ring
    rw [hcrit]
    exact (hα ψ hψ.2).2 m
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ :=
    hmajor q hq1 hq ψ hψ.1 a α hαeq
  have hαA : ‖α‖ ≤ A := (hα ψ hψ.2).1
  have hαqA : ‖Coeff.exponentInclusion hq1.le α‖ ≤ A :=
    (Coeff.norm_exponentInclusion_le hq1.le α).trans hαA
  have hdA : d*‖Coeff.exponentInclusion hq1.le α‖ ≤ d*A :=
    mul_le_mul_of_nonneg_left hαqA hd
  refine ⟨Bq,Bg,?_,?_,?_⟩
  · intro n hn z hzdisc
    have hN : N < n.natAbs := hNK.trans_le hn
    have hziso : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
      simpa only [sourceIsolatingDisc, if_neg (not_le.mpr hN)] using hzdisc
    have hfactor : I * sourceCriticalRootRatioExtension hp hp1 n ψ z =
        sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by
      change I * (-I *
        sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) = _
      calc
        I * (-I * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))) =
            -(I^2) * sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ)) := by ring
        _ = _ := by simp [Complex.I_sq]
    change ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤ _
    rw [hfactor]
    exact hpoint n hn z hziso
  · have hBq' : ‖Bq‖ ≤ u*‖Coeff.exponentInclusion hq1.le α‖ +
        Real.exp (d*‖Coeff.exponentInclusion hq1.le α‖)*
          (d*‖Coeff.exponentInclusion hq1.le α‖)^2 := by
      simpa only [u,d] using hBq
    apply hBq'.trans
    dsimp [Lq]
    apply add_le_add (mul_le_mul_of_nonneg_left hαqA hu)
    apply mul_le_mul
      (Real.exp_le_exp.mpr hdA)
      (pow_le_pow_left₀
        (mul_nonneg hd (lp.norm_nonneg' _)) hdA 2)
      (sq_nonneg _)
      (Real.exp_nonneg _)
  · have hBg' : ‖Bg‖ ≤ (Real.exp (C*‖α‖*v)*C^2)*(H^2*w) := by
      simpa only [v,w] using hBg
    apply hBg'.trans
    dsimp [Lg]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hw)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hαA (by linarith : 0 ≤ C)) hv

end NLS.ZakharovShabat
