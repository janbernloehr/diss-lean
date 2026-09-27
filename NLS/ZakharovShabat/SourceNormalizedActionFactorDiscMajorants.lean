import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ZakharovShabat.SourceNormalizedActionSequenceMajorants

/-!
# Deleted-factor majorants on complex distant-index discs

The existing quotient disc estimate applies to the canonical critical
root data. Its `ℓq + ℓ^(p/2)` bounds therefore control the deleted
factor at every spectral point of each distant refined resonant disc,
including the uniform circles used for the normalized action.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complementary factor on distant complex isolating discs has
`ℓq + ℓ^(p/2)` pointwise majorants at all sufficiently distant
indices. The exponent `q` can be any finite Banach exponent strictly
above one and at least `p/2`. -/
theorem exists_local_sourceNormalizedAction_factor_disc_sequenceMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ C R H : ℝ,
        1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧ ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤
              ‖Bq n‖ + ‖Bg n‖) ∧
          ‖Bq‖ ≤
            (Real.pi⁻¹*(Fourier.hilbertTransformBound hq1 hq+
                ‖Fourier.hilbertSquareCoeffs‖)+
              C*R*‖Fourier.hilbertSquareCoeffs‖)*
                ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖ +
              Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hq*
                ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖)*
                ((C/2)*Fourier.absoluteSampledRowConstant hq*
                  ‖sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ‖)^2 ∧
          ‖Bg‖ ≤
            (Real.exp (C*‖sourceCriticalMidpointOffsetAtExponent
                hp hp1 hhalf ψ‖*‖Coeff.puncturedLattice q.conjExponent
                  ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp
                    hq.lt_top)‖)*C^2) *
              (H^2 *
                ‖squaredReciprocalKernel (min 1 (p.toReal/2))
                  (lt_min (by norm_num : (1/2:ℝ)<1)
                    (by
                      have hpr : 1 < p.toReal :=
                        (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                      linarith))‖) := by
  obtain ⟨N,ε,_,_,V₁,hV₁open,_,hφV₁,C,R,H,hC,hR,hH,K₁,hNK,hmajor⟩ :=
    exists_local_sourceSingleRootQuotientDiscMajorants
      hp hp1 hq1 hq φ hφ
  obtain ⟨W,hWopen,hWreal,hOffset⟩ :=
    exists_global_sourceCriticalMidpointOffsetAtExponent_eq hp hp1 hhalf
  let V := V₁ ∩ W
  let K := K₁
  refine ⟨V,hV₁open.inter hWopen,
    ⟨hφV₁,hWreal hφ⟩,K,C,R,H,hC,hR,hH,?_⟩
  intro ψ hψ
  let a : Coeff p := canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
  let α : Coeff q := sourceCriticalMidpointOffsetAtExponent
    hp hp1 hhalf ψ
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m := by
    have hcrit : displacedRoots a m =
        canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m := by
      simp only [a,displacedRoots,canonicalCriticalDisplacement_apply]
      ring
    rw [hcrit]
    exact hOffset ψ hψ.2 m
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ :=
    hmajor ψ hψ.1 a α hα
  refine ⟨Bq,Bg,?_,hBq,hBg⟩
  intro n hn z hzdisc
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

/-- The disc factor majorants may be chosen with common sequence-norm bounds
throughout a neighborhood of a real-type source. -/
theorem exists_local_sourceNormalizedAction_factor_disc_uniformMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
            ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤
              ‖Bq n‖ + ‖Bg n‖) ∧
          ‖Bq‖ ≤ Lq ∧ ‖Bg‖ ≤ Lg := by
  obtain ⟨V₁,hV₁open,hφV₁,K,C,R,H,hC,hR,hH,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_disc_sequenceMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨V₂,hV₂open,hφV₂,A,hA,hα⟩ :=
    exists_local_sourceCriticalMidpointOffsetAtExponent_bound
      hp hp1 hq1.le hq hhalf φ hφ
  let u : ℝ := Real.pi⁻¹ *
    (Fourier.hilbertTransformBound hq1 hq + ‖Fourier.hilbertSquareCoeffs‖) +
      C*R*‖Fourier.hilbertSquareCoeffs‖
  let d : ℝ := (C/2) * Fourier.absoluteSampledRowConstant hq
  let v : ℝ := ‖Coeff.puncturedLattice q.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖
  have hpr : 1 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let w : ℝ := ‖squaredReciprocalKernel (min 1 (p.toReal/2))
    (lt_min (by norm_num : (1/2:ℝ)<1) (by linarith))‖
  let Lq : ℝ := u*A + Real.exp (d*A)*(d*A)^2
  let Lg : ℝ := (Real.exp (C*A*v)*C^2)*(H^2*w)
  have hv : 0 ≤ v := lp.norm_nonneg' _
  have hw : 0 ≤ w := lp.norm_nonneg' _
  have hu : 0 ≤ u := by
    dsimp [u]
    have := Fourier.hilbertTransformBound_nonneg hq1 hq
    positivity
  have hd : 0 ≤ d := by
    dsimp [d]
    have := Fourier.absoluteSampledRowConstant_nonneg hq
    positivity
  refine ⟨V₁ ∩ V₂,hV₁open.inter hV₂open,⟨hφV₁,hφV₂⟩,
    K,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hfactor ψ hψ.1
  let α := sourceCriticalMidpointOffsetAtExponent hp hp1 hhalf ψ
  have hαA : ‖α‖ ≤ A := hα ψ hψ.2
  have hdA : d*‖α‖ ≤ d*A := mul_le_mul_of_nonneg_left hαA hd
  have hBq' : ‖Bq‖ ≤ u*‖α‖ + Real.exp (d*‖α‖)*(d*‖α‖)^2 := by
    simpa only [u,d,α] using hBq
  have hBg' : ‖Bg‖ ≤ (Real.exp (C*‖α‖*v)*C^2)*(H^2*w) := by
    simpa only [v,w,α] using hBg
  refine ⟨Bq,Bg,hpoint,?_,?_⟩
  · apply hBq'.trans
    dsimp [Lq]
    apply add_le_add (mul_le_mul_of_nonneg_left hαA hu)
    apply mul_le_mul
      (Real.exp_le_exp.mpr hdA)
      (pow_le_pow_left₀ (mul_nonneg hd (lp.norm_nonneg' α)) hdA 2)
      (sq_nonneg _)
      (Real.exp_nonneg _)
  · apply hBg'.trans
    dsimp [Lg]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (sq_nonneg _) hw)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hαA (by linarith : 0 ≤ C))
      hv

/-- The same summable majorants hold on one common family of fixed
free-centered circles for all sufficiently distant signed indices. -/
theorem exists_local_sourceNormalizedAction_factor_circle_uniformMajorants
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ, K ≤ n.natAbs →
            ∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
              ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ ≤
                ‖Bq n‖ + ‖Bg n‖) ∧
          ‖Bq‖ ≤ Lq ∧ ‖Bg‖ ≤ Lg := by
  obtain ⟨Vd,hVdopen,hφVd,Kd,Lq,Lg,hdisc⟩ :=
    exists_local_sourceNormalizedAction_factor_disc_uniformMajorants
      hp hp1 hq1 hq hhalf φ hφ
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcircle⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circles hp hp1 φ
  let V := Vd ∩ Vc
  let K := max Kd Kc
  refine ⟨V,hVdopen.inter hVcopen,⟨hφVd,hφVc⟩,K,Lq,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hdisc ψ hψ.1
  refine ⟨Bq,Bg,?_,hBq,hBg⟩
  intro n hn z hz
  have hKd : Kd ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKc : Kc ≤ n.natAbs := le_trans (le_max_right _ _) hn
  have hclosed := (hcircle ψ hψ.2 n hKc).2.1
  have hzclosed : z ∈ closedBall ((Real.pi:ℂ)*n) (Real.pi/8) :=
    mem_closedBall.mpr (mem_sphere.mp hz).le
  exact hpoint n hKd z (hclosed hzclosed)

/-- In particular, the deleted factors are uniformly bounded on all
distant common circles and all sources in one complex neighborhood. -/
theorem exists_local_sourceNormalizedAction_factor_circle_uniform_bound
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ K : ℕ, ∃ M : ℝ, ∀ ψ ∈ V,
        ∀ n : ℤ, K ≤ n.natAbs →
          ∀ z ∈ sphere ((Real.pi:ℂ)*n) (Real.pi/8),
            ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ M := by
  obtain ⟨V,hVopen,hφV,K,Lq,Lg,hmajor⟩ :=
    exists_local_sourceNormalizedAction_factor_circle_uniformMajorants
      hp hp1 hq1 hq hhalf φ hφ
  refine ⟨V,hVopen,hφV,K,Lq+Lg+1,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨Bq,Bg,hpoint,hBq,hBg⟩ := hmajor ψ hψ
  have hpr : 0 < p.toReal/2 := by
    have hpr' : 1 < p.toReal :=
      (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
    linarith
  have hqpoint : ‖Bq n‖ ≤ ‖Bq‖ :=
    lp.norm_apply_le_norm (zero_lt_one.trans hq1).ne' Bq n
  have hgpoint : ‖Bg n‖ ≤ ‖Bg‖ :=
    lp.norm_apply_le_norm (ENNReal.ofReal_ne_zero_iff.mpr hpr) Bg n
  calc
    ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ =
        ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z‖ := by simp
    _ = ‖(I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1) + 1‖ := by
      congr 1
      ring
    _ ≤ ‖I * sourceCriticalRootRatioExtension hp hp1 n ψ z - 1‖ +
        ‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ ‖Bq n‖ + ‖Bg n‖ + 1 := by
      simpa using add_le_add_right (hpoint n hn z hz) 1
    _ ≤ Lq+Lg+1 := by linarith


end NLS.ZakharovShabat
