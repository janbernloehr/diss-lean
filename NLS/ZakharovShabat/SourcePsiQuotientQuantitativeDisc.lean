import NLS.ZakharovShabat.SourcePsiQuotientDiscMajorant

/-!
# Quantitative tail majorant for the psi quotient

The quotient majorant used in the near-free psi equation retains the
explicit norm control of Lemma 10.8. This is needed to obtain a bound
uniform over a neighborhood of the source and root parameters.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The distant-disc quotient error is bounded by one `ℓᵖ` sequence
whose norm is controlled by the midpoint offset and squared gaps.
The constants and tail cutoff are independent of the root input. -/
theorem exists_local_sourcePsiQuotient_quantitativeTailMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ C R H : ℝ, 1 ≤ C ∧ 0 ≤ R ∧ 0 ≤ H ∧
          ∃ K : ℕ, N < K ∧ ∀ ψ ∈ V,
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ R ∧
            ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ ≤ H^2 ∧
            ∀ a : Coeff p,
            ∃ B : Coeff p,
              (∀ m : ℤ, K ≤ m.natAbs →
                ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
                  ‖sourceSingleRootQuotientJointProduct hp hp1 m
                    (z,(a,ψ))-1‖ ≤ ‖B m‖) ∧
              ‖B‖ ≤
                (Real.pi⁻¹*(Fourier.hilbertTransformBound hp1 hp+
                    ‖Fourier.hilbertSquareCoeffs‖)+
                  C*R*‖Fourier.hilbertSquareCoeffs‖)*
                    ‖a-sourcePeriodicMidpointDisplacement hp hp1 ψ‖ +
                Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hp*
                    ‖a-sourcePeriodicMidpointDisplacement hp hp1 ψ‖)*
                  ((C/2)*Fourier.absoluteSampledRowConstant hp*
                    ‖a-sourcePeriodicMidpointDisplacement hp hp1 ψ‖)^2 +
                (Real.exp (C*‖a-sourcePeriodicMidpointDisplacement hp hp1 ψ‖*
                    ‖Coeff.puncturedLattice p.conjExponent
                      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p
                        p.conjExponent).mp hp.lt_top)‖)*C^2) *
                  (‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
                    ‖squaredReciprocalKernel (min 1 (p.toReal/2))
                      (lt_min (by norm_num : (1/2:ℝ)<1)
                        (by
                          have hpr : 1 < p.toReal :=
                            (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
                          linarith))‖) := by
  obtain ⟨N,ε,hε,_,V,hVopen,_,hφV,C,R,H,hC,hR,hH,K,hNK,hdata⟩ :=
    exists_local_sourceSingleRootQuotientAsymptotic_data hp hp1 φ hφ
  refine ⟨N,ε,hε,V,hVopen,hφV,C,R,H,hC,hR,hH,max (N+1) K,by omega,?_⟩
  intro ψ hψ
  obtain ⟨hdisp,hgap,hsep,hsmall,hdom⟩ := hdata ψ hψ
  refine ⟨hdisp,hgap,?_⟩
  intro a
  let α : Coeff p := a - sourcePeriodicMidpointDisplacement hp hp1 ψ
  have hα (m : ℤ) :
      displacedRoots a m -
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) m = α m :=
    sourcePsi_midpoint_offset_apply hp hp1 a ψ m
  obtain ⟨Bp,Bg,hpoint,hBp,hBg⟩ :=
    exists_sourceSingleRootQuotientDiscMajorants
      hp hp1 hp1 hp φ ψ a α hα N K ε C R hC hR
      hdisp hsep (hdom a) hsmall
  let r := ENNReal.ofReal (p.toReal/2)
  have hr : 0 < r := ENNReal.ofReal_pos.mpr (by
    have hpr : 0 < p.toReal :=
      ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
    positivity)
  have hrp : r ≤ p := by
    calc
      r ≤ ENNReal.ofReal p.toReal := by
        dsimp [r]
        apply ENNReal.ofReal_le_ofReal
        have hpr : 0 ≤ p.toReal := ENNReal.toReal_nonneg
        linarith
      _ = p := ENNReal.ofReal_toReal hp
  let BgP : Coeff p := ⟨fun m => Bg m,(lp.memℓp Bg).of_exponent_ge hrp⟩
  let B : Coeff p := Coeff.magnitude Bp + Coeff.magnitude BgP
  refine ⟨B,?_,?_⟩
  · intro m hm z hz
    have hBpoint : ‖B m‖ = ‖Bp m‖+‖Bg m‖ := by
      simp only [B,lp.coeFn_add,Pi.add_apply,Coeff.magnitude_apply]
      rw [← Complex.ofReal_add,Complex.norm_real]
      exact Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    rw [hBpoint]
    exact hpoint m hm z hz
  · have hBgP : ‖BgP‖ ≤ ‖Bg‖ :=
      Coeff.norm_quasiExponentInclusion_le hr
        (zero_lt_one.trans hp1) hp hrp Bg
    calc
      ‖B‖ ≤ ‖Bp‖ + ‖BgP‖ := by
        simpa only [B,Coeff.norm_magnitude] using
          (norm_add_le (Coeff.magnitude Bp) (Coeff.magnitude BgP))
      _ ≤ ‖Bp‖ + ‖Bg‖ := by gcongr
      _ ≤ _ := by
        dsimp only [α] at hBp hBg
        exact add_le_add hBp hBg

/-- On any fixed bounded ball of root inputs, the quotient tail majorant
has a norm bound independent of both the source and the input. -/
theorem exists_local_sourcePsiQuotient_uniformBoundedBallTailMajorant
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (T : ℝ) (hT : 0 ≤ T) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ K : ℕ, N < K ∧ ∃ M : ℝ, 0 ≤ M ∧
          ∀ ψ ∈ V, ∀ a : Coeff p, ‖a‖ ≤ T →
            ∃ B : Coeff p, ‖B‖ ≤ M ∧
              ∀ m : ℤ, K ≤ m.natAbs →
                ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε m,
                  ‖sourceSingleRootQuotientJointProduct hp hp1 m
                    (z,(a,ψ))-1‖ ≤ ‖B m‖ := by
  obtain ⟨N,ε,hε,V,hVopen,hφV,C,R,H,hC,hR,hH,K,hNK,hmajor⟩ :=
    exists_local_sourcePsiQuotient_quantitativeTailMajorant hp hp1 φ hφ
  let t : ℝ := T+R
  let M : ℝ :=
    (Real.pi⁻¹*(Fourier.hilbertTransformBound hp1 hp+
        ‖Fourier.hilbertSquareCoeffs‖)+
      C*R*‖Fourier.hilbertSquareCoeffs‖)*t +
    Real.exp ((C/2)*Fourier.absoluteSampledRowConstant hp*t)*
      ((C/2)*Fourier.absoluteSampledRowConstant hp*t)^2 +
    (Real.exp (C*t*
        ‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p
            p.conjExponent).mp hp.lt_top)‖)*C^2) *
      (H^2 *
        ‖squaredReciprocalKernel (min 1 (p.toReal/2))
          (lt_min (by norm_num : (1/2:ℝ)<1)
            (by
              have hpr : 1 < p.toReal :=
                (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
              linarith))‖)
  have hM : 0 ≤ M := by
    dsimp [M]
    have hHil := Fourier.hilbertTransformBound_nonneg hp1 hp
    have hAbs := Fourier.absoluteSampledRowConstant_nonneg hp
    have hC0 : 0 ≤ C := by linarith
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have hpi : 0 ≤ Real.pi⁻¹ := by positivity
    have hpunct : 0 ≤ ‖Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p
          p.conjExponent).mp hp.lt_top)‖ := lp.norm_nonneg' _
    have hkernel : 0 ≤ ‖squaredReciprocalKernel (min 1 (p.toReal/2))
        (lt_min (by norm_num : (1/2:ℝ)<1)
          (by
            have hpr : 1 < p.toReal :=
              (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
            linarith))‖ := lp.norm_nonneg' _
    positivity
  refine ⟨N,ε,hε,V,hVopen,hφV,K,hNK,M,hM,?_⟩
  intro ψ hψ a ha
  obtain ⟨hmid,hgap,hB⟩ := hmajor ψ hψ
  obtain ⟨B,hpoint,hBn⟩ := hB a
  refine ⟨B,?_,hpoint⟩
  have hα : ‖a-sourcePeriodicMidpointDisplacement hp hp1 ψ‖ ≤ t := by
    dsimp [t]
    exact (norm_sub_le a _).trans (add_le_add ha hmid)
  calc
    ‖B‖ ≤ _ := hBn
    _ ≤ M := by
      dsimp [M,t]
      have hHil := Fourier.hilbertTransformBound_nonneg hp1 hp
      have hAbs := Fourier.absoluteSampledRowConstant_nonneg hp
      gcongr
      all_goals first
        | exact mul_nonneg (lp.norm_nonneg' _) (lp.norm_nonneg' _)
        | exact lp.norm_nonneg' _

end NLS.ZakharovShabat
