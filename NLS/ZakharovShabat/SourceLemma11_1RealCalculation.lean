import NLS.ZakharovShabat.SourceActionIntegrandSign
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-!
# The literal real-gap calculation in Lemma 11.1

The actual indexed action is the positive-root real integral with the
printed coefficient 2/pi. Recentring holds on every original winding-one
piecewise C1 circuit. The integral is positive on open real gaps, while
the integrand has its unique interior zero at the critical coordinate.
-/

noncomputable section
open Set Complex MeasureTheory intervalIntegral NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal recentered integral equals the area under the arcosh profile,
including the zero-length convention at a collapsed gap. -/
theorem sourceRecenteredRealActionIntegrand_integral_eq_arcosh
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    (∫ x in a..b, sourceRecenteredRealActionIntegrand hp hp1 ψ n x) =
      ∫ x in a..b, Real.arcosh (realGapHalfDiscriminant hp (periodOnePotential ψ) n x) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let c := (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let g := realGapHalfDiscriminant hp (periodOnePotential ψ) n
  have hab : a ≤ b := (realGapHalfDiscriminant_arcosh_gap_data hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).1
  change (∫ x in a..b, _) = ∫ x in a..b, Real.arcosh (g x)
  rcases eq_or_lt_of_le hab with he | hopen
  · rw [he]; simp only [intervalIntegral.integral_same]
  have hw := (realGap_weighted_arcosh_integral_eq_and_neg hp hp1 ψ hreal n hopen c).1
  calc
    _ = -(∫ x in a..b, (x-c)*(deriv g x / Real.sqrt (g x^2-1))) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro x hx
      rw [sourceRecenteredRealActionIntegrand_eq_halfDiscriminant hp hp1 ψ hreal n x hx]
      exact neg_mul _ _
    _ = _ := by rw [hw,neg_neg]

/-- The independently defined indexed action is 2/pi times the actual
arcosh area on every real gap and at every signed index. -/
theorem sourceIndexedAction_eq_realGapArcoshIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
    sourceIndexedAction hp hp1 n ψ = (2/(Real.pi : ℂ)) *
      ((∫ x in a..b, Real.arcosh (realGapHalfDiscriminant hp (periodOnePotential ψ) n x) : ℝ) : ℂ) := by
  let a := (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  let b := (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re
  have hab : a ≤ b := (realGapHalfDiscriminant_arcosh_gap_data hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n).1
  rcases eq_or_lt_of_le hab with he | hopen
  · have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) (isRealType_periodOnePotential ψ hreal) n
    have hrl : canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
        canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n :=
      Complex.ext he.symm (him.2.trans him.1.symm)
    have hg : sourcePeriodicGapDisplacement hp hp1 ψ n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,hrl,sub_self]
    rw [(sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n ψ hreal).2.2.mpr hg]
    change (0 : ℂ) = (2/(Real.pi : ℂ))*((∫ x in a..b, _ : ℝ) : ℂ)
    simp only [he,intervalIntegral.integral_same,ofReal_zero,mul_zero]
  · obtain ⟨ε,hε,hcircle⟩ := exists_sourceActionCircle_eq_upperBoundaryIntegral hp hp1 ψ hreal n hopen
    let δ := sourceRealActionEpsilon hp hp1 ψ hreal n
    have hδ : 0 < δ := (sourceRealActionEpsilon_spec hp hp1 ψ hreal n).1
    let η := min δ ε / 2
    have hη : 0 < η := div_pos (lt_min hδ hε) (by norm_num)
    have hηδ : η ∈ Ioc 0 δ := ⟨hη,by dsimp [η]; linarith [min_le_left δ ε]⟩
    have hηε : η ∈ Ioc 0 ε := ⟨hη,by dsimp [η]; linarith [min_le_right δ ε]⟩
    rw [sourceIndexedAction_eq_sourceRealAction hp hp1 n ψ hreal,
      sourceRealAction_eq_small_midpointCircle hp hp1 ψ hreal n hηδ,hcircle η hηε]
    have hu := sourceAction_upper_cosineBoundaryIntegral_eq_neg_arcosh_all hp hp1 ψ hreal n hopen 0
    simp only [ofReal_zero] at hu
    rw [hu]
    push_cast
    ring

/-- The exact 2/pi formula with the literal parity-weighted numerator and
the positive real square root from the dissertation. -/
theorem sourceIndexedAction_eq_recenteredRealIntegral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = (2/(Real.pi : ℂ)) *
      ((∫ x in
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
        sourceRecenteredRealActionIntegrand hp hp1 ψ n x : ℝ) : ℂ) := by
  rw [sourceRecenteredRealActionIntegrand_integral_eq_arcosh hp hp1 ψ hreal n]
  exact sourceIndexedAction_eq_realGapArcoshIntegral hp hp1 ψ hreal n

/-- The literal integral is strictly positive on an open gap despite its
single interior critical-point zero. -/
theorem sourceRecenteredRealActionIntegrand_integral_pos
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re) :
    0 < ∫ x in
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re..
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
      sourceRecenteredRealActionIntegrand hp hp1 ψ n x := by
  rw [sourceRecenteredRealActionIntegrand_integral_eq_arcosh hp hp1 ψ hreal n]
  obtain ⟨he,hneg⟩ := realGap_weighted_arcosh_integral_eq_and_neg hp hp1 ψ hreal n hopen 0
  rw [he] at hneg
  exact neg_neg_iff_pos.mp hneg

/-- The vanishing unweighted period allows any spectral recentering on
every original winding-one circuit, also at complex and collapsed gaps. -/
theorem SourceLemma11_1Data.action_eq_recentered_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1)
    (q : ℂ) :
    sourceIndexedAction hp hp1 n ψ = (Real.pi : ℂ)⁻¹*Γ.integral (fun z =>
      (z-q)*deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z) := by
  let f := fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hroot : D n \ sourcePeriodicSegment hp hp1 ψ n ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    intro z hz m
    by_cases hm : m = n
    · subst m; exact hz.2
    · exact hD.disk_subset_omittedDomain ψ hψV n hz.1 m hm
  have hf : ContinuousOn f (D n \ sourcePeriodicSegment hp hp1 ψ n) :=
    (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ).continuousOn.mono hroot
  have hz : Γ.integral f = 0 :=
    H.previous.previous.previous.previous.originalDisk_loopIntegral_zero hD ψ hψW hψV n Γ hΓ
  have hshift : Γ.integral (fun z => (z-q)*f z) = Γ.integral (fun z => z*f z) := by
    have he : (fun z => (z-q)*f z) = (fun z => z*f z-q*f z) := by funext z; ring
    rw [he,Γ.integral_sub (fun z => z*f z) (fun z => q*f z)
      (continuousOn_id.mul hf) (continuousOn_const.mul hf) hΓ,
      Γ.integral_const_mul,hz,mul_zero,sub_zero]
  have ha := H.previous.circuit hD ψ hψW hψV n Γ hΓ hw
  have ha' : sourceIndexedAction hp hp1 n ψ = (Real.pi : ℂ)⁻¹*Γ.integral (fun z => z*f z) := by
    simpa only [f,sourceCriticalRootRatioJoint,mul_div_assoc] using ha
  simpa only [f,sourceCriticalRootRatioJoint,mul_div_assoc] using
    ha'.trans (congrArg ((Real.pi : ℂ)⁻¹*·) hshift.symm)

/-- The two displayed equalities of the real-gap calculation hold for
every original admissible circuit, with the exact factors 1/pi and 2/pi. -/
theorem SourceLemma11_1Data.originalCircuit_realCalculation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceLemma11_1Data hp hp1 W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψW : ψ ∈ W) (hψV : ψ ∈ V)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (Γ : PiecewiseC1Loop) (hΓ : Γ.Inside (D n \ sourcePeriodicSegment hp hp1 ψ n))
    (hw : Γ.windingIntegral
      (canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) = 1) :
    let J := (Real.pi : ℂ)⁻¹*Γ.integral (fun z =>
      (z-canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)*
        deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z)
    sourceIndexedAction hp hp1 n ψ = J ∧ J = (2/(Real.pi : ℂ)) *
      ((∫ x in
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re..
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n).re,
        sourceRecenteredRealActionIntegrand hp hp1 ψ n x : ℝ) : ℂ) := by
  have he := H.action_eq_recentered_circuit hD ψ hψW hψV n Γ hΓ hw
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
  exact ⟨he,he.symm.trans (sourceIndexedAction_eq_recenteredRealIntegral hp hp1 ψ hreal n)⟩

end NLS.ZakharovShabat
