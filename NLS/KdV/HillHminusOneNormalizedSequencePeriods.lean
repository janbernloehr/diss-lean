import NLS.KdV.HillHminusOneNormalizedNumeratorSequence

/-! # Native Bochner contour normalization of the whole numerator family -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {C : HillHminusMiuraChart} {N : ℕ} {V : Set PeriodOneHminusOne} {A : ℝ}
variable (D : HillHminusUniformPeriodData C N V A)
include D

/-- The assembled normalized one-form is genuinely Bochner integrable. -/
theorem normalizedNumeratorSequence_contour_integrable
    (R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V) :
    CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,q)) •
      hillHminusNormalizedNumeratorSequence C N R (z^2,q))
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) := by
  let L := Coeff.hilbertMatrixTranspose (R q)
  have hi := D.numerator_contour_integrable k q hq
  have hj : CircleIntegrable (fun z : ℂ => L
      (((2*z)/hillHminusContinuedRoot (z^2,q)) • hillHminusNumeratorHilbert C N (z^2,q)))
      ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  simpa only [map_smul,L,hillHminusNormalizedNumeratorSequence] using hj

/-- The actual inverse preserves the complementary identity block, so
assembling positive numerators introduces no extra nonpositive components. -/
theorem normalizedNumeratorSequence_nonpositive
    (T R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (t : ℂ × PeriodOneHminusOne) (ht : t ∈ univ ×ˢ V)
    (hentry : ∀ j m : ℤ, (T t.2 (lp.single 2 m 1)) j = hillHminusPeriodMatrix C N t.2 j m)
    (hRT : (R t.2).comp (T t.2) = ContinuousLinearMap.id ℂ (Coeff 2))
    (m : ℤ) (hm : m ≤ 0) : hillHminusNormalizedNumeratorSequence C N R t m = 0 := by
  have hTe : T t.2 (lp.single 2 m 1) = lp.single 2 m 1 := by
    ext j
    rw [hentry]
    by_cases hj : 0 < j
    · simp only [hillHminusPeriodMatrix,dif_pos hj,dif_neg (by omega : ¬ 0 < m),
        lp.single_apply,Pi.single_apply,if_neg (by omega : j ≠ m)]
    · simp only [hillHminusPeriodMatrix,dif_neg hj,lp.single_apply,Pi.single_apply]
  have hRe := congrArg (fun L : Coeff 2 →L[ℂ] Coeff 2 => L (lp.single 2 m 1)) hRT
  change R t.2 (T t.2 (lp.single 2 m 1)) = lp.single 2 m 1 at hRe
  rw [hTe] at hRe
  change Coeff.hilbertCotangentCoefficients
    ((Coeff.dualPairing (hillHminusNumeratorHilbert C N t)).comp (R t.2)) m = 0
  rw [Coeff.hilbertCotangentCoefficients_apply]
  simp only [ContinuousLinearMap.comp_apply,hRe,Coeff.dualPairing_hilbert_single_right]
  rw [D.numeratorHilbert_spec.1 t ht,hillHminusNumeratorCoordinates,dif_neg (by omega : ¬ 0 < m)]

/-- A single native Hilbert-valued contour integral equals the exact
Kronecker basis vector, including its nonpositive output coordinates. -/
theorem normalizedNumeratorSequence_period
    (T R : PeriodOneHminusOne → (Coeff 2 →L[ℂ] Coeff 2))
    (k : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ V)
    (hentry : ∀ m j : ℤ, (T q (lp.single 2 j 1)) m = hillHminusPeriodMatrix C N q m j)
    (hTR : (T q).comp (R q) = ContinuousLinearMap.id ℂ (Coeff 2)) :
    (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      ((2*z)/hillHminusContinuedRoot (z^2,q)) •
        hillHminusNormalizedNumeratorSequence C N R (z^2,q)) = lp.single 2 (k : ℤ) 1 := by
  have hm := map_circleIntegral (Coeff.hilbertMatrixTranspose (R q))
    (D.numerator_contour_integrable k q hq)
  simp only [map_smul] at hm
  change (2*(Real.pi : ℂ))⁻¹ •
    (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
      ((2*z)/hillHminusContinuedRoot (z^2,q)) •
        Coeff.hilbertMatrixTranspose (R q) (hillHminusNumeratorHilbert C N (z^2,q))) = _
  rw [← hm]
  ext m
  change (2*(Real.pi : ℂ))⁻¹ *
    Coeff.hilbertCotangentCoefficients
      ((Coeff.dualPairing (hillHminusNumeratorContourVector C N k q)).comp (R q)) m = _
  rw [Coeff.hilbertCotangentCoefficients_apply]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Coeff.dualPairing_hilbert_comm]
  have hr := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L (R q (lp.single 2 m 1)))
    (D.hilbertPeriod_eq_row k q hq (T q) hentry)
  change (2*(Real.pi : ℂ))⁻¹ * Coeff.dualPairing
    (R q (lp.single 2 m 1)) (hillHminusNumeratorContourVector C N k q) =
      (T q (R q (lp.single 2 m 1))) (k : ℤ) at hr
  rw [hr]
  have he := congrArg (fun L : Coeff 2 →L[ℂ] Coeff 2 => L (lp.single 2 m 1)) hTR
  change T q (R q (lp.single 2 m 1)) = lp.single 2 m 1 at he
  rw [he]
  simp only [lp.single_apply,Pi.single_apply]
  simp only [eq_comm]

end HillHminusUniformPeriodData
end NLS.KdV
