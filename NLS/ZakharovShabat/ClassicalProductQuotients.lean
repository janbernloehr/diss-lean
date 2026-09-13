import NLS.ZakharovShabat.ClassicalDiscriminantMultiplicity
import NLS.ComplexAnalysis.AnalyticQuotientUniqueness

/-!
# Entire normalization factors for the classical spectral products

The shifted classical traces differ from the canonical parity products by
explicit entire nonvanishing quotient functions. The full characteristic
function has the corresponding entire factor as well. Determining these
functions from asymptotics remains the normalization problem.
-/

noncomputable section
open Set Complex Matrix MeasureTheory Filter Topology NLS.Fourier NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- Filled quotient of the shifted classical trace by its intrinsic parity product. -/
def classicalParityProductQuotient (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ)) (r : ℤ) : ℂ → ℂ :=
  analyticQuotient (fun z => classicalDiscriminant Φ z-2*wave r 1) (canonicalParityProduct (by simp) φ r)

/-- Filled quotient of the full classical characteristic function by its canonical product. -/
def classicalPeriodicProductQuotient (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ)) : ℂ → ℂ :=
  analyticQuotient (fun z => (classicalDiscriminant Φ z)^2-4) (canonicalPeriodicProduct (by simp) φ)

private theorem shiftedTrace_analytic (Φ : Curve (ℂ × ℂ)) (r : ℤ) :
    AnalyticOnNhd ℂ (fun z => classicalDiscriminant Φ z-2*wave r 1) univ := by
  intro z _
  have hpair : AnalyticAt ℂ (fun w : ℂ => (w,Φ)) z := analyticAt_id.prod analyticAt_const
  exact ((analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp
    (f := fun w : ℂ => (w,Φ)) hpair).sub analyticAt_const

private theorem parityShift_order_eq (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    analyticOrderAt (fun w => classicalDiscriminant Φ w-2*wave r 1) z =
      analyticOrderAt (canonicalParityProduct (by simp) φ r) z := by
  rcases hr with rfl | rfl
  · simpa only [wave_zero,mul_one] using
      (analyticOrderAt_canonicalEven_eq_classicalDiscriminant_sub_two φ hφ Φ hΦ z).symm
  · have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
    simpa only [hw,mul_neg_one,sub_neg_eq_add] using
      (analyticOrderAt_canonicalOdd_eq_classicalDiscriminant_add_two φ hφ Φ hΦ z).symm

private theorem parityProduct_finite (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    analyticOrderAt (canonicalParityProduct (by simp) φ r) z ≠ ⊤ := by
  rw [((canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).2 z).1]
  exact ENat.natCast_ne_top _

private theorem fullTrace_analytic (Φ : Curve (ℂ × ℂ)) :
    AnalyticOnNhd ℂ (fun z => (classicalDiscriminant Φ z)^2-4) univ := by
  intro z _
  have hpair : AnalyticAt ℂ (fun w : ℂ => (w,Φ)) z := analyticAt_id.prod analyticAt_const
  exact (((analyticOnNhd_classicalDiscriminant_joint (z,Φ) (mem_univ _)).comp
    (f := fun w : ℂ => (w,Φ)) hpair).pow 2).sub analyticAt_const

private theorem periodicProduct_finite (φ : PairSpace 2) (z : ℂ) :
    analyticOrderAt (canonicalPeriodicProduct (by simp) φ) z ≠ ⊤ := by
  rw [analyticOrderAt_canonicalPeriodicProduct (by simp) (by norm_num)]
  exact ENat.natCast_ne_top _

/-- Both actual parity normalization factors are entire in the spectral parameter. -/
theorem analyticOnNhd_classicalParityProductQuotient
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) : AnalyticOnNhd ℂ (classicalParityProductQuotient φ Φ r) univ :=
  analyticOnNhd_analyticQuotient (shiftedTrace_analytic Φ r)
    (canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).1
    (parityShift_order_eq φ hφ Φ hΦ r hr) (parityProduct_finite φ hφ r hr)

/-- The actual parity normalization factors never vanish, including at spectral collisions. -/
theorem classicalParityProductQuotient_ne_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) : classicalParityProductQuotient φ Φ r z ≠ 0 :=
  analyticQuotient_ne_zero (shiftedTrace_analytic Φ r)
    (canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).1
    (parityShift_order_eq φ hφ Φ hΦ r hr) (parityProduct_finite φ hφ r hr) z

/-- The classical shifted trace factors exactly into the canonical parity product and an entire unit. -/
theorem classicalParityProductQuotient_mul
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    classicalParityProductQuotient φ Φ r z*canonicalParityProduct (by simp) φ r z =
      classicalDiscriminant Φ z-2*wave r 1 :=
  analyticQuotient_mul (shiftedTrace_analytic Φ r)
    (canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).1
    (parityShift_order_eq φ hφ Φ hΦ r hr) z

/-- The full classical normalization factor is entire. -/
theorem analyticOnNhd_classicalPeriodicProductQuotient
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) :
    AnalyticOnNhd ℂ (classicalPeriodicProductQuotient φ Φ) univ :=
  analyticOnNhd_analyticQuotient (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ)
    (fun z => (analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ z).symm)
    (periodicProduct_finite φ)

/-- The full classical normalization factor is nonvanishing. -/
theorem classicalPeriodicProductQuotient_ne_zero
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : classicalPeriodicProductQuotient φ Φ z ≠ 0 :=
  analyticQuotient_ne_zero (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ)
    (fun z => (analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ z).symm)
    (periodicProduct_finite φ) z

/-- The full classical characteristic function is its canonical product times the entire normalization factor. -/
theorem classicalPeriodicProductQuotient_mul
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (z : ℂ) : classicalPeriodicProductQuotient φ Φ z*canonicalPeriodicProduct (by simp) φ z =
      (classicalDiscriminant Φ z)^2-4 :=
  analyticQuotient_mul (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ)
    (fun z => (analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ z).symm) z

/-- Away from the parity spectrum, the normalization factor is the ordinary quotient. -/
theorem classicalParityProductQuotient_eq_div
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0) (Φ : Curve (ℂ × ℂ))
    (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) (hz : canonicalParityProduct (by simp) φ r z ≠ 0) :
    classicalParityProductQuotient φ Φ r z =
      (classicalDiscriminant Φ z-2*wave r 1)/canonicalParityProduct (by simp) φ r z :=
  analyticQuotient_eq_div (shiftedTrace_analytic Φ r)
    (canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).1 z hz

/-- Away from the periodic spectrum, the full normalization factor is ordinary division. -/
theorem classicalPeriodicProductQuotient_eq_div
    (φ : PairSpace 2) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (hz : canonicalPeriodicProduct (by simp) φ z ≠ 0) :
    classicalPeriodicProductQuotient φ Φ z =
      ((classicalDiscriminant Φ z)^2-4)/canonicalPeriodicProduct (by simp) φ z :=
  analyticQuotient_eq_div (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ) z hz

/-- The two entire parity factors multiply to the entire full normalization factor. -/
theorem classicalParityProductQuotients_mul
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ) :
    classicalParityProductQuotient φ Φ 0*classicalParityProductQuotient φ Φ 1 =
      classicalPeriodicProductQuotient φ Φ := by
  symm
  apply analyticQuotient_eq_of_factorization (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ)
    (fun z => (analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ z).symm)
    (periodicProduct_finite φ)
    ((analyticOnNhd_classicalParityProductQuotient φ hφ Φ hΦ 0 (Or.inl rfl)).mul
      (analyticOnNhd_classicalParityProductQuotient φ hφ Φ hΦ 1 (Or.inr rfl)))
  intro z
  have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
  calc
    _ = (classicalParityProductQuotient φ Φ 0 z*canonicalParityProduct (by simp) φ 0 z)*
        (classicalParityProductQuotient φ Φ 1 z*canonicalParityProduct (by simp) φ 1 z) := by
      rw [← canonicalParityProducts_mul (by simp) (by norm_num) φ hφ z]
      ring
    _ = _ := by
      rw [classicalParityProductQuotient_mul φ hφ Φ hΦ 0 (Or.inl rfl),
        classicalParityProductQuotient_mul φ hφ Φ hΦ 1 (Or.inr rfl),wave_zero,hw]
      ring

/-- A quotient limit of one proves the exact parity product normalization. -/
theorem canonicalParity_eq_classical_of_quotient_tendsto_one
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (r : ℤ) (hr : r = 0 ∨ r = 1)
    (hlim : Tendsto (classicalParityProductQuotient φ Φ r) (cocompact ℂ) (𝓝 1)) (z : ℂ) :
    canonicalParityProduct (by simp) φ r z = classicalDiscriminant Φ z-2*wave r 1 := by
  have h := eq_const_mul_of_tendsto_analyticQuotient (shiftedTrace_analytic Φ r)
    (canonicalParityProduct_spec (by simp) (by norm_num) φ hφ r hr).1
    (parityShift_order_eq φ hφ Φ hΦ r hr) (parityProduct_finite φ hφ r hr) hlim z
  simpa only [one_mul] using h.symm

/-- A quotient limit of one proves the exact full periodic product normalization. -/
theorem canonicalPeriodic_eq_classical_of_quotient_tendsto_one
    (φ : PairSpace 2) (hφ : φ ∈ pairParitySubspace 0)
    (Φ : Curve (ℂ × ℂ)) (hΦ : physicalBase φ =ᵐ[volume.restrict (Ioc 0 1)] extend Φ)
    (hlim : Tendsto (classicalPeriodicProductQuotient φ Φ) (cocompact ℂ) (𝓝 1)) (z : ℂ) :
    canonicalPeriodicProduct (by simp) φ z = (classicalDiscriminant Φ z)^2-4 := by
  have h := eq_const_mul_of_tendsto_analyticQuotient (fullTrace_analytic Φ)
    (analyticOnNhd_canonicalPeriodicProduct (by simp) (by norm_num) φ)
    (fun z => (analyticOrderAt_canonicalPeriodic_eq_classicalDiscriminant_sq_sub_four φ hφ Φ hΦ z).symm)
    (periodicProduct_finite φ) hlim z
  simpa only [one_mul] using h.symm

end NLS.ZakharovShabat
