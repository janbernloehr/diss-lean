import NLS.Fourier.UnitIntervalL2Product

/-! # Maximal first-order interval regularity with a boundary defect

An L2 weak solution of v'=u*v+b, with u and b in L2, is H1 on the
original interval. The constant Fourier defect is retained as the jump
of its endpoint values. There is no periodic quasi-derivative hypothesis.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open NLS.FunctionalAnalysis

@[simp] theorem unitFourierCoefficient_unitL2Synthesis (a : Coeff 2) (n : ℤ) :
    unitFourierCoefficient (unitL2SynthesisEquiv a) n = a n := by
  rw [unitFourierCoefficient_eq_intervalFourierCoefficient]
  exact unitL2SynthesisLinear_coefficient a n

/-- The weak coefficient equation itself recovers the entire interval H1
representative and its nonperiodic boundary values. -/
theorem exists_intervalH1_of_weak_firstOrder (u v b : Coeff 2) (c : ℂ)
    (he : ∀ n : ℤ, 2*I*(Real.pi:ℂ)*n*v n =
      (∑' k : ℤ, u (n-k)*v k)+b n+c) :
    ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
      MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) ∧
      unitL2SynthesisEquiv v =ᵐ[volume.restrict (Ioc 0 1)] G ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1),
        HasDerivAt G (unitL2SynthesisEquiv u x*G x+unitL2SynthesisEquiv b x) x) ∧
      G 1-G 0 = -c := by
  let U := unitL2SynthesisEquiv u
  let V := unitL2SynthesisEquiv v
  let B := unitL2SynthesisEquiv b
  have hU := Lp.memLp U
  have hV := Lp.memLp V
  have hB := Lp.memLp B
  have hUV : IntervalIntegrable (fun x => U x*V x) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hU.integrable_mul hV)
  have hBi : IntervalIntegrable B volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hB.integrable (by norm_num))
  have hcoef (n : ℤ) : 2*I*(Real.pi:ℂ)*n*unitFourierCoefficient V n =
      unitFourierCoefficient (fun x => U x*V x+B x) n+c := by
    rw [unitFourierCoefficient_add _ _ hUV hBi,
      unitFourierCoefficient_L2_product _ _ hU hV]
    simpa only [U, V, B, unitFourierCoefficient_unitL2Synthesis] using he n
  obtain ⟨G, hGc, hGa, hVG, hGd, hjump⟩ :=
    exists_ac_unitInterval_representative_of_fourier_equation V
      (fun x => U x*V x+B x) hV (hUV.add hBi) c hcoef
  have hder : ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G (U x*G x+B x) x := by
    filter_upwards [hGd, hVG] with x hx hvg
    simpa only [hvg] using hx
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc.continuousOn
  have hUG : MemLp (fun x => U x*G x) 2 (volume.restrict (Ioc 0 1)) := by
    simpa only [mul_comm] using memLp_unitInterval_bounded_mul U G hU hGc K hK
  have hregular : MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) := by
    apply (memLp_congr_ae ?_).mp (hUG.add hB)
    filter_upwards [hder] with x hx
    exact hx.deriv.symm
  exact ⟨G, hGc, hGa, hregular, hVG, hder, hjump⟩

end NLS.Fourier
