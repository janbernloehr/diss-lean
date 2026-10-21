import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties
import NLS.Dynamics.RealComplexBirkhoffCoordinates

/-! # Nonlinear Parseval in the scalar physical L2 norm

The normalization in the introduction, printed p. 10, retains both real coordinates
and the physical pair (u, conjugate u). The normalized complex coefficient is (x-i*y)/sqrt(2).
-/

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Conjugation preserves the scalar physical L2 norm. -/
theorem norm_intervalL2_star (u : IntervalL2) : ‖star u‖ = ‖u‖ := by
  have he : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), ‖(star u) x‖ = ‖u x‖ := by
    filter_upwards [Lp.coeFn_star u] with x hx
    rw [hx]
    exact Complex.norm_conj _
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))

/-- Put a scalar unit-interval L2 class into the physical real pair. -/
def scalarPhysicalRealInput (u : IntervalL2) : physicalRealSubmodule :=
  ⟨WithLp.toLp 2 (u,star u),by
    rw [mem_physicalRealSubmodule]
    change (fun x => (star u) x) =ᵐ[volume.restrict (Ioc 0 1)]
      (fun x => (starRingEnd ℂ) (u x))
    exact Lp.coeFn_star u⟩

/-- The physical pair contains both conjugate components. -/
theorem norm_sq_scalarPhysicalRealInput (u : IntervalL2) :
    ‖scalarPhysicalRealInput u‖^2 = 2*‖u‖^2 := by
  change ‖WithLp.toLp 2 (u,star u)‖^2 = _
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖u‖^2+‖star u‖^2 = _
  rw [norm_intervalL2_star]
  ring

/-- The normalized complex coordinate is literally (x-i*y)/sqrt(2). -/
theorem encodeReal_fst_normalized (z : RealCoeff 2 × RealCoeff 2) (n : ℤ) :
    (Birkhoff.encodeReal z).1 n =
      ((z.1 n : ℂ)-I*(z.2 n : ℂ))/(Real.sqrt 2:ℂ) := by
  change (Birkhoff.rectangularToComplex
    (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) z)).1 n = _
  rw [Birkhoff.rectangularToComplex_fst]
  change Birkhoff.complexCoordinateScale*((z.1 n:ℂ)-I*(z.2 n:ℂ)) = _
  rw [Birkhoff.complexCoordinateScale, div_eq_mul_inv, mul_comm]

/-- The squared modulus of each normalized coefficient is its rectangular action. -/
theorem norm_sq_encodeReal_fst_apply (z : RealCoeff 2 × RealCoeff 2) (n : ℤ) :
    ‖(Birkhoff.encodeReal z).1 n‖^2 = ((z.1 n)^2+(z.2 n)^2)/2 := by
  rw [encodeReal_fst_normalized, norm_div, div_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]
  ring

/-- Normalized complex coordinates carry half the rectangular squared norm. -/
theorem norm_sq_encodeReal_fst (z : RealCoeff 2 × RealCoeff 2) :
    ‖(Birkhoff.encodeReal z).1‖^2 = (‖z.1‖^2+‖z.2‖^2)/2 := by
  have hs (a : RealCoeff 2) : HasSum (fun n : ℤ => (a n)^2) (‖a‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs] using
      lp.hasSum_norm (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal) a
  have ht : HasSum (fun n : ℤ => ‖(Birkhoff.encodeReal z).1 n‖^2)
      (‖(Birkhoff.encodeReal z).1‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      lp.hasSum_norm (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal) (Birkhoff.encodeReal z).1
  simp only [norm_sq_encodeReal_fst_apply] at ht
  exact ht.unique (((hs z.1).add (hs z.2)).div_const 2)

/-- Scalar nonlinear Fourier coordinates with the physical square-root-two normalization. -/
def scalarNonlinearFourier (u : IntervalL2) : Coeff 2 :=
  (Birkhoff.encodeReal (intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).ofLp).1

/-- The scalar nonlinear Fourier coefficients are the literal normalized physical coordinates. -/
theorem scalarNonlinearFourier_apply (u : IntervalL2) (n : ℤ) :
    scalarNonlinearFourier u n =
      (((intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).fst n : ℂ)-
        I*((intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).snd n : ℂ))/
        (Real.sqrt 2:ℂ) := encodeReal_fst_normalized _ n

/-- Nonlinear Parseval in the scalar physical L2 norm. -/
theorem scalarNonlinearFourier_norm (u : IntervalL2) :
    ‖scalarNonlinearFourier u‖ = ‖u‖ := by
  have h := norm_sq_encodeReal_fst
    (intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).ofLp
  have hp := congrArg (fun t : ℝ => t^2)
    (intrinsicPhysicalBirkhoffMap_norm (scalarPhysicalRealInput u))
  rw [WithLp.prod_norm_sq_eq_of_L2,norm_sq_scalarPhysicalRealInput] at hp
  change ‖(intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).ofLp.1‖^2+
    ‖(intrinsicPhysicalBirkhoffMap (scalarPhysicalRealInput u)).ofLp.2‖^2 = 2*‖u‖^2 at hp
  change ‖scalarNonlinearFourier u‖^2 = _ at h
  nlinarith [norm_nonneg (scalarNonlinearFourier u),norm_nonneg u]

/-- The convergent sum of squared nonlinear coefficients is the scalar physical mass. -/
theorem scalarNonlinearFourier_hasSum_norm_sq (u : IntervalL2) :
    HasSum (fun n : ℤ => ‖scalarNonlinearFourier u n‖^2) (‖u‖^2) := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,scalarNonlinearFourier_norm] using
    lp.hasSum_norm (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal) (scalarNonlinearFourier u)

end NLS.ZakharovShabat
