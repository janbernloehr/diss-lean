import NLS.MKdV.MiuraL2CartesianProperness
import NLS.ZakharovShabat.SourceDiagonalActionFree
import NLS.ZakharovShabat.SourceBirkhoffFourier
import NLS.ZakharovShabat.SourceBirkhoffImageInverse

/-! # The actual free Cartesian differential

At the zero profile all NLS rectangular coordinates vanish. Differentiating
the regularized physical scaling therefore contributes no derivative of
the scaling factor. The actual Cartesian differential is the signed scalar
Fourier transform times the positive inverse-square-root frequency.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraL2CartesianCoordinates_zero (n : ℕ) :
    miuraL2CartesianCoordinates n 0 = 0 := by
  simp [miuraL2CartesianCoordinates,miuraActionFlowFamily.data.birkhoff_map_zero]

/-- Exact evaluation of the bounded original-NLS Jacobian after the scalar diagonal. -/
theorem hasFDerivAt_miuraNLSCoordinates_zero :
    HasFDerivAt (fun a : Coeff 2 => sourceBirkhoffMap (by simp) (by norm_num)
      miuraActionFlowFamily.psi (scalarL2Diagonal a))
      ((sourceBirkhoffFourier (p := 2)).comp scalarL2Diagonal) 0 := by
  let D := miuraActionFlowFamily.data
  have h0 := D.real_subset (0 : realTypeSourceSubmodule 2).property
  have hd := (D.analytic 0 h0).differentiableAt.hasFDerivAt
  change HasFDerivAt _ (sourceBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi 0) 0 at hd
  rw [D.jacobian_zero] at hd
  have he : HasFDerivAt (sourceBirkhoffMap (by simp) (by norm_num) miuraActionFlowFamily.psi)
      (sourceBirkhoffFourier (p := 2)) (scalarL2Diagonal (0 : Coeff 2)) := by
    simpa only [map_zero] using! hd
  exact he.comp (0 : Coeff 2) scalarL2Diagonal.hasFDerivAt

/-- Every selected Cartesian differential is the correctly signed and
scaled Fourier pair, including the collapsed selected action at zero. -/
theorem fderiv_miuraL2CartesianCoordinates_zero (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2) :
    (fderiv ℂ (miuraL2CartesianCoordinates n) 0) h =
      (sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
          (sourceBirkhoffFourier (scalarL2Diagonal h)).1 n,
       -(sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
          (sourceBirkhoffFourier (scalarL2Diagonal h)).2 n)) := by
  let φ : realDiagonalSourceLocus 2 := ⟨0,⟨by intro j; simp,by rfl⟩⟩
  obtain ⟨U,_,hφU,_,hr,_⟩ := exists_local_sourceDiagonalActionRoot_analytic_factor
    (by simp) (by norm_num) φ n (by omega)
  have ht : HasFDerivAt (fun a : Coeff 2 => sourceDiagonalActionRoot (by simp) (by norm_num) n (scalarL2Diagonal a))
      ((fderiv ℂ (sourceDiagonalActionRoot (p := 2) (by simp) (by norm_num) n) (0 : CoeffPair 2)).comp scalarL2Diagonal) 0 := by
    have h0 : scalarL2Diagonal (0 : Coeff 2) ∈ U := by simpa only [map_zero] using hφU
    have hd := (hr (scalarL2Diagonal (0 : Coeff 2)) h0).differentiableAt.hasFDerivAt.comp
      (0 : Coeff 2) scalarL2Diagonal.hasFDerivAt
    simpa only [map_zero] using! hd
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).comp
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).comp
    (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  have hx := ex.hasFDerivAt.comp 0 hasFDerivAt_miuraNLSCoordinates_zero
  have hy := ey.hasFDerivAt.comp 0 hasFDerivAt_miuraNLSCoordinates_zero
  have hd := ((ht.mul hx).prodMk ((ht.mul hy).neg)).fderiv
  have he := congrArg (fun L : Coeff 2 →L[ℂ] (ℂ × ℂ) => L h) hd
  change (fderiv ℂ (fun a => miuraL2CartesianCoordinates n a) 0) h = _
  simpa [miuraL2CartesianCoordinates,ex,ey,Function.comp_def,lp.evalCLM,
    miuraActionFlowFamily.data.birkhoff_map_zero] using! he

/-- Explicit raw Fourier coefficients and physical free scale. -/
theorem fderiv_miuraL2CartesianCoordinates_zero_explicit (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2) :
    (fderiv ℂ (miuraL2CartesianCoordinates n) 0) h =
      ((Real.sqrt ((2*Real.pi*(n : ℝ))⁻¹) : ℂ)*(-(h (-(n : ℤ))+h n)/(Real.sqrt 2 : ℂ)),
       -((Real.sqrt ((2*Real.pi*(n : ℝ))⁻¹) : ℂ)*((h (-(n : ℤ))-h n)/((Real.sqrt 2 : ℂ)*I)))) := by
  rw [fderiv_miuraL2CartesianCoordinates_zero n hn h,
    sourceDiagonalActionRoot_zero (by simp) (by norm_num) n (by omega),
    sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,scalarL2Diagonal_fst,scalarL2Diagonal_snd]
  norm_cast

end NLS.MKdV
