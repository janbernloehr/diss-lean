import NLS.MKdV.PhysicalMiuraFundamentalMatrix
import NLS.Articles.MKdVNLSHierarchies.DiscriminantIdentity

/-! # Lemma 2's literal physical matrix on the original complex H1 domain

The Hill matrix uses the actual independent scalar solutions and their
actual derivatives with position/derivative initial data. The ZS matrix
uses the original diagonal H1 profile. No smoothness strengthening is used.
-/
noncomputable section
open Set Complex Matrix MeasureTheory NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.Articles.MKdVNLSHierarchies

def hillFundamentalMatrix (a : ScalarDomain 2) (μ : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  physicalMiuraFundamentalMatrix (periodOneMiuraCurve a) μ x

def miuraTransferMatrix (a : ScalarDomain 2) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  miuraPaperGauge (periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))) z

theorem lemma2_transfer_matrix_entries (a : ScalarDomain 2) (z : ℂ) (x : ℝ) :
    miuraTransferMatrix a z x =
      !![1,I;periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))-I*z,
        I*periodOneSobolevSynthesis a (x : AddCircle (2:ℝ))-z] := rfl

theorem lemma2_transfer_matrix_determinant (a : ScalarDomain 2) (z : ℂ) (x : ℝ) :
    (miuraTransferMatrix a z x).det = -2*z := det_miuraPaperGauge _ _

theorem lemma2_transfer_matrix_invertible_iff (a : ScalarDomain 2) (z : ℂ) (x : ℝ) :
    IsUnit (miuraTransferMatrix a z x) ↔ z ≠ 0 := isUnit_miuraPaperGauge_iff _ _

theorem lemma2_transfer_matrix_periodic (a : ScalarDomain 2) (z : ℂ) :
    Function.Periodic (miuraTransferMatrix a z) 1 := by
  intro x
  exact congrArg (fun u => miuraPaperGauge u z) (periodOneSobolevSynthesis_periodic a x)

theorem lemma2_h1_matrix_conjugacy (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) (x : Icc (0:ℝ) 1) :
    hillFundamentalMatrix a (z^2) x =
      miuraTransferMatrix a z x*classicalFundamentalMatrix
        (classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z x*
          (miuraTransferMatrix a z 0)⁻¹ := by
  have h := physicalMiuraFundamentalMatrix_eq_ZS_conjugate (periodOneMiuraCurve a) z hz x
  have hΦ : (periodOneMiuraCurve a).prodMk (periodOneMiuraCurve a) =
      classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a) := rfl
  rw [hΦ] at h
  simpa only [hillFundamentalMatrix,miuraTransferMatrix,periodOneMiuraCurve_apply] using h

theorem lemma2_h1_endpoint_conjugacy (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    hillFundamentalMatrix a (z^2) 1 =
      miuraTransferMatrix a z 0*classicalMonodromy
        (classicalSobolevPotential (Coeff.periodDoubleSobolev a,Coeff.periodDoubleSobolev a)) z*
          (miuraTransferMatrix a z 0)⁻¹ := by
  have h := lemma2_h1_matrix_conjugacy a z hz ⟨1,by norm_num⟩
  have hp : miuraTransferMatrix a z 1 = miuraTransferMatrix a z 0 := by
    simpa only [zero_add] using lemma2_transfer_matrix_periodic a z 0
  simpa only [hp,classicalMonodromy] using h

/-- The matrix's columns have the physical H1 Miura potential and exact
position/derivative initial conditions, from the independent scalar IVP. -/
theorem lemma2_h1_physical_column (a : ScalarDomain 2) (μ : ℂ) (v : ℂ × ℂ) :
    let g := physicalMiuraSolution (periodOneMiuraCurve a) μ v
    AbsolutelyContinuousOnInterval g 0 1 ∧
      AbsolutelyContinuousOnInterval (deriv g) 0 1 ∧
      g 0 = v.1 ∧ deriv g 0 = v.2 ∧
      ∀ᵐ x : ℝ, x ∈ Ioo (0:ℝ) 1 →
        -deriv (deriv g) x+
          miuraPotential (fun y => periodOneSobolevSynthesis a (y : AddCircle (2:ℝ))) x*g x = μ*g x :=
  hill_column_spec a μ v

end NLS.Articles.MKdVNLSHierarchies
