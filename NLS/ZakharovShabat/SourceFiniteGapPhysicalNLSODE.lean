import NLS.ZakharovShabat.SourceFiniteGapPhysicalNLSCoefficients
import NLS.ZakharovShabat.SourcePhysicalEnergyHamiltonianODE

/-! # The classical physical NLS field is the finite-gap source velocity

The full Hilbert-norm trajectory derivative equals the Fourier realization
of the classical spatial NLS vector field. Every Fourier coefficient obeys
the corresponding time equation, with the scalar defocusing NLS sign and
normalization. `SourceFiniteGapPointwiseNLS` combines these identities with
H¹ time regularity to prove the physical equation pointwise.
-/
noncomputable section
open Set Complex NLS.Fourier
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual source-norm derivative equals the original classical physical NLS field. -/
theorem hasDerivAt_hamiltonianOrdinarySourceFlow_physicalNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) :
    HasDerivAt (fun r => (A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val)
      (sourceFiniteGapPhysicalNLSCoefficients (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
        (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)) time := by
  obtain ⟨L,hL,hd⟩ := A.exists_physicalEnergyHamiltonian_ODE hs D φ hf time
  rw [sourceFiniteGapPhysicalNLSCoefficients_eq_HamiltonianDirection _ _ L hL]
  exact hd

/-- Every signed Fourier mode satisfies both component equations of physical NLS. -/
theorem hasDerivAt_hamiltonianOrdinarySourceFlow_physical_coordinates
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) (n : ℤ) :
    let ψ := A.hamiltonianOrdinarySourceFlow D le_rfl φ time
    let hfψ := A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time
    HasDerivAt (fun r => (A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val.fst n)
      (periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) ψ hfψ).1 n) time ∧
    HasDerivAt (fun r => (A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val.snd n)
      (periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) ψ hfψ).2 n) time := by
  dsimp only
  have ht := A.hasDerivAt_hamiltonianOrdinarySourceFlow_physicalNLS hs D φ hf time
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (WithLp.fstL 2 ℂ (Coeff 2) (Coeff 2))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp (WithLp.sndL 2 ℂ (Coeff 2) (Coeff 2))
  have hx := (ex.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time ht
  have hy := (ey.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt time ht
  change HasDerivAt (fun r => (A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val.fst n)
    ((sourceFiniteGapPhysicalNLSCoefficients _ _).fst n) time at hx
  change HasDerivAt (fun r => (A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val.snd n)
    ((sourceFiniteGapPhysicalNLSCoefficients _ _).snd n) time at hy
  rw [(sourceFiniteGapPhysicalNLSCoefficients_apply _ _ n).1] at hx
  rw [(sourceFiniteGapPhysicalNLSCoefficients_apply _ _ n).2] at hy
  exact ⟨hx,hy⟩

/-- The first component has precisely `i u_t = -u_xx + 2 |u|² u` in each Fourier mode. -/
theorem hasDerivAt_hamiltonianOrdinarySourceFlow_scalarNLS_fourier
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) (n : ℤ) :
    let ψ := A.hamiltonianOrdinarySourceFlow D le_rfl φ time
    let hfψ := A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time
    let u := (sourceFiniteGapPhysicalPair (by simp) (by norm_num) ψ hfψ).1
    HasDerivAt (fun r => I*(A.hamiltonianOrdinarySourceFlow D le_rfl φ r).val.fst n)
      (periodOneCoefficient (fun x => -deriv (deriv u) x+2*(‖u x‖^2 : ℝ)*u x) n) time := by
  dsimp only
  have hd := (A.hasDerivAt_hamiltonianOrdinarySourceFlow_physical_coordinates hs D φ hf time n).1.const_mul I
  have he := sourceFiniteGapPhysicalNLSVectorField_scalar (by simp) (by norm_num)
    (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
    (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)
  have hcoeff := fourierCoeffOn.const_smul
    (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1 I n (by norm_num : (0 : ℝ) < 1)
  change periodOneCoefficient (fun x => I*(sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)).1 x) n =
    I*periodOneCoefficient _ n at hcoeff
  simp only [he] at hcoeff
  rw [← hcoeff] at hd
  exact hd

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
