import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.SpectralConvolution
import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.SobolevEmbedding

/-! The ACTUAL distributional Miura map preserves all-order Sobolev
regularity. Weighted convolution is the actual raw coefficient product;
the period-one derivative retains its factor2*pi. -/
noncomputable section
open scoped ENNReal
namespace NLS

/-- All-order Hilbert regularity yields the SAME coefficients in each
weighted Wiener space, without a finite Fourier support assumption. -/
theorem memlp_one_sobolev_of_all_hilbert (u : Coeff 2)
    (hu : ∀ s : ℝ, 0 ≤ s → Memℓp (fun k => (Weight.sobolev s k:ℂ)*u k) 2)
    (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*u k) 1 := by
  let a : WeightedCoeff (Weight.sobolev 1) 2 := ⟨fun k => (Weight.sobolev s k:ℂ)*u k,by
    change Memℓp (fun k => (Weight.sobolev 1 k:ℂ)*((Weight.sobolev s k:ℂ)*u k)) 2
    have h := hu (s+1) (by linarith)
    simpa only [Weight.sobolev_add,Complex.ofReal_mul,mul_assoc,mul_left_comm,mul_comm] using h⟩
  have h := (WeightedCoeff.sobolevToL1CLM 2 (by simp) a).property
  change Memℓp (fun k => WeightedCoeff.sobolevToL1CLM 2 (by simp) a k) 1 at h
  convert! h using 1
  funext k
  exact (WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) a k).symm

/-- The actual full Miura image is in EVERY nonnegative Sobolev space
when its actual L2 input has all-order Sobolev regularity. -/
theorem periodOneMiura_mem_all_sobolev (u : Coeff 2)
    (hu : ∀ s : ℝ, 0 ≤ s → Memℓp (fun k => (Weight.sobolev s k:ℂ)*u k) 2)
    (s : ℝ) (hs : 0 ≤ s) :
    Memℓp (fun k => (Weight.sobolev s k:ℂ)*(periodOneMiura u).val k) 2 := by
  let w := SpectralWeight.sobolev s hs
  let a : WeightedCoeff w.toWeight 2 := ⟨u,by
    change Memℓp (fun k => (w k:ℂ)*u k) 2
    simpa only [w,SpectralWeight.sobolev_apply] using hu s hs⟩
  let b : WeightedCoeff w.toWeight 1 := ⟨u,by
    change Memℓp (fun k => (w k:ℂ)*u k) 1
    simpa only [w,SpectralWeight.sobolev_apply] using (memlp_one_sobolev_of_all_hilbert u hu s hs)⟩
  have hc : Memℓp (fun k => (Weight.sobolev s k:ℂ)*(∑' j : ℤ, u (k-j)*u j)) 2 := by
    have h := (w.convolution a b).property
    change Memℓp (fun k => (w k:ℂ)*(w.convolution a b).val k) 2 at h
    convert! h using 1
    funext k
    have he := SpectralWeight.convolution_apply w a b k
    have hw : w k=Weight.sobolev s k := SpectralWeight.sobolev_apply s hs k
    calc
      (Weight.sobolev s k:ℂ)*(∑' j : ℤ, u (k-j)*u j)=
          (w k:ℂ)*(∑' j : ℤ, u (k-j)*u j) := by rw [hw]
      _=(w k:ℂ)*(w.convolution a b).val k :=
        (congrArg (fun z : ℂ => (w k:ℂ)*z) he).symm

  let v : WeightedCoeff (Weight.sobolev (s+1)) 2 := ⟨u,hu (s+1) (by linarith)⟩
  have hd : Memℓp (fun k => (Weight.sobolev s k:ℂ)*(2*Complex.I*(Real.pi:ℂ)*k*u k)) 2 := by
    have h := (WeightedCoeff.sobolevDerivative s v).property
    convert! h.const_mul (2:ℂ) using 1
    funext k
    rw [WeightedCoeff.sobolevDerivative_apply]
    change (Weight.sobolev s k:ℂ)*(2*Complex.I*(Real.pi:ℂ)*k*u k)=
      2*((Weight.sobolev s k:ℂ)*(Complex.I*(Real.pi:ℂ)*k*u k))
    ring
  have hh := hd.add hc
  change Memℓp (fun k => (Weight.sobolev s k:ℂ)*(2*Complex.I*(Real.pi:ℂ)*k*u k)+
    (Weight.sobolev s k:ℂ)*(∑' j : ℤ, u (k-j)*u j)) 2 at hh
  simpa only [periodOneMiura_apply,mul_add] using hh

end NLS
