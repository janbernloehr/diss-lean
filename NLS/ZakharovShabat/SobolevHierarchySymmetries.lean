import NLS.ZakharovShabat.SobolevHamiltonianReflection

/-! # Component-swap symmetry of the physical Sobolev NLS hierarchy

These consequences reuse the physical signed-swap and reciprocal-rescaling
identities. All Hamiltonians retain their existing normalization. The derivative
statements are identities of complex Fréchet covectors, before identifying them
with distributional or L² gradients.
-/
noncomputable section
open Complex
namespace NLS.ZakharovShabat

/-- Exchange the two original complex Sobolev fields. -/
def hierarchyComponentSwap (s : ℕ) : SobolevSource s →L[ℂ] SobolevSource s :=
  (ContinuousLinearMap.snd ℂ (ScalarSobolev s) (ScalarSobolev s)).prod
    (ContinuousLinearMap.fst ℂ (ScalarSobolev s) (ScalarSobolev s))

@[simp] theorem hierarchyComponentSwap_apply (s : ℕ) (ab : SobolevSource s) :
    hierarchyComponentSwap s ab = (ab.2, ab.1) := rfl

/-- Simultaneously negating both fields preserves the physical Hamiltonians. -/
theorem sobolevNLSHamiltonian_neg
    (s k : ℕ) (hk : k ≤ s+1) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s (-ab.1, -ab.2) k hk =
      sobolevNLSHamiltonian s ab k hk := by
  simpa only [inv_neg, inv_one, neg_one_smul] using
    sobolevNLSHamiltonian_reciprocal_rescaling s k hk ab (-1) (by norm_num)

/-- Unsigned component exchange has sign `(-1)^(k-1)` at positive order k. -/
theorem sobolevNLSHamiltonian_swap
    (s k : ℕ) (hk : k+1 ≤ s+1) (ab : SobolevSource s) :
    sobolevNLSHamiltonian s (ab.2, ab.1) (k+1) hk =
      (-1 : ℂ)^k * sobolevNLSHamiltonian s ab (k+1) hk := by
  have h := sobolevNLSHamiltonian_signedSwap s k hk ab
  rw [sobolevNLSHamiltonian_neg s (k+1) hk (ab.2, ab.1)] at h
  exact h

/-- Theorem 2(i)'s swap symmetry at the level of complex Fréchet covectors. -/
theorem fderiv_sobolevNLSHamiltonian_swap
    (s k : ℕ) (hk : k+1 ≤ s+1) (ab : SobolevSource s) :
    (fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd (k+1) hk)
      (hierarchyComponentSwap s ab)).comp (hierarchyComponentSwap s) =
      (-1 : ℂ)^k • fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd (k+1) hk) ab := by
  have hleft := ((analyticAt_sobolevNLSHamiltonian s (k+1) hk
    (hierarchyComponentSwap s ab)).differentiableAt.hasFDerivAt).comp ab
      (hierarchyComponentSwap s).hasFDerivAt
  have hf := (analyticAt_sobolevNLSHamiltonian s (k+1) hk ab).differentiableAt.hasFDerivAt
  have hright := hf.const_mul ((-1 : ℂ)^k)
  have he : (fun cd => sobolevNLSHamiltonian s (hierarchyComponentSwap s cd) (k+1) hk) =
      (fun cd => (-1 : ℂ)^k * sobolevNLSHamiltonian s cd (k+1) hk) :=
    funext fun cd => sobolevNLSHamiltonian_swap s k hk cd
  simp only [Function.comp_def] at hleft
  rw [he] at hleft
  exact hleft.unique hright

/-- Opposite nonzero field scalings, including every phase rotation. -/
def hierarchyReciprocalScaling (s : ℕ) (c : ℂ) : SobolevSource s →L[ℂ] SobolevSource s :=
  (c • ContinuousLinearMap.fst ℂ (ScalarSobolev s) (ScalarSobolev s)).prod
    (c⁻¹ • ContinuousLinearMap.snd ℂ (ScalarSobolev s) (ScalarSobolev s))

@[simp] theorem hierarchyReciprocalScaling_apply (s : ℕ) (c : ℂ) (ab : SobolevSource s) :
    hierarchyReciprocalScaling s c ab = (c • ab.1, c⁻¹ • ab.2) := rfl

/-- Theorem 2(i)'s phase symmetry as an identity of Fréchet covectors;
the stronger statement allows every nonzero complex scaling. -/
theorem fderiv_sobolevNLSHamiltonian_reciprocal_scaling
    (s k : ℕ) (hk : k ≤ s+1) (ab : SobolevSource s) (c : ℂ) (hc : c ≠ 0) :
    (fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd k hk)
      (hierarchyReciprocalScaling s c ab)).comp (hierarchyReciprocalScaling s c) =
      fderiv ℂ (fun cd => sobolevNLSHamiltonian s cd k hk) ab := by
  have hleft := ((analyticAt_sobolevNLSHamiltonian s k hk
    (hierarchyReciprocalScaling s c ab)).differentiableAt.hasFDerivAt).comp ab
      (hierarchyReciprocalScaling s c).hasFDerivAt
  have he : (fun cd => sobolevNLSHamiltonian s (hierarchyReciprocalScaling s c cd) k hk) =
      (fun cd => sobolevNLSHamiltonian s cd k hk) :=
    funext fun cd => sobolevNLSHamiltonian_reciprocal_rescaling s k hk cd c hc
  simp only [Function.comp_def] at hleft
  rw [he] at hleft
  exact hleft.fderiv.symm

end NLS.ZakharovShabat
