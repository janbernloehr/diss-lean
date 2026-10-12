import NLS.ZakharovShabat.SobolevRiccatiRescaling
import NLS.ZakharovShabat.SourceCorollaryH2

/-! # Rescaling invariance of the actual Sobolev Hamiltonians

The physical smooth identity determines both the original H^(k-1)
Hamiltonians and the odd Hamiltonians at their sharper H^m regularity.
Reciprocal rescaling is a consequence for nonzero scalars.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem hamiltonian_field_rescaling_of_smooth
    (s k : ℕ) (F : SobolevSource s → ℂ) (hF : Continuous F)
    (hclassical : ∀ (ab : SobolevSource s) (f g : ℝ → ℂ),
      ContDiff ℝ ∞ f → ContDiff ℝ ∞ g → Function.Periodic f 1 → Function.Periodic g 1 →
      (∀ j, ab.1.val j = periodOneCoefficient f j) →
      (∀ j, ab.2.val j = periodOneCoefficient g j) → F ab = classicalNLSHamiltonian f g k)
    (ab : SobolevSource s) (c : ℂ) : F (ab.1,c • ab.2) = F (c • ab.1,ab.2) := by
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => F (cd.1,c • cd.2)) (fun cd => F (c • cd.1,cd.2))
    (hF.comp (continuous_fst.prodMk (continuous_snd.const_smul c)))
    (hF.comp ((continuous_fst.const_smul c).prodMk continuous_snd)) (by
      intro cd f g hf hg hpf hpg ha hb
      have hcb (j : ℤ) : (c • cd.2).val j = periodOneCoefficient (c • g) j := by
        rw [periodOneCoefficient,fourierCoeffOn.const_smul]
        change c*cd.2.val j = c*periodOneCoefficient g j
        rw [hb]
      have hca (j : ℤ) : (c • cd.1).val j = periodOneCoefficient (c • f) j := by
        rw [periodOneCoefficient,fourierCoeffOn.const_smul]
        change c*cd.1.val j = c*periodOneCoefficient f j
        rw [ha]
      rw [hclassical (cd.1,c • cd.2) f (c • g) hf (hg.const_smul c)
          hpf (fun x => congrArg (fun y : ℂ => c*y) (hpg x)) ha hcb,
        hclassical (c • cd.1,cd.2) (c • f) g (hf.const_smul c) hg
          (fun x => congrArg (fun y : ℂ => c*y) (hpf x)) hpg hca hb,
        classicalNLSHamiltonian_field_rescaling])
  exact congrFun he ab

/-- The actual order-k Hamiltonian retains rescaling throughout its original Sobolev domain. -/
theorem sobolevNLSHamiltonian_field_rescaling
    (s k : ℕ) (hk : k ≤ s+1) (ab : SobolevSource s) (c : ℂ) :
    sobolevNLSHamiltonian s (ab.1,c • ab.2) k hk =
      sobolevNLSHamiltonian s (c • ab.1,ab.2) k hk :=
  hamiltonian_field_rescaling_of_smooth s k _ (continuous_sobolevNLSHamiltonian s k hk)
    (fun cd f g hf hg hpf hpg ha hb =>
      sobolevNLSHamiltonian_eq_classical s cd f g hf hg hpf hpg ha hb k hk) ab c

/-- H_(2m+1) retains the same identity on H^m, without imposing the stronger H^(2m) domain. -/
theorem sobolevOddHamiltonian_field_rescaling
    (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) (c : ℂ) :
    sobolevOddHamiltonian m hm (ab.1,c • ab.2) =
      sobolevOddHamiltonian m hm (c • ab.1,ab.2) :=
  hamiltonian_field_rescaling_of_smooth m (2*m+1) _ (continuous_sobolevOddHamiltonian m hm)
    (fun cd f g hf hg hpf hpg ha hb =>
      sobolevOddHamiltonian_eq_classical m hm cd f g hf hg hpf hpg ha hb) ab c

/-- Reciprocal field scaling preserves every actual Hamiltonian at its original regularity. -/
theorem sobolevNLSHamiltonian_reciprocal_rescaling
    (s k : ℕ) (hk : k ≤ s+1) (ab : SobolevSource s) (c : ℂ) (hc : c ≠ 0) :
    sobolevNLSHamiltonian s (c • ab.1,c⁻¹ • ab.2) k hk = sobolevNLSHamiltonian s ab k hk := by
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul,Prod.mk.eta] using
    sobolevNLSHamiltonian_field_rescaling s k hk (c • ab.1,ab.2) c⁻¹

/-- The odd Hamiltonians have reciprocal rescaling invariance on their full H^m domain. -/
theorem sobolevOddHamiltonian_reciprocal_rescaling
    (m : ℕ) (hm : 1 ≤ m) (ab : SobolevSource m) (c : ℂ) (hc : c ≠ 0) :
    sobolevOddHamiltonian m hm (c • ab.1,c⁻¹ • ab.2) = sobolevOddHamiltonian m hm ab := by
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul,Prod.mk.eta] using
    sobolevOddHamiltonian_field_rescaling m hm (c • ab.1,ab.2) c⁻¹

end NLS.ZakharovShabat
