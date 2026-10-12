import NLS.ZakharovShabat.NLSRiccatiRescaling
import NLS.ZakharovShabat.SourceLemmaH1

/-! # Rescaling on the original Sobolev and weak Riccati sources

Continuity and dense smooth Fourier sources transfer the actual recurrence
identity to every admissible Sobolev density and its next weak H^-1 density.
All complex scalars are allowed, including zero.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem periodOneCoefficient_smul_aux (f : ℝ → ℂ) (c : ℂ) (j : ℤ) :
    periodOneCoefficient (c • f) j = c*periodOneCoefficient f j :=
  fourierCoeffOn.const_smul _ _ _ _

/-- The next density retains rescaling at the weak H^-1 boundary of every H^s source. -/
theorem weakSobolevRiccatiDensity_field_rescaling (s : ℕ) (ab : SobolevSource s) (c : ℂ) :
    weakSobolevRiccatiDensity s (ab.1,c • ab.2) =
      c • weakSobolevRiccatiDensity s (c • ab.1,ab.2) := by
  have hd : Continuous (weakSobolevRiccatiDensity s) :=
    continuous_iff_continuousAt.mpr fun cd => (analyticAt_weakSobolevRiccatiDensity s cd).continuousAt
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => weakSobolevRiccatiDensity s (cd.1,c • cd.2))
    (fun cd => c • weakSobolevRiccatiDensity s (c • cd.1,cd.2))
    (hd.comp (continuous_fst.prodMk (continuous_snd.const_smul c)))
    ((hd.comp ((continuous_fst.const_smul c).prodMk continuous_snd)).const_smul c) (by
      intro cd f g hf hg hpf hpg ha hb
      apply Subtype.ext
      funext j
      change (weakSobolevRiccatiDensity s (cd.1,c • cd.2)).val j =
        c*(weakSobolevRiccatiDensity s (c • cd.1,cd.2)).val j
      have hcb (k : ℤ) : (c • cd.2).val k = periodOneCoefficient (c • g) k := by
        simp only [WeightedCoeff.smul_val,periodOneCoefficient_smul_aux,hb]
      have hca (k : ℤ) : (c • cd.1).val k = periodOneCoefficient (c • f) k := by
        simp only [WeightedCoeff.smul_val,periodOneCoefficient_smul_aux,ha]
      rw [weakSobolevRiccatiDensity_eq_classical_coefficients s (cd.1,c • cd.2) f (c • g)
          hf (hg.const_smul c) hpf (fun x => congrArg (fun y : ℂ => c*y) (hpg x)) ha hcb,
        weakSobolevRiccatiDensity_eq_classical_coefficients s (c • cd.1,cd.2) (c • f) g
          (hf.const_smul c) hg (fun x => congrArg (fun y : ℂ => c*y) (hpf x)) hpg hca hb,
        nlsRiccatiDensity_field_rescaling,periodOneCoefficient_smul_aux])
  exact congrFun he ab

/-- Rescaling holds in the actual lower Sobolev space for every available Riccati density. -/
theorem sobolevRiccatiDensity_field_rescaling (s n : ℕ) (hn : n ≤ s) (ab : SobolevSource s) (c : ℂ) :
    sobolevRiccatiDensity s (ab.1,c • ab.2) n hn =
      c • sobolevRiccatiDensity s (c • ab.1,ab.2) n hn := by
  have hd : Continuous (fun cd => sobolevRiccatiDensity s cd n hn) :=
    continuous_iff_continuousAt.mpr fun cd => (analyticAt_sobolevRiccatiDensity s n hn cd).continuousAt
  have he := eq_of_continuous_of_smooth_sobolevSource s
    (fun cd => sobolevRiccatiDensity s (cd.1,c • cd.2) n hn)
    (fun cd => c • sobolevRiccatiDensity s (c • cd.1,cd.2) n hn)
    (hd.comp (continuous_fst.prodMk (continuous_snd.const_smul c)))
    ((hd.comp ((continuous_fst.const_smul c).prodMk continuous_snd)).const_smul c) (by
      intro cd f g hf hg hpf hpg ha hb
      apply Subtype.ext
      funext j
      change (sobolevRiccatiDensity s (cd.1,c • cd.2) n hn).val j =
        c*(sobolevRiccatiDensity s (c • cd.1,cd.2) n hn).val j
      have hcb (k : ℤ) : (c • cd.2).val k = periodOneCoefficient (c • g) k := by
        simp only [WeightedCoeff.smul_val,periodOneCoefficient_smul_aux,hb]
      have hca (k : ℤ) : (c • cd.1).val k = periodOneCoefficient (c • f) k := by
        simp only [WeightedCoeff.smul_val,periodOneCoefficient_smul_aux,ha]
      rw [sobolevRiccatiDensity_eq_classical_coefficients s (cd.1,c • cd.2) f (c • g)
          hf (hg.const_smul c) hpf (fun x => congrArg (fun y : ℂ => c*y) (hpg x)) ha hcb n hn,
        sobolevRiccatiDensity_eq_classical_coefficients s (c • cd.1,cd.2) (c • f) g
          (hf.const_smul c) hg (fun x => congrArg (fun y : ℂ => c*y) (hpf x)) hpg hca hb n hn,
        nlsRiccatiDensity_field_rescaling,periodOneCoefficient_smul_aux])
  exact congrFun he ab

end NLS.ZakharovShabat
