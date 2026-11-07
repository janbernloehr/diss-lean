import NLS.KdV.MiuraHillPsiNumerators

/-! The exact free zero-energy normalization of the descended numerator.
The original normalized Dirac family gives 2/(pi*n), including the filled
energy zero; no nonzero-frequency restriction is used in that conclusion. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

/-- The original free Dirac psi function has derivative 2/(pi*n) at zero. -/
theorem deriv_sourcePsiFree_zero_of_ne (n : ℤ) (hn : n ≠ 0) :
    deriv (sourcePsiFree n) 0 = 2/((Real.pi:ℂ)*n) := by
  have ha : (Real.pi:ℂ)*n ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hn)
  have h0 : (0:ℂ) ≠ (Real.pi:ℂ)*n := Ne.symm ha
  have hd := ((Complex.hasDerivAt_sin (0:ℂ)).const_mul (-2)).fun_div
    ((hasDerivAt_id (0:ℂ)).sub_const ((Real.pi:ℂ)*n))
      (by simpa only [id_eq,zero_sub] using neg_ne_zero.mpr ha)
  simp only [id_eq] at hd
  have he : sourcePsiFree n =ᶠ[𝓝 (0:ℂ)] fun z => -2*sin z/(z-(Real.pi:ℂ)*n) := by
    filter_upwards [eventually_ne_nhds h0] with z hz
    rw [sourcePsiFree,freeSineQuotient_eq_div n z hz]
    ring
  rw [he.deriv_eq,hd.deriv]
  simp only [Complex.sin_zero,Complex.cos_zero,mul_one,mul_zero,zero_sub,sub_zero]
  field_simp

theorem MiuraHillPsiFamily.roots_zero (B : MiuraHillPsiFamily) (n : ℤ) : B.roots n 0 = 0 := by
  have h := B.verified.real_agreement n
    (⟨0,by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus 2)
  rw [sourcePsiGapRoot_zero] at h
  exact h

/-- All choices of verified simultaneous families have the same literal free numerator. -/
theorem MiuraHillPsiFamily.selected_free (B : MiuraHillPsiFamily) (n : ℤ) (z : ℂ) :
    sourceSelectedPsiNumerator B.roots n (z,0) = sourcePsiFree n z := by
  change sourcePsiCandidate n (z,(B.roots n 0:Coeff 2)) = _
  rw [B.roots_zero]
  exact sourcePsiCandidate_zero (by norm_num) (by norm_num) n z

/-- Exact Hill free normalization at the removable zero-energy point. -/
theorem MiuraHillPsiFamily.numerator_free_zero (B : MiuraHillPsiFamily) (n : ℕ+) :
    B.numerator n (0,0) = 2/((Real.pi:ℂ)*(n:ℕ)) := by
  have hf : AnalyticAt ℂ (fun z : ℂ => sourceSelectedPsiNumerator B.roots ((n:ℕ):ℤ) (z,0)) 0 := by
    have he : (fun z : ℂ => sourceSelectedPsiNumerator B.roots ((n:ℕ):ℤ) (z,0)) =
        sourcePsiFree ((n:ℕ):ℤ) := funext (B.selected_free ((n:ℕ):ℤ))
    rw [he]
    exact (differentiable_sourcePsiFree ((n:ℕ):ℤ)).analyticAt 0
  change oddSquareDescent (sourceSelectedPsiNumerator B.roots ((n:ℕ):ℤ)) (0,hillMiuraDiagonal 0) = _
  rw [map_zero,oddSquareDescent_zero _ _ hf]
  have he : (fun z : ℂ => sourceSelectedPsiNumerator B.roots ((n:ℕ):ℤ) (z,0)) =
      sourcePsiFree ((n:ℕ):ℤ) := funext (B.selected_free ((n:ℕ):ℤ))
  rw [he,deriv_sourcePsiFree_zero_of_ne _ (by exact_mod_cast n.ne_zero)]
  simp only [Int.cast_natCast]

end NLS.KdV
