import NLS.KdV.HillFreeCartesianDifference
import NLS.KdV.HillOriginalAllGapCartesianMatrix
import NLS.Poisson.GardnerFourierModes

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The FULL original Gardner matrix and the proved antisymmetric Fourier
differential determine every original Cartesian cosine-mode derivative.
All positive indices and all free collapsed gaps are included. -/
theorem hillOriginalCartesian_free_cosine_fderiv (n m : ℕ+)
    (Z W G : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z 0) (hW : AnalyticAt ℂ W 0) (hG : AnalyticAt ℂ G 0)
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hWM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      W (hillOriginalHminusSource p.val) = conj (hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos))
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential),
      G (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos) :
    (fderiv ℂ G 0) (NLS.Poisson.hminusCosineMode n) =
      if (n : ℕ) = (m : ℕ) then hillActionGapPrefactor 0 h0q h0r n else 0 := by
  let Q : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  let P := hillActionGapPrefactor 0 h0q h0r n
  let c : ℂ := (2*Real.pi : ℂ)*I*(n : ℂ)*P
  let K : PeriodOneHminusOne →L[ℂ] ℂ := fderiv ℂ Z 0-fderiv ℂ W 0
  have hK (h : PeriodOneHminusOne) : K h = P*(h.val n-h.val (-(n : ℤ))) :=
    hillOriginalCartesian_free_difference_fderiv h0q h0r n Z W hZ hW hZM hWM h
  have hZZ := hillSignedCartesians_hminus_Gardner_original_matrix Q (by rfl) n m true true Z G
    (by simpa only [Q,map_zero] using hZ) (by simpa only [Q,map_zero] using hG)
    (by simpa only [hillSignedSpectralCartesian,ite_true] using hZM)
    (by simpa only [hillSignedSpectralCartesian,ite_true] using hGM)
  have hWZ := hillSignedCartesians_hminus_Gardner_original_matrix Q (by rfl) n m false true W G
    (by simpa only [Q,map_zero] using hW) (by simpa only [Q,map_zero] using hG)
    (by simpa [hillSignedSpectralCartesian,Q] using hWM)
    (by simpa only [hillSignedSpectralCartesian,ite_true] using hGM)
  have hZG : NLS.Poisson.gardnerCotangentBivector (fderiv ℂ Z 0) (fderiv ℂ G 0) = 0 := by
    change NLS.Poisson.hminusGardnerBracket Z G 0 = 0
    simpa only [Q,map_zero,hillOriginalComplexGardnerMatrixEntry,ite_true,zero_mul] using hZZ
  have hWG : NLS.Poisson.gardnerCotangentBivector (fderiv ℂ W 0) (fderiv ℂ G 0) =
      -(2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := by
    change NLS.Poisson.hminusGardnerBracket W G 0 = _
    simpa [Q,hillOriginalComplexGardnerMatrixEntry] using hWZ
  have hPair : NLS.Poisson.gardnerCotangentBivector K (fderiv ℂ G 0) =
      (2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := by
    change NLS.Poisson.gardnerCotangentBivector (fderiv ℂ Z 0-fderiv ℂ W 0) (fderiv ℂ G 0) = _
    rw [map_sub,sub_apply,hZG,hWG]
    ring
  have hEval : c*(fderiv ℂ G 0) (NLS.Poisson.hminusCosineMode n) =
      (2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := by
    have hh := (NLS.Poisson.gardnerCotangentBivector_antisymmetric_fourier (n : ℤ) P K (fderiv ℂ G 0) hK).symm.trans hPair
    simpa only [Int.cast_natCast] using hh
  have hp : 0 < (n : ℝ)*Real.pi := mul_pos (by exact_mod_cast n.pos) Real.pi_pos
  have hs : (Real.sqrt ((n : ℝ)*Real.pi) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hp).ne'
  have hsq : (Real.sqrt ((n : ℝ)*Real.pi) : ℂ)^2 = (n : ℂ)*Real.pi := by
    exact_mod_cast Real.sq_sqrt hp.le
  have hPne : P ≠ 0 := by
    rw [show P = hillActionGapPrefactor 0 h0q h0r n from rfl,hillActionGapPrefactor_free_value h0q h0r n n.pos]
    exact inv_ne_zero hs
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt n.pos)
  have hcne : c ≠ 0 := by
    dsimp only [c]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero) hn0) hPne
  have hcoef : c*P = 2*I := by
    dsimp only [c,P]
    rw [hillActionGapPrefactor_free_value h0q h0r n n.pos]
    field_simp [hs]
    rw [hsq]
    ring
  have hcandidate : c*(if (n : ℕ) = (m : ℕ) then P else 0) =
      (2*I)*(if (n : ℕ) = (m : ℕ) then 1 else 0) := by
    split_ifs <;> simp only [mul_zero,mul_one,hcoef]
  exact mul_left_cancel₀ hcne (hEval.trans hcandidate.symm)

end NLS.KdV
