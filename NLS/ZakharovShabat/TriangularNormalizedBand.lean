import NLS.ZakharovShabat.TriangularDyadicKernel

/-! # Normalized finite bands with an exact Dirichlet eigenvalue -/
noncomputable section
open Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Positive Fourier indices between 2^P and 2^(2P). -/
def triangularDyadicBand (P : ℕ) : Finset ℤ :=
  (Finset.Ico (2^P) (2^P*2^P)).image (Nat.cast : ℕ → ℤ)

/-- The positive mass that normalizes the triangular boundary equation. -/
def triangularDyadicMass (P : ℕ) : ℝ :=
  ∑ n ∈ triangularDyadicBand P, triangularBoundaryKernel (2^P) n

/-- Opposite constant coefficients on the band and its reflection. -/
def triangularNormalizedCoefficients (P : ℕ) : ℤ →₀ ℂ :=
  oddFourierCoefficients (triangularDyadicBand P) (1/triangularDyadicMass P)

theorem triangularDyadicBand_pos (P : ℕ) {n : ℤ} (hn : n ∈ triangularDyadicBand P) :
    0 < n := by
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
  exact_mod_cast (show 0 < m from (by positivity : 0 < 2^P).trans_le (Finset.mem_Ico.mp hm).1)

theorem triangularDyadicMass_lower (P : ℕ) : (P : ℝ)/12 ≤ triangularDyadicMass P := by
  have h := triangularBoundaryKernel_dyadic_band P (H := 2^P) (by positivity)
  unfold triangularDyadicMass triangularDyadicBand
  rw [Finset.sum_image (by intro a _ b _ h; exact Nat.cast_injective h)]
  simpa only [Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat] using h

theorem triangularDyadicMass_pos {P : ℕ} (hP : 0 < P) : 0 < triangularDyadicMass P :=
  (by positivity : 0 < (P : ℝ)/12).trans_le (triangularDyadicMass_lower P)

/-- The number of signed coefficients grows at most as 8^P. -/
theorem triangularDyadicBand_card {P : ℕ} (hP : 0 < P) :
    2*(triangularDyadicBand P).card ≤ 8^P := by
  have hc : (triangularDyadicBand P).card ≤ 2^P*2^P := by
    exact (Finset.card_image_le).trans (by rw [Nat.card_Ico]; exact Nat.sub_le _ _)
  calc
    _ ≤ 2*(2^P*2^P) := Nat.mul_le_mul_left 2 hc
    _ ≤ 2^P*(2^P*2^P) := Nat.mul_le_mul_right _
      (by simpa using Nat.pow_le_pow_right (n := 2) (by norm_num) hP)
    _ = 8^P := by rw [← mul_pow,← mul_pow]; norm_num

/-- Normalization solves the exact finite Fourier equation. -/
theorem triangularBoundarySum_normalized {P : ℕ} (hP : 0 < P) :
    triangularBoundarySum (triangularNormalizedCoefficients P) (2^P) = 2*I := by
  rw [triangularNormalizedCoefficients,triangularBoundarySum_oddFourierCoefficients
    _ (fun _ hn => triangularDyadicBand_pos P hn) _ (by positivity)]
  change 2*I*((1/triangularDyadicMass P : ℝ) : ℂ)*(triangularDyadicMass P : ℂ) = _
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (triangularDyadicMass_pos hP).ne']

/-- The exact source norm is at most 96/P. No estimate for an interval extension is used. -/
theorem norm_triangularNormalizedCoefficients_source_le {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 0 < P) :
    ‖CoeffPair.ofFinsupp (p := (P : ℝ≥0∞)) (triangularNormalizedCoefficients P,0)‖ ≤
      96/(P : ℝ) := by
  have hmass := triangularDyadicMass_pos hP
  have hnorm := norm_oddFourierCoefficients_source_le (ENNReal.natCast_ne_top P)
    (triangularDyadicBand P) (c := 1/triangularDyadicMass P) (B := 8)
    (by positivity) (by norm_num) (by
      rw [ENNReal.toReal_natCast,Real.rpow_natCast]
      exact_mod_cast triangularDyadicBand_card hP)
  apply hnorm.trans
  have hPr : 0 < (P : ℝ) := by exact_mod_cast hP
  have hl := triangularDyadicMass_lower P
  rw [mul_one_div]
  apply (div_le_div_iff₀ hmass hPr).mpr
  nlinarith

/-- The normalized finite polynomial has an actual source Dirichlet eigenvalue at i*2^P. -/
theorem mem_sourceDirichletSpectrum_triangularNormalized {P : ℕ}
    [Fact (1 ≤ (P : ℝ≥0∞))] (hP : 1 < (P : ℝ≥0∞)) :
    ((2 : ℂ)^P)*I ∈ BoundaryCondition.spectrum .dirichlet (ENNReal.natCast_ne_top P)
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP
        (CoeffPair.ofFinsupp (triangularNormalizedCoefficients P,0))).val
      (periodOneBoundaryPotential (ENNReal.natCast_ne_top P) hP
        (CoeffPair.ofFinsupp (triangularNormalizedCoefficients P,0))).property := by
  have hP0 : 0 < P := by exact_mod_cast (zero_lt_one.trans hP)
  simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using
    mem_sourceDirichletSpectrum_of_triangularBoundarySum (ENNReal.natCast_ne_top P) hP
      (triangularNormalizedCoefficients P) (by positivity) (triangularBoundarySum_normalized hP0)

end NLS.ZakharovShabat
