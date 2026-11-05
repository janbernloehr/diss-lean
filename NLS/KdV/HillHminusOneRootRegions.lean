import NLS.KdV.HillHminusOneExteriorRoots
import NLS.KdV.HillCentralRegionGeometry

/-! # Exhaustive central and high H^-1 root regions

A common complex neighborhood and cutoff control every actual root on
every straight source path. The high energy disc radius is prescribed
in advance. Every larger cutoff works with its exact free separator.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_hillHminus_source_root_regions (q : PeriodOneHminusOne)
    (r : ℝ) (hr : 0 < r) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ J : ℕ, N ≤ J → ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ,
        hillHminusRadicand ((s : ℂ) • a) z = 0 →
          -(J : ℝ)^2 < z.re ∧
            (z.re < hillCentralSeparator J ∨ ∃ n : ℕ+, J ≤ (n : ℕ) ∧
              z ∈ ball (freeHillValue (n : ℕ) : ℂ) (Real.pi*(n : ℕ)*r) ∧
                hillCentralSeparator J < z.re) := by
  let eta : ℝ := min (r/16) (min (1/(32*Real.pi)) (Real.pi/4))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hetapi : eta ≤ Real.pi/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hetar : eta ≤ r/16 := min_le_left _ _
  have hetasmall : eta ≤ 1/(32*Real.pi) := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨V,hV,hq,M,A,hM,hA,hroots⟩ :=
    exists_hillHminus_source_energy_root_confinement q eta heta hetapi
  have hpr : 0 < Real.pi*r := mul_pos Real.pi_pos hr
  have hdiv : 0 ≤ 4*A/(Real.pi*r) := by positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (2+8*A+M+A+2+4*A/(Real.pi*r))
  have hN2 : 2 ≤ N := by exact_mod_cast (show (2 : ℝ) ≤ N by linarith)
  refine ⟨N,V,hN2,hV,hq,?_⟩
  intro J hJ a ha s hs z hz
  have hJR : (N : ℝ) ≤ J := by exact_mod_cast hJ
  have hJA : 8*A ≤ (J : ℝ) := by linarith
  have hJM : M+A+2 ≤ (J : ℝ) := by linarith
  have hJAr : 4*A ≤ Real.pi*(J : ℝ)*r := by
    have hh : 4*A/(Real.pi*r) ≤ (J : ℝ) := by linarith
    have he := (div_le_iff₀ hpr).mp hh
    nlinarith
  have hb8 : 2*Real.pi*eta ≤ 1/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 32*Real.pi)).mp hetasmall
    linarith
  have hbr : 2*Real.pi*eta ≤ Real.pi*r/4 := by nlinarith [Real.pi_pos]
  apply energy_root_central_or_high_of_affine_bound M A (2*Real.pi*eta) r J hM hA
    (by positivity) hb8 hbr hr (hN2.trans hJ) hJA hJM hJAr z
  rcases hroots a ha s hs z hz with h | ⟨n,hn⟩
  · exact Or.inl h
  · exact Or.inr ⟨n,by nlinarith [hn]⟩

/-- The entire vertical separator and left real half-plane are zero-free
on the same source family. No unaccounted roots remain between high discs. -/
theorem exists_hillHminus_zero_free_source_separators (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ J : ℕ, N ≤ J → ∀ a ∈ V, ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℂ,
        z.re ≤ -(J : ℝ)^2 ∨ z.re = hillCentralSeparator J →
          hillHminusRadicand ((s : ℂ) • a) z ≠ 0 := by
  obtain ⟨N,V,hN,hV,hq,hregions⟩ := exists_hillHminus_source_root_regions q 1 (by norm_num)
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro J hJ a ha s hs z hz hzero
  obtain ⟨hlo,hregion⟩ := hregions J hJ a ha s hs z hzero
  rcases hz with hz | hz
  · linarith
  · rcases hregion with h | ⟨_,_,_,h⟩ <;> linarith

end NLS.KdV
