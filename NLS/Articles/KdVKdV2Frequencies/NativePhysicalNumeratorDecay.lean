import NLS.Articles.KdVKdV2Frequencies.NativeNormalizedNumerators
import NLS.KdV.HillMiuraPhysicalProductDecay
import NLS.KdV.HillAbelianCoordinateContinuity

/-! # Physical product decay for the actual common native numerator family -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The actual common-ball Hilbert-valued normalized numerator family also
satisfies the exterior product-decay condition at every physical L2 source
in that ball. The whole energy circle is controlled; its cutoff may depend
on the source, output index, comparison product and tolerance. -/
theorem exists_hillHminus_native_numerators_with_physical_product_decay :
    ∃ C : HillHminusMiuraChart, ∃ δ : ℝ, ∃ W₀ W : Set (CoeffPair 2),
      ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ F : ℂ × PeriodOneHminusOne → Coeff 2,
        0 < δ ∧ ball (0 : PeriodOneHminusOne) δ ⊆ C.domain ∧
        SourceTheorem12_1Data (by simp) (by norm_num) W₀ W s ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, C.criticalSource q ∈ W) ∧
        AnalyticOnNhd ℂ F (univ ×ˢ ball (0 : PeriodOneHminusOne) δ) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) δ, ∀ n : ℕ+, ∀ E : ℂ,
          F (E,q) (n : ℤ) = hillHminusMiuraEnergyPsi C s (n : ℤ) (E,q)) ∧
        (∀ n : ℕ+, ∀ E : ℂ, F (E,0) (n : ℤ) = classicalHillFreePsi n E) ∧
        (∀ t ∈ univ ×ˢ ball (0 : PeriodOneHminusOne) δ, ∀ m : ℤ, m ≤ 0 → F t m = 0) ∧
        (∀ k : ℕ+, ∀ q ∈ ball (0 : PeriodOneHminusOne) δ,
          CircleIntegrable (fun z : ℂ => ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2,q))
            ((Real.pi : ℂ)*(k : ℕ)) (Real.pi/4) ∧
          (2*(Real.pi : ℂ))⁻¹ • (∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            ((2*z)/hillHminusContinuedRoot (z^2,q)) • F (z^2,q)) = lp.single 2 (k : ℤ) 1) ∧
        ∀ p : RealHillWeightedPotential SpectralWeight.one,
          periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff p.val) ∈
            ball (0 : PeriodOneHminusOne) δ → ∀ n : ℕ+,
          ∀ roots ∈ hillGapRootBox (hillRealWeightedEmbedding SpectralWeight.one p).val
            (hillRealWeightedEmbedding SpectralWeight.one p).property.1
            (hillRealWeightedEmbedding SpectralWeight.one p).property.2,
          ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
            ∀ E ∈ sphere (0 : ℂ) ((centralCircleRadius k)^2),
              ‖F (E,periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff p.val)) (n : ℤ)/
                hillAbelianNumeratorProduct roots 0 E‖ ≤ ε := by
  obtain ⟨C,δ,W₀,W,s,F,hδ,hδC,H,hW,hFa,hmatch,hfree,hzero,hperiod,_⟩ :=
    exists_hillHminus_actual_native_normalized_numerators
  refine ⟨C,δ,W₀,W,s,F,hδ,hδC,H,hW,hFa,hmatch,hfree,hzero,hperiod,?_⟩
  intro p hp n roots hroots ε hε
  let q := hillRealWeightedEmbedding SpectralWeight.one p
  let u := SpectralWeight.one.doubleIndex.toCoeff p.val
  have hcoeff : SpectralWeight.one.toCoeff q.val = Coeff.periodDouble u := by
    dsimp only [q,hillRealWeightedEmbedding,u]
    rw [toCoeff_hillPeriodOneUnitPotential,toCoeff_hillPeriodOnePotential]
  filter_upwards [eventually_hillHminusMiuraEnergyPsi_div_physical_gap_product_le q.val
    q.property.1 q.property.2 C s (n : ℤ) u hcoeff (hδC hp) roots hroots ε hε] with k hk
  intro E hE
  rw [hmatch _ hp n E]
  exact hk E hE

end NLS.Articles.KdVKdV2Frequencies
