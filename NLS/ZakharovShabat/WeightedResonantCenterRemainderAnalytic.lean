import NLS.ZakharovShabat.WeightedResonantCenterRemainderSmall
import NLS.ZakharovShabat.WeightedResonantDiagonalCenterAnalytic
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-!
# Banach analyticity of the actual center remainder

The actual moving-center coordinates are analytic. Their proved `ℓᵖ`
membership and uniform norm bound assemble them into a Banach analytic
pair map. For any tolerance, one open convex source neighborhood works
for every larger cutoff. The actual coefficients are retained on that
neighborhood; no model sequence or supplied norm premise replaces them.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The scalar remainder coordinates are analytic wherever the two
actual closing equations are analytic. The block below the cutoff is zero. -/
theorem analyticOnNhd_weightedResonantCenterRemainderCoordinate
    (hp : p ≠ ⊤) (w : SpectralWeight) (N : ℕ) (positive : Bool) (n : ℤ)
    (U : Set (WeightedCoeffPair w.toWeight p))
    (hplus : N ≤ n.natAbs → AnalyticOnNhd ℂ (fun ψ => weightedResonantBPlusExtension hp w ψ n
      (weightedResonantDiagonalCenter hp w ψ n)) U)
    (hminus : N ≤ n.natAbs → AnalyticOnNhd ℂ (fun ψ => weightedResonantBMinusExtension hp w ψ n
      (weightedResonantDiagonalCenter hp w ψ n)) U) :
    AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterRemainderCoordinate hp w ψ N positive n) U := by
  intro φ hφ
  by_cases hn : N ≤ n.natAbs
  · cases positive
    · have hproj : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => ψ.fst) φ :=
        analyticAt_fst.comp ((WeightedCoeffPair.toMax w.toWeight p).analyticAt φ)
      have hraw : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.fst) φ :=
        (w.toCoeff.analyticAt φ.fst).comp hproj
      have hlead : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => ψ.fst.val (-(2*n))) φ := by
        have he := ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) p (-(2*n))).analyticAt (w.toCoeff φ.fst)).comp
          (f := fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.fst) hraw
        change AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.fst (-(2*n))) φ at he
        simpa only [SpectralWeight.toCoeff_apply] using he
      simp only [weightedResonantCenterRemainderCoordinate,if_pos hn,Bool.false_eq_true,if_false]
      exact analyticAt_const.mul ((hminus hn φ hφ).sub hlead)
    · have hproj : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => ψ.snd) φ :=
        analyticAt_snd.comp ((WeightedCoeffPair.toMax w.toWeight p).analyticAt φ)
      have hraw : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.snd) φ :=
        (w.toCoeff.analyticAt φ.snd).comp hproj
      have hlead : AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => ψ.snd.val (2*n)) φ := by
        have he := ((lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) p (2*n)).analyticAt (w.toCoeff φ.snd)).comp
          (f := fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.snd) hraw
        change AnalyticAt ℂ (fun ψ : WeightedCoeffPair w.toWeight p => w.toCoeff ψ.snd (2*n)) φ at he
        simpa only [SpectralWeight.toCoeff_apply] using he
      simp only [weightedResonantCenterRemainderCoordinate,if_pos hn,if_true]
      exact analyticAt_const.mul ((hplus hn φ hφ).sub hlead)
  · simpa only [weightedResonantCenterRemainderCoordinate,if_neg hn] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : WeightedCoeffPair w.toWeight p => (0 : ℂ)) φ)

/-- One open convex neighborhood supports the genuine Banach analytic
remainder maps for all sufficiently large cutoffs, with an arbitrary
joint norm tolerance and exact actual coefficients throughout. -/
theorem exists_uniform_analytic_weightedResonantCenterRemainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterRemainder hp w ψ N) U ∧
        ∀ ψ ∈ U,
          (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ N positive) p) ∧
          ‖weightedResonantCenterRemainder hp w ψ N‖ < ε := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,_,h₁⟩ :=
    exists_uniform_weightedResonantCenterRemainder_small hp hp1 w φ ε hε
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ :=
    exists_uniform_analytic_weightedResonantCenterEquations hp hp1 w φ
  let U := U₁ ∩ U₂
  have ho : IsOpen U := ho₁.inter ho₂
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U,ho,hc₁.inter hc₂,⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro N hN
  have hdata (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ U) := h₁ ψ hψ.1 N (by omega)
  have hcoord (positive : Bool) (n : ℤ) :
      AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterRemainderCoordinate hp w ψ N positive n) U :=
    analyticOnNhd_weightedResonantCenterRemainderCoordinate hp w N positive n U
      (fun hn ψ hψ => (h₂ n (by omega)).2.1 ψ hψ.2)
      (fun hn ψ hψ => (h₂ n (by omega)).2.2 ψ hψ.2)
  have hfst : AnalyticOnNhd ℂ (fun ψ : WeightedCoeffPair w.toWeight p =>
      (weightedResonantCenterRemainder hp w ψ N).fst) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ ho ?_ ε ?_
    · intro n ψ hψ
      apply (hcoord false n ψ hψ).congr
      filter_upwards [ho.mem_nhds hψ] with χ hχ
      exact (weightedResonantCenterRemainder_apply_of_mem hp w χ N (hdata χ hχ).1 n).1.symm
    · intro ψ hψ
      exact (WithLp.norm_fst_le _ (weightedResonantCenterRemainder hp w ψ N)).trans (hdata ψ hψ).2.le
  have hsnd : AnalyticOnNhd ℂ (fun ψ : WeightedCoeffPair w.toWeight p =>
      (weightedResonantCenterRemainder hp w ψ N).snd) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ ho ?_ ε ?_
    · intro n ψ hψ
      apply (hcoord true n ψ hψ).congr
      filter_upwards [ho.mem_nhds hψ] with χ hχ
      exact (weightedResonantCenterRemainder_apply_of_mem hp w χ N (hdata χ hχ).1 n).2.symm
    · intro ψ hψ
      exact (WithLp.norm_snd_le _ (weightedResonantCenterRemainder hp w ψ N)).trans (hdata ψ hψ).2.le
  refine ⟨?_,hdata⟩
  intro ψ hψ
  have hpairs := (hfst ψ hψ).prod (hsnd ψ hψ)
  exact ((CoeffPair.toMax p).symm.analyticAt _).comp hpairs

end NLS.ZakharovShabat
