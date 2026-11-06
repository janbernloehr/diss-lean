import NLS.SequenceSpaces.LocalScalarActionFamilyDescent
import NLS.SequenceSpaces.NonzeroFiniteCenter

/-! # Common analytic action charts from real action invariance

Real fiber invariance supplies all complex tail sign symmetries and
infinitesimal rotations. One finite center and one action chart work for
the entire scalar family, including every zero tail coordinate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- A real-invariant family descends on one common open action image near
every real coordinate pair. No complex invariance hypothesis is assumed. -/
theorem exists_real_scalar_action_family_chart {ι : Type*} (hp : p ≠ ⊤)
    (f : ι → (Coeff p × Coeff p) → ℂ) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hinv : ∀ i, ∀ z ∈ U, ∀ w ∈ U,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      quadraticActionsExponent (q := q) w = quadraticActionsExponent z → f i w = f i z)
    (z₀ : Coeff p × Coeff p) (hz₀ : z₀ ∈ U) (hzreal : z₀ ∈ realPairLocus p) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ U ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧
      ∀ i, ∀ z ∈ Z, g i (quadraticActionsExponent z) = f i z := by
  obtain ⟨S,R,hR,hbase,hball,hhead⟩ := exists_nonzeroFiniteCenter_ball hp U hU z₀ hz₀
  let c := truncatePair S z₀
  have hcr : c ∈ realPairLocus p := truncatePair_mem_realPairLocus S z₀ hzreal
  have hrealinv (i : ι) : ∀ z ∈ ball c R, ∀ w ∈ ball c R,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2 = z.1 n^2+z.2 n^2) → f i w = f i z := by
    intro z hz w hw hzr hwr he
    apply hinv i z (hball hz) w (hball hw) hzr hwr
    ext n
    simp only [quadraticActionsExponent_apply,he n]
  have hsign : ∀ i, ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ ball c R, f i (pairSignChange e d z) = f i z := by
    intro i e d he hd z hz
    exact eqOn_pairSignChange_of_real_action_invariance (f i) c R hR hcr
      ((hf i).mono hball) (hrealinv i) e d (pairSignChange_truncatePair S z₀ e d he hd) hz
  have hrot : ∀ i, ∀ z ∈ ball c R, ∀ k,
      fderiv ℂ (f i) z (actionRotationVectorCLM p k z) = 0 := by
    intro i z hz k
    exact fderiv_actionRotationVector_eq_zero_of_real_action_invariance (f i)
      (ball c R) isOpen_ball (convex_ball c R) c (mem_ball_self hR) hcr
      ((hf i).mono hball) (hrealinv i) z hz k
  obtain ⟨Z,T,g,hZ,hbaseZ,hZball,hT,himage,hg,hrec⟩ :=
    exists_local_scalar_action_factors (q := q) hp S f (ball c R) isOpen_ball
      (fun i => (hf i).mono hball) hsign hrot z₀ hbase hhead
  exact ⟨Z,T,g,hZ,hbaseZ,hZball.trans hball,hT,himage,hg,hrec⟩

/-- The same chart transfers every bound depending only on the actions. -/
theorem exists_real_scalar_action_family_chart_with_bounds {ι : Type*} (hp : p ≠ ⊤)
    (f : ι → (Coeff p × Coeff p) → ℂ) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hinv : ∀ i, ∀ z ∈ U, ∀ w ∈ U,
      z ∈ realPairLocus p → w ∈ realPairLocus p →
      quadraticActionsExponent (q := q) w = quadraticActionsExponent z → f i w = f i z)
    (z₀ : Coeff p × Coeff p) (hz₀ : z₀ ∈ U) (hzreal : z₀ ∈ realPairLocus p)
    (B : ι → Coeff q → ℝ)
    (hbound : ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ B i (quadraticActionsExponent z)) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ U ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧
      (∀ i, ∀ z ∈ Z, g i (quadraticActionsExponent z) = f i z) ∧
      ∀ i, ∀ b ∈ T, ‖g i b‖ ≤ B i b := by
  obtain ⟨Z,T,g,hZ,hbaseZ,hZU,hT,himage,hg,hrec⟩ :=
    exists_real_scalar_action_family_chart (q := q) hp f U hU hf hinv z₀ hz₀ hzreal
  refine ⟨Z,T,g,hZ,hbaseZ,hZU,hT,himage,hg,hrec,?_⟩
  intro i b hb
  obtain ⟨z,hz,rfl⟩ := himage.symm ▸ hb
  rw [hrec i z hz]
  exact hbound i z (hZU hz)

end NLS.Coeff
