import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianCanonical
import NLS.SequenceSpaces.HminusMeanZeroProjection

/-! # One common complex neighborhood with the full actual canonical matrix

The neighborhood is chosen before all signed coordinate indices. It
contains every real mean-zero rough source, including non-L2 sources.
The bracket is the literal ambient HminusOne Gardner bracket of the SAME
global signed map, with the original Abelian normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

def canonicalDomain (D : GlobalRoughAbelianForwardData) : Set PeriodOneHminusOne :=
  ⋃ q0 : {q : PeriodOneRealHminusOne // q.val.val 0 = 0},
    ball q0.val.val (D.chart q0.val).data.radius

theorem canonicalDomain_open (D : GlobalRoughAbelianForwardData) : IsOpen D.canonicalDomain :=
  isOpen_iUnion (fun _ => isOpen_ball)

theorem canonicalDomain_subset_domain (D : GlobalRoughAbelianForwardData) :
    D.canonicalDomain ⊆ D.domain := by
  intro q hq
  obtain ⟨q0,hq0⟩ := mem_iUnion.mp hq
  exact D.chart_subset_domain q0.val hq0

theorem real_meanZero_mem_canonicalDomain (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0) :
    q ∈ D.canonicalDomain :=
  mem_iUnion.mpr ⟨⟨⟨q,hr⟩,hm⟩,mem_ball_self (D.chart ⟨q,hr⟩).data.radius_pos⟩

/-- The actual full Gardner matrix on ONE common complex neighborhood,
with only the literal mean-zero constraint and no reality assumption. -/
theorem gardner_matrix_complex_meanZero (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.canonicalDomain) (hm : q.val 0 = 0)
    (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent D.signed σ n)
      (hillRoughSignedAbelianComponent D.signed τ m) q =
        hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  obtain ⟨q0,hq0⟩ := mem_iUnion.mp hq
  let U := ball q0.val.val (D.chart q0.val).data.radius
  let Q := hminusMeanZeroProjection
  let B := NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent D.signed σ n)
    (hillRoughSignedAbelianComponent D.signed τ m)
  have hQ (u : PeriodOneHminusOne) (hu : u ∈ U) : Q u ∈ U :=
    hminusMeanZeroProjection_mem_ball q0.val.val u q0.property _ hu
  have hBa := NLS.Poisson.analyticOnNhd_hminusGardnerBracket _ _
    (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic σ n)
    (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic τ m)
  have ha : AnalyticOnNhd ℂ (fun u => B (Q u)) U := by
    intro u hu
    exact (hBa _ (D.chart_subset_domain q0.val (hQ u hu))).comp (Q.analyticAt u)
  have he := periodOneHminus_real_form_identity_at isOpen_ball isPreconnected_ball
    q0.val.val (mem_ball_self (D.chart q0.val).data.radius_pos) q0.val.property
    (fun u => B (Q u)) (fun _ => hillOriginalComplexGardnerMatrixEntry σ τ n m/2)
    ha analyticOnNhd_const (by
      intro u _ hr
      exact D.gardner_matrix_real_meanZero (Q u) (hminusMeanZeroProjection_real u hr)
        (hminusMeanZeroProjection_zero_mode u) σ τ n m)
  simpa only [Q,hminusMeanZeroProjection_eq_self q hm] using he hq0

theorem gardner_positive_negative (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.canonicalDomain) (hm : q.val 0 = 0)
    (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent D.signed true n)
      (hillRoughSignedAbelianComponent D.signed false m) q =
        if n = m then I else 0 := by
  rw [D.gardner_matrix_complex_meanZero q hq hm]
  by_cases h : n = m
  · subst m
    simp [hillOriginalComplexGardnerMatrixEntry]
  · have hnm : (n : ℕ) ≠ (m : ℕ) := fun he => h (Subtype.ext he)
    simp [hillOriginalComplexGardnerMatrixEntry,hnm,h]

theorem gardner_same_sign (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.canonicalDomain) (hm : q.val 0 = 0)
    (σ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent D.signed σ n)
      (hillRoughSignedAbelianComponent D.signed σ m) q = 0 := by
  rw [D.gardner_matrix_complex_meanZero q hq hm]
  cases σ <;> simp [hillOriginalComplexGardnerMatrixEntry]

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
