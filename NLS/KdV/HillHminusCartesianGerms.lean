import NLS.KdV.HillHminusRelativeAmplitude
import NLS.KdV.HillPhaseLocalSign

/-! Actual original Cartesian coordinate germs on an isospectral set.
Both the action amplitude and the complete physical phase are retained.
No global canonical-map or inverse assertion is made here. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- A common H-minus-one analytic Cartesian germ equals the COMPLETE
ORIGINAL Cartesian coordinate on an L2 neighborhood of EVERY original
isospectral point in an actual H-minus-one ball. This is stronger than
matching only at those points and retains the derivatives needed for
strong H-minus-one endpoint transport. -/
theorem exists_hillOriginal_cartesian_hminus_isospectral_physical_germs
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ Z (ball (hillOriginalHminusSource q.val) ε) ∧
      ∀ p : RealPeriodOneHillPotential,
        hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ε →
        (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
          hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) →
        ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ p ∈ V ∧
          ∀ r ∈ V, Z (hillOriginalHminusSource r.val) =
            hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos := by
  obtain ⟨U,hU,hqU,hA,hmatchA⟩ :=
    exists_hillHminusRelativeAmplitude_isospectral_physical_germs q n n.pos hgap
  obtain ⟨δ,hδ,F,hF,hmatchF⟩ :=
    HillHminusPsiChart.exists_hillOriginal_fullPhaseFactor_hminus_analytic_open q n hgap
  let W := U ∩ ball (hillOriginalHminusSource q.val) δ
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp (hU.inter isOpen_ball)
    (hillOriginalHminusSource q.val) (show hillOriginalHminusSource q.val ∈ W from ⟨hqU,mem_ball_self hδ⟩)
  let Z : PeriodOneHminusOne → ℂ := fun a => hillHminusRelativeAmplitude q n a * F a
  refine ⟨ε,hε,Z,?_,?_⟩
  · intro a ha
    exact (hA a (hball ha).1).mul (hF a (hball ha).2)
  · intro p hp hΔ
    obtain ⟨V,hV,hpV,hmatchA⟩ := hmatchA p hΔ
    let T : Set RealPeriodOneHillPotential :=
      (fun r : RealPeriodOneHillPotential => hillOriginalHminusSource r.val) ⁻¹'
        ball (hillOriginalHminusSource q.val) δ
    have hT : IsOpen T := isOpen_ball.preimage
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val)
    refine ⟨V ∩ T,hV.inter hT,⟨hpV,(hball hp).2⟩,?_⟩
    intro r hr
    change hillHminusRelativeAmplitude q n (hillOriginalHminusSource r.val) *
      F (hillOriginalHminusSource r.val) = _
    rw [hmatchA r hr.1,hmatchF r hr.2]
    simp only [hillSpectralCartesian,hillOriginalFullPhaseFactor,mul_assoc]

/-- The common ORIGINAL Cartesian germs have strongly continuous H-minus-one
Fréchet derivatives. The physical matching is on real L2 neighborhoods,
not only on the isospectral sequence itself. -/
theorem exists_hillOriginal_cartesian_hminus_strong_derivative_germs
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ Z : PeriodOneHminusOne → ℂ,
      AnalyticOnNhd ℂ Z (ball (hillOriginalHminusSource q.val) ε) ∧
      (∀ a : ℕ → PeriodOneHminusOne,
        Tendsto a atTop (𝓝 (hillOriginalHminusSource q.val)) →
        Tendsto (fun j => fderiv ℂ Z (a j)) atTop
          (𝓝 (fderiv ℂ Z (hillOriginalHminusSource q.val)))) ∧
      ∀ p : RealPeriodOneHillPotential,
        hillOriginalHminusSource p.val ∈ ball (hillOriginalHminusSource q.val) ε →
        (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
          hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) →
        ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ p ∈ V ∧
          ∀ r ∈ V, Z (hillOriginalHminusSource r.val) =
            hillSpectralCartesian r.val r.property.1 r.property.2 n n.pos := by
  obtain ⟨ε,hε,Z,hZ,hmatch⟩ :=
    exists_hillOriginal_cartesian_hminus_isospectral_physical_germs q n hgap
  refine ⟨ε,hε,Z,hZ,?_,hmatch⟩
  intro a ha
  exact (hZ.fderiv _ (mem_ball_self hε)).continuousAt.tendsto.comp ha

end NLS.KdV
