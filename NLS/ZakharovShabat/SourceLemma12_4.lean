import NLS.ZakharovShabat.SourcePsiOriginalEquationAnalytic
import NLS.ZakharovShabat.SourceTheorem12_1

/-!
# Lemma 12.4 on the unchanged original source domain

The literal contour equation is an actual deleted lp-valued analytic map
for every root input and every source in W. Its norm and printed power
sum are locally bounded uniformly in the deleted index. All preceding
Section 11 data are retained on exactly the same W.
-/

noncomputable section
open Set Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceSection11OriginalEstimates.quotients
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11OriginalEstimates hp hp1 W) : SourceCorollary10_6Data hp hp1 W := by
  have h11 := H.previous.previous.previous
  exact h11.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous

structure SourceLemma12_4Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceSection11OriginalEstimates hp hp1 W
  equation : ∀ ψ ∈ W, ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ m : ℤ,
    ∀ D : SourceCriticalRootPeriodCircle hp hp1 ψ m,
      (sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (D.center:ℂ) D.radius
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ
    (fun t : CoeffPair p × DeletedCoeff p n => sourcePsiOriginalEquation hp hp1 n t.2 t.1) (W ×ˢ univ)
  real_analytic : ∀ n : ℤ, AnalyticOnNhd ℝ
    (fun t : CoeffPair p × DeletedCoeff p n => sourcePsiOriginalEquation hp hp1 n t.2 t.1) (W ×ˢ univ)
  real : ∀ ψ ∈ W, IsRealType (CoeffPair.toMax p ψ) → ∀ n : ℤ, ∀ a : DeletedCoeff p n,
    (∀ k : ℤ, ((a:Coeff p) k).im = 0) → ∀ m : ℤ, ((sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m).im = 0
  locally_uniform : ∀ φ ∈ W, ∀ a₀ : Coeff p,
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
        ((a:Coeff p),ψ) ∈ U → ‖sourcePsiOriginalEquation hp hp1 n a ψ‖ ≤ C
  power_sum : ∀ φ ∈ W, ∀ a₀ : Coeff p,
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
        ((a:Coeff p),ψ) ∈ U →
          (∑' m : ℤ, ‖(sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m‖^p.toReal) < C

/-- Lemma 12.4 retains the entire existing original domain, with no shrink. -/
theorem SourceSection11OriginalEstimates.lemma12_4
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11OriginalEstimates hp hp1 W) (hW : IsOpen W) : SourceLemma12_4Data hp hp1 W := by
  have ha := H.quotients.originalEquation_analytic_sourceFirst hW H.psiIntegrand_joint
  exact ⟨H,H.quotients.originalEquation_apply hW,ha,
    (fun n t ht => (ha n t ht).restrictScalars (𝕜 := ℝ)),
    H.quotients.originalEquation_real hW,H.quotients.originalEquation_uniformNorm hW,
    H.quotients.originalEquation_uniformPowerSum hW⟩

/-- The same equation is computed by every original circuit with its actual winding. -/
theorem SourceLemma12_4Data.circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (a : DeletedCoeff p n)
    (m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (Metric.ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourceGapFunctional hp hp1 n m ψ Γ (fun z => sourcePsiCandidate n (z,(a:Coeff p))) =
      (sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m*
        Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) :=
  H.previous.quotients.originalEquation_circuit hW ψ hψ n a m D Γ hΓ

theorem sourceLemma12_4 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma12_4Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceSection11OriginalEstimates hp hp1
  exact ⟨W,ho,hc,hr,H.lemma12_4 ho⟩

/-- The simultaneous family already constructed in Theorem 12.1 solves
the actual lp-valued equation on its common domain. -/
theorem SourceTheorem12_1Data.originalEquation_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceTheorem12_1Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourcePsiOriginalEquation hp hp1 n (s n ψ) ψ = 0 := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.previous.quotients.neighborhoods ψ (H.subset hψ)
  apply Subtype.ext
  ext m
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV m d r hr he
  rw [H.previous.quotients.originalEquation_apply hW₀ ψ (H.subset hψ) n (s n ψ) m P]
  simp only [sourcePsiEquationCoordinate,H.period ψ hψ n m P]
  by_cases hmn : m = n
  · subst m; simp
  · simp [hmn]

end NLS.ZakharovShabat
