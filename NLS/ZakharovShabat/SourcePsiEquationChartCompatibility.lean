import NLS.ZakharovShabat.SourcePsiEquationContourHomotopy
import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.ZakharovShabat.SourcePsiGapRootGraphCompact

/-!
# Compatibility and limit closure of selected psi equations

The selected Banach-valued equation is represented by scalar contour
coordinates on each local chart. Common outer isolating circles make
those coordinates independent of the chart. Continuity of a fixed
chart then preserves the zero equation under strong root and source
limits, once the limit belongs to its open chart domain.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- Two selected contour families admit a coordinatewise comparison
through common outer circles at a fixed source potential. -/
def sourcePsiContourFamiliesComparable
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ) : Prop :=
  ∀ m : ℤ, ∃ c : ℂ, ∃ R : ℝ,
    0 < R₀ m ∧ 0 < R₁ m ∧ 0 < R ∧
    sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c₀ m) (R₀ m) ∧
    sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c₁ m) (R₁ m) ∧
    sourcePeriodicSegment hp hp1 ψ m ⊆ ball c R ∧
    closedBall (c₀ m) (R₀ m) ⊆ closedBall c R ∧
    closedBall (c₁ m) (R₁ m) ⊆ closedBall c R ∧
    closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ m

/-- At a point where both selected maps have their actual contour
coordinates, comparable contour families give the same deleted
Banach-space equation value. -/
theorem sourcePsiSelectedEquationSequence_eq_of_comparable_contours
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (c₀ c₁ : ℤ → ℂ) (R₀ R₁ : ℤ → ℝ)
    (hcoord₀ : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₀ m) (R₀ m))
    (hcoord₁ : ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₁ m) (R₁ m))
    (hcompare : sourcePsiContourFamiliesComparable
      hp hp1 ψ c₀ c₁ R₀ R₁) :
    sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a ψ =
      sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a ψ := by
  apply Subtype.ext
  ext m
  obtain ⟨c,R,hr₀,hr₁,hR,hseg₀,hseg₁,hseg,
    hnest₀,hnest₁,hother⟩ := hcompare m
  calc
    (sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ a ψ : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₀ m) (R₀ m) := hcoord₀ m
    _ = sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c₁ m) (R₁ m) :=
      sourcePsiEquationCoordinate_eq_of_common_outer hp hp1 n m
        (a : Coeff p) ψ (c₀ m) (c₁ m) c (R₀ m) (R₁ m) R
        hr₀ hr₁ hR hseg₀ hseg₁ hseg hnest₀ hnest₁ hother
    _ = (sourcePsiSelectedEquationSequence hp hp1 n c₁ R₁ a ψ : Coeff p) m :=
      (hcoord₁ m).symm

/-- A zero sequence in one selected contour chart remains a zero at
its strong limit whenever the chart is `C¹` near that limit. -/
theorem sourcePsiSelectedEquationSequence_zero_of_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hC1 : ContDiffOn ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : ℕ → DeletedCoeff p n) (ψ : ℕ → CoeffPair p)
    (b : DeletedCoeff p n) (φ : CoeffPair p)
    (ha : Tendsto a atTop (𝓝 b))
    (hψ : Tendsto ψ atTop (𝓝 φ))
    (hmem : (b,φ) ∈ U)
    (hzero : ∀ᶠ k : ℕ in atTop,
      sourcePsiSelectedEquationSequence hp hp1 n c R (a k) (ψ k) = 0) :
    sourcePsiSelectedEquationSequence hp hp1 n c R b φ = 0 := by
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hpair : Tendsto (fun k => (a k,ψ k)) atTop (𝓝 (b,φ)) :=
    ha.prodMk_nhds hψ
  have hlimit : Tendsto (fun k => F (a k,ψ k)) atTop (𝓝 (F (b,φ))) :=
    (hC1.contDiffAt (hUopen.mem_nhds hmem)).continuousAt.tendsto.comp hpair
  have hzeroLimit : Tendsto (fun k => F (a k,ψ k)) atTop
      (𝓝 (0 : DeletedCoeff p n)) :=
    tendsto_const_nhds.congr' (hzero.mono (fun k hk => hk.symm))
  exact tendsto_nhds_unique hlimit hzeroLimit

/-- Zeros represented in varying selected contour families pass to a
limit in one fixed `C¹` chart when the families are eventually
comparable through common outer circles. -/
theorem sourcePsiSelectedEquationSequence_zero_of_tendsto_varying_contours
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hC1 : ContDiffOn ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : ℕ → DeletedCoeff p n) (ψ : ℕ → CoeffPair p)
    (b : DeletedCoeff p n) (φ : CoeffPair p)
    (ha : Tendsto a atTop (𝓝 b))
    (hψ : Tendsto ψ atTop (𝓝 φ))
    (hmem : (b,φ) ∈ U)
    (c' : ℕ → ℤ → ℂ) (R' : ℕ → ℤ → ℝ)
    (hcoord : ∀ᶠ k : ℕ in atTop, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R (a k) (ψ k) : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a k : Coeff p) (ψ k) (c m) (R m))
    (hcoord' : ∀ᶠ k : ℕ in atTop, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n (c' k) (R' k)
        (a k) (ψ k) : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a k : Coeff p) (ψ k) (c' k m) (R' k m))
    (hcompare : ∀ᶠ k : ℕ in atTop,
      sourcePsiContourFamiliesComparable hp hp1 (ψ k)
        c (c' k) R (R' k))
    (hzero : ∀ᶠ k : ℕ in atTop,
      sourcePsiSelectedEquationSequence hp hp1 n (c' k) (R' k)
        (a k) (ψ k) = 0) :
    sourcePsiSelectedEquationSequence hp hp1 n c R b φ = 0 := by
  apply sourcePsiSelectedEquationSequence_zero_of_tendsto
    hp hp1 n c R U hUopen hC1 a ψ b φ ha hψ hmem
  filter_upwards [hcoord,hcoord',hcompare,hzero] with k hk hk' hc hz
  rw [sourcePsiSelectedEquationSequence_eq_of_comparable_contours
    hp hp1 n (a k) (ψ k) c (c' k) R (R' k) hk hk' hc]
  exact hz

end NLS.ZakharovShabat
