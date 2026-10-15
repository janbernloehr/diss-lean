import NLS.ZakharovShabat.SourceRealBallCore
import NLS.ZakharovShabat.SourceSection14Original
import NLS.ZakharovShabat.SourceBirkhoffCoordinateExponent

/-!
# Original Birkhoff maps on complex exponent intersections

A complex point in the two ball cores lies in a convex overlap containing
its real-type projection. Banach-valued analytic uniqueness propagates
real-source agreement throughout this overlap. This proves equality of
the full sequences without choosing separate neighborhoods for each index.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

namespace SourceSection14OriginalData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {hq : q ≠ ⊤} {hq1 : 1 < q} {A B C : Set (CoeffPair q)}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- The full rectangular sequences agree at real sources after exponent inclusion. -/
theorem map_real_exponent (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (E : SourceSection14OriginalData hq hq1 A B C t) (hpq : p ≤ q)
    (φ : realTypeSourceLocus p) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceBirkhoffMap hp hp1 s φ.val) =
        sourceBirkhoffMap hq hq1 t (CoeffPair.exponentInclusion hpq φ.val) := by
  have hcoord n := D.complex.angular.birkhoffXY_real_exponent E.complex.angular V C
    D.complex.source_open E.complex.source_open D.complex.source_subset E.complex.source_subset hpq n
    ⟨φ.val,φ.property⟩ (D.complex.real_subset φ.property)
    (E.complex.real_subset (realTypeSourceExponentInclusion hpq ⟨φ.val,φ.property⟩).property)
  have hD n := D.complex.coordinates φ.val (D.complex.real_subset φ.property) n
  have hE n := E.complex.coordinates (CoeffPair.exponentInclusion hpq φ.val)
    (E.complex.real_subset (realTypeSourceExponentInclusion hpq ⟨φ.val,φ.property⟩).property) n
  apply Prod.ext
  · ext n
    change (sourceBirkhoffMap hp hp1 s φ.val).1 n =
      (sourceBirkhoffMap hq hq1 t (CoeffPair.exponentInclusion hpq φ.val)).1 n
    rw [(hD n).1,(hE n).1]
    exact (hcoord n).1
  · ext n
    change (sourceBirkhoffMap hp hp1 s φ.val).2 n =
      (sourceBirkhoffMap hq hq1 t (CoeffPair.exponentInclusion hpq φ.val)).2 n
    rw [(hD n).2,(hE n).2]
    exact (hcoord n).2

/-- The original maps agree on the entire intersection of the real-centered
ball cores, including non-real sources and collapsed gaps. -/
theorem map_exponent_on_realBallCore (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (E : SourceSection14OriginalData hq hq1 A B C t) (hpq : p ≤ q)
    (ψ : CoeffPair p) (hψ : ψ ∈ sourceRealBallCore V)
    (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ sourceRealBallCore C) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceBirkhoffMap hp hp1 s ψ) =
        sourceBirkhoffMap hq hq1 t (CoeffPair.exponentInclusion hpq ψ) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  obtain ⟨r,hr⟩ := mem_iUnion.mp hφ
  obtain ⟨hball,hψ⟩ := mem_iUnion.mp hr
  obtain ⟨χ,hχ⟩ := mem_iUnion.mp hψ'
  obtain ⟨r',hr'⟩ := mem_iUnion.mp hχ
  obtain ⟨hball',hψ'⟩ := mem_iUnion.mp hr'
  let I : Set (CoeffPair p) := ball φ.val r ∩ CoeffPair.exponentInclusion hpq ⁻¹' ball χ.val r'
  let f : CoeffPair p → Coeff q × Coeff q := fun ψ =>
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) (sourceBirkhoffMap hp hp1 s ψ)
  let g : CoeffPair p → Coeff q × Coeff q :=
    sourceBirkhoffMap hq hq1 t ∘ CoeffPair.exponentInclusion hpq
  have hf : AnalyticOnNhd ℂ f I := fun x hx =>
    (((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)).analyticAt _).comp
      (D.complex.analytic x (hball hx.1))
  have hg : AnalyticOnNhd ℂ g I := fun x hx =>
    (E.complex.analytic _ (hball' hx.2)).comp ((CoeffPair.exponentInclusion hpq).analyticAt x)
  have hθ : sourceRealPart ψ ∈ I := by
    constructor
    · exact (dist_sourceRealPart_le_of_realType hp φ.val φ.property ψ).trans_lt hψ
    · change CoeffPair.exponentInclusion hpq (sourceRealPart ψ) ∈ ball χ.val r'
      rw [sourceRealPart_exponent]
      exact (dist_sourceRealPart_le_of_realType hq χ.val χ.property _).trans_lt hψ'
  have hconv : Convex ℝ I :=
    (convex_ball φ.val r).inter ((convex_ball χ.val r').linear_preimage
      ((CoeffPair.exponentInclusion hpq).restrictScalars ℝ).toLinearMap)
  have heq : f =ᶠ[𝓝 (sourceRealPart ψ)] g :=
    eventuallyEq_source_of_analyticAt_of_real_agreement hp
      ⟨sourceRealPart ψ,sourceRealPart_realType ψ⟩ f g (hf _ hθ) (hg _ hθ)
      (map_real_exponent D E hpq)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg hconv.isPreconnected hθ heq ⟨hψ,hψ'⟩

end SourceSection14OriginalData
end NLS.ZakharovShabat
