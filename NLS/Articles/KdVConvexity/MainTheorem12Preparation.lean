import NLS.Articles.KdVConvexity.MainTheorem11
import NLS.KdV.HillRoughFourierLebesgueInverseCompatibility
import NLS.KdV.HillHminusRetainedFourierLebesgueMiuraGerms

/-! # Theorem 1.2: exact physical restriction, global bijection and fixed inverse

The original real mean-zero Fourier-Lebesgue norms and literal signed
physical map are retained. The stated bijection and both inclusion
diagrams are proved on the entire source and target, for every requested
order and finite exponent. Native analyticity in both directions remains
an explicit unproved requirement of `Theorem12PhysicalData`.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Articles.KdVConvexity
open NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

/-- Precise remaining Theorem 1.2 data: the SAME original physical map
is a real analytic diffeomorphism in both original native norms, for
EVERY -1/2<=s<=0 and EVERY finite p>=2. Its actual bijection, full signed
recovery and fixed rough inverse are already constructed unconditionally. -/
structure Theorem12PhysicalData where
  physicalMap : GlobalRoughAbelianForwardData
  analytic_forward : ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
    ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      AnalyticOnNhd ℝ (physicalMap.fourierLebesgueForward s hs p hp h2p) univ
  analytic_inverse : ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
    ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      AnalyticOnNhd ℝ (physicalMap.fourierLebesgueEquiv s hs p hp h2p).symm univ

/-- The exact global bijection and BOTH fixed rough inclusion diagrams
of Theorem 1.2. This does not claim the remaining native analyticity. -/
theorem theorem_1_2_bijection_and_fixed_inverse :
    ∃ D : GlobalRoughAbelianForwardData,
      ∀ (s : ℝ) (hs : -1/2≤s), s≤0 →
      ∀ (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)],
      ∃ e : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p ≃
          physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p,
        (∀ a, e a=D.fourierLebesgueForward s hs p hp h2p a) ∧
        (∀ a, fourierLebesgueTargetNormalization s hs p hp h2p (e a)=
          D.realWeakHomeomorph (fourierLebesgueSourceNormalization s hs p hp h2p a)) ∧
        (∀ z, fourierLebesgueSourceNormalization s hs p hp h2p (e.symm z)=
          D.realWeakHomeomorph.symm (fourierLebesgueTargetNormalization s hs p hp h2p z)) ∧
        (∀ z, D.signed (fourierLebesgueSourceInclusion s hs p hp h2p (e.symm z).val)=
          fourierLebesgueTargetInclusion s hs p hp h2p z.val) := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  refine ⟨D,?_⟩
  intro s hs _hsupper p hp h2p inst
  refine ⟨D.fourierLebesgueEquiv s hs p hp h2p,(fun _ => rfl),?_,?_,?_⟩
  · exact D.fourierLebesgueForward_weak_commuting s hs p hp h2p
  · exact D.fourierLebesgueEquiv_symm_weak_commuting s hs p hp h2p
  · exact D.fourierLebesgueEquiv_symm_signed s hs p hp h2p

/-- The fixed physical global map retains an actual native analytic
Miura lift germ at EVERY real Fourier-Lebesgue source. The chart is the
already-chosen chart of D, rather than a replacement chart. -/
theorem exists_actual_physical_fourierLebesgue_miura_lift
    (D : GlobalRoughAbelianForwardData) (s p : ℝ) (hs : -1/2≤s) (hp : 2<p)
    [Fact (1≤ENNReal.ofReal p)] (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hreal : IsRealPeriodOneHminusOne (periodOneFourierLebesgueImageInclusion s p hs hp q)) :
    let q0 : PeriodOneRealHminusOne := ⟨periodOneFourierLebesgueImageInclusion s p hs hp q,hreal⟩
    let P := (D.chart q0).data.chart
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) →
        WeightedCoeff (Weight.sobolev (s+1)) (ENNReal.ofReal p),
        AnalyticOnNhd ℂ g V ∧ ∀ x∈V,
          periodOneFourierLebesgueImageInclusion s p hs hp x∈P.miura.domain ∧
          ∀ n : ℤ, (g x).val n=P.miura.lift (periodOneFourierLebesgueImageInclusion s p hs hp x) n := by
  let q0 : PeriodOneRealHminusOne := ⟨periodOneFourierLebesgueImageInclusion s p hs hp q,hreal⟩
  let R := (D.chart q0).data
  have hq := R.source_domain (Metric.mem_ball_self R.radius_pos)
  exact R.chart.exists_fourierLebesgue_native_Miura_lift R.native_lifts s p hs hp q hq.1.1

end NLS.Articles.KdVConvexity
