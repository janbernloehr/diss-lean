import NLS.Articles.MKdVBelowL2.PhysicalFourthFrequencyCandidate

/-! # Physical actual-action remainder of the H₄ candidate

The fixed ℓ^(p/3)+ℓ^(1+) components are transported to the original
period-one distributions. The actions are the actual products of the
same chosen physical Birkhoff coordinates used in Theorem 1.2.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical candidate has the refined actual-action remainder.
The domain and both remainder maps precede every OnePlus exponent.
The finite-coordinate term makes reconstruction valid also at zero. -/
theorem physicalFourthFrequencyCandidate_remainder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalFL p × PhysicalFL p)
    (hu : u ∈ physicalFourthCandidateDomain hp hp1) :
    ∃ T : Set (PhysicalFL p × PhysicalFL p), IsOpen T ∧ u ∈ T ∧
      T ⊆ physicalFourthCandidateDomain hp hp1 ∧
      ∃ a : (PhysicalFL p × PhysicalFL p) → Coeff (ENNReal.ofReal (p.toReal/3)),
      ∃ b : (PhysicalFL p × PhysicalFL p) → CoeffOnePlus,
        (∀ v ∈ T, ∀ n : ℤ,
          physicalFourthFrequencyCandidate hp hp1 n v+
            (12*Real.pi:ℂ)*(n:ℂ)*((compatibleBirkhoff hp hp1 v).1 n*(compatibleBirkhoff hp hp1 v).2 n) =
          (n:ℂ)*(a v n+(b v).1 n)+(if n=0 then physicalFourthFrequencyCandidate hp hp1 0 v else 0)) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖a v‖ ≤ C) ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b v)‖ ≤ C := by
  let C := fourthMomentChart hp hp1
  obtain ⟨Ts,hTs,hφTs,_,D⟩ := C.remainder (physicalCoefficients u) hu.2
  obtain ⟨a,b,he,ha,hb⟩ := D.mixed
  let T := physicalCoefficients ⁻¹' Ts ∩ physicalFourthCandidateDomain hp hp1
  have hT : IsOpen T := (hTs.preimage (physicalCoefficients (p := p)).continuous).inter
    (physicalFourthCandidateDomain_open_real hp hp1).1
  refine ⟨T,hT,⟨hφTs,hu⟩,inter_subset_right,
    fun v => a (physicalCoefficients v),fun v => b (physicalCoefficients v),?_,?_,?_⟩
  · intro v hv n
    rw [compatibleBirkhoff_action_on_fourthDomain hp hp1 v hv.2 n]
    change fourthFrequencyCandidate C.atlas n (physicalCoefficients v)+
      (12*Real.pi:ℂ)*(n:ℂ)*sourceComplexAction hp hp1 n (physicalCoefficients v) = _
    rw [fourthActionRemainder_reconstruct,he _ hv.1 n]
    rfl
  · obtain ⟨M,hM,ha⟩ := ha
    exact ⟨M,hM,fun v hv => ha _ hv.1⟩
  · intro q hq1 hq
    obtain ⟨M,hM,hb⟩ := hb q hq1 hq
    exact ⟨M,hM,fun v hv => hb _ hv.1⟩

/-- The printed asymptotic at nonzero indices, with actual physical actions
and one fixed pair of locally uniformly bounded remainder maps. -/
theorem physicalFourthFrequencyCandidate_asymptotic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalFL p × PhysicalFL p)
    (hu : u ∈ physicalFourthCandidateDomain hp hp1) :
    ∃ T : Set (PhysicalFL p × PhysicalFL p), IsOpen T ∧ u ∈ T ∧
      T ⊆ physicalFourthCandidateDomain hp hp1 ∧
      ∃ a : (PhysicalFL p × PhysicalFL p) → Coeff (ENNReal.ofReal (p.toReal/3)),
      ∃ b : (PhysicalFL p × PhysicalFL p) → CoeffOnePlus,
        (∀ v ∈ T, ∀ n : ℤ, n ≠ 0 →
          physicalFourthFrequencyCandidate hp hp1 n v+
            (12*Real.pi:ℂ)*(n:ℂ)*((compatibleBirkhoff hp hp1 v).1 n*(compatibleBirkhoff hp hp1 v).2 n) =
          (n:ℂ)*(a v n+(b v).1 n)) ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖a v‖ ≤ C) ∧
        ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ T, ‖CoeffOnePlus.toCoeff q hq1 hq (b v)‖ ≤ C := by
  obtain ⟨T,hT,huT,hTU,a,b,he,ha,hb⟩ := physicalFourthFrequencyCandidate_remainder hp hp1 u hu
  refine ⟨T,hT,huT,hTU,a,b,?_,ha,hb⟩
  intro v hv n hn
  simpa only [if_neg hn,add_zero] using he v hv n

end NLS.Articles.MKdVBelowL2
