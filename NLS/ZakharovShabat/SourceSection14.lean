import NLS.ZakharovShabat.SourceBirkhoffOriginalExponent

/-!
# Section 14 with compatible complex exponent domains

The original map is restricted to a union of real-centered balls, keeping
the same normalized roots, angles, actions, and real inverse properties.
Any two resulting packages agree on their entire complex intersection
after exponent inclusion. No real-type assumption is imposed there.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {hq : q ≠ ⊤} {hq1 : 1 < q} {A B C : Set (CoeffPair q)}
  {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- Restriction preserves the root family, analytic map, and indexed-action radius. -/
theorem SourceSection14OriginalData.restrict (D : SourceSection14OriginalData hp hp1 W₀ W V s)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (hrU : realTypeSourceLocus p ⊆ U) (hUV : U ⊆ V) :
    SourceSection14OriginalData hp hp1 W₀ W U s := by
  refine ⟨D.previous,⟨D.complex.angular,hU,hrU,hUV.trans D.complex.source_subset,
    D.complex.analytic.mono hUV,?_,?_,?_,?_⟩,?_⟩
  · intro ψ hψ
    obtain ⟨Z,hZ,hψZ,hZV,M,hM,hbound⟩ := D.complex.locally_bounded ψ (hUV hψ)
    exact ⟨Z ∩ U,hZ.inter hU,⟨hψZ,hψ⟩,inter_subset_right,M,hM,fun χ hχ => hbound χ hχ.1⟩
  · exact fun ψ hψ => D.complex.coordinates ψ (hUV hψ)
  · exact fun ψ hψ => D.complex.action_radius ψ (hUV hψ)
  · exact fun ψ hψ => D.complex.real_closed_gap_zero ψ (hUV hψ)
  · exact fun ψ hψ => D.indexed_action_radius ψ (hUV hψ)

/-- All Section 14 data, with complex domains suited to exponent compatibility. -/
structure SourceSection14Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W₀ W V : Set (CoeffPair p))
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop extends
    SourceSection14OriginalData hp hp1 W₀ W V s where
  domain_eq_core : sourceRealBallCore V = V

/-- Construct the original Section 14 map on a compatible complex domain for every finite p > 1. -/
theorem sourceSection14 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W V : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
      SourceSection14Data hp hp1 W₀ W V s := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14_original hp hp1
  exact ⟨W₀,W,sourceRealBallCore V,s,
    SourceSection14OriginalData.restrict D (sourceRealBallCore V) (sourceRealBallCore_open V)
      (sourceRealBallCore_real_subset V D.complex.source_open D.complex.real_subset)
      (sourceRealBallCore_subset V), sourceRealBallCore_idem V⟩

/-- Theorem 14.1(ii) on the full complex intersection of the constructed domains. -/
theorem SourceSection14Data.exponent (D : SourceSection14Data hp hp1 W₀ W V s)
    (E : SourceSection14Data hq hq1 A B C t) (hpq : p ≤ q)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ C) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceBirkhoffMap hp hp1 s ψ) =
        sourceBirkhoffMap hq hq1 t (CoeffPair.exponentInclusion hpq ψ) :=
  SourceSection14OriginalData.map_exponent_on_realBallCore D.toSourceSection14OriginalData E.toSourceSection14OriginalData hpq ψ
    (by rwa [D.domain_eq_core]) (by rwa [E.domain_eq_core])

/-- One common complex germ identifies the whole sequence map at any point of the overlap. -/
theorem SourceSection14Data.eventually_map_exponent (D : SourceSection14Data hp hp1 W₀ W V s)
    (E : SourceSection14Data hq hq1 A B C t) (hpq : p ≤ q)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ C) :
    (fun χ => ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq))
      (sourceBirkhoffMap hp hp1 s χ)) =ᶠ[𝓝 ψ]
        (sourceBirkhoffMap hq hq1 t ∘ CoeffPair.exponentInclusion hpq) := by
  filter_upwards [D.complex.source_open.mem_nhds hψ,
    (E.complex.source_open.preimage (CoeffPair.exponentInclusion hpq).continuous).mem_nhds hψ'] with χ hχ hχ'
  exact D.exponent E hpq χ hχ hχ'

/-- Full complex Fréchet derivatives commute with exponent inclusion throughout the overlap. -/
theorem SourceSection14Data.fderiv_exponent (D : SourceSection14Data hp hp1 W₀ W V s)
    (E : SourceSection14Data hq hq1 A B C t) (hpq : p ≤ q)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hψ' : CoeffPair.exponentInclusion hpq ψ ∈ C) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)).comp
      (fderiv ℂ (sourceBirkhoffMap hp hp1 s) ψ) =
        (fderiv ℂ (sourceBirkhoffMap hq hq1 t) (CoeffPair.exponentInclusion hpq ψ)).comp
          (CoeffPair.exponentInclusion hpq) := by
  have he := (D.eventually_map_exponent E hpq ψ hψ hψ').fderiv_eq (𝕜 := ℂ)
  have hf := D.complex.analytic ψ hψ
  have hg := E.complex.analytic _ hψ'
  change fderiv ℂ
    (((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) ∘ sourceBirkhoffMap hp hp1 s) ψ = _ at he
  rw [fderiv_comp ψ ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)).differentiableAt
    hf.differentiableAt,ContinuousLinearMap.fderiv,
    fderiv_comp ψ hg.differentiableAt (CoeffPair.exponentInclusion hpq).differentiableAt,
    ContinuousLinearMap.fderiv] at he
  exact he

end NLS.ZakharovShabat
