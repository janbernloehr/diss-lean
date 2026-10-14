import NLS.ZakharovShabat.SourceNormalizedIndexedActionUniform

/-!
# The remaining page 62 estimates on the original source domain

The literal gap supremum and normalized indexed-action deviation have
actual ℓ^(p/2)+ℓ^(1+) summands. Near every complex source, one neighborhood
and four summand functions work before any index or one-plus exponent is
chosen. The critical coordinate itself has a bounded half-exponent
coefficient. No further shrinking of the original W is made.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact critical coordinate is an actual half-exponent sequence,
with its quantitative bound, also at collapsed complex gaps. -/
theorem SourceEquation2_18Data.criticalCoordinate_halfExponent
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ a : Coeff (p/2), (∀ n : ℤ, a n = sourceActionCriticalCoordinate hp hp1 n ψ) ∧
      ‖a‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 ψ‖*‖sourceCriticalGapQuotient hp hp1 ψ‖ := by
  have hhalf : 0 < ENNReal.ofReal (p.toReal/2) := by
    rw [Coeff.halfExponent_eq_div hp]
    exact ENNReal.div_pos (zero_lt_one.trans hp1).ne' (by norm_num)
  have he : ∃ a : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ, a n = sourceActionCriticalCoordinate hp hp1 n ψ) ∧
      ‖a‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 ψ‖*‖sourceCriticalGapQuotient hp hp1 ψ‖ := by
    refine ⟨(2:ℂ) • sourceCriticalGapLinearOffset hp hp1 ψ,?_,?_⟩
    · intro n
      rw [H.actionCriticalCoordinate_eq_gap_mul ψ hψ n,← sourcePeriodicGapDisplacement_apply]
      simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,sourceCriticalGapLinearOffset_apply]
      ring
    · rw [lp.norm_const_smul hhalf.ne']
      norm_num only [Complex.norm_ofNat]
      nlinarith [norm_sourceCriticalGapLinearOffset_le hp hp1 ψ]
  rw [← Coeff.halfExponent_eq_div hp]
  exact he

/-- The half-exponent critical-coordinate bound is locally uniform on all of W. -/
theorem SourceEquation2_18Data.criticalCoordinate_locally_uniform
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ∃ a : Coeff (p/2),
        (∀ n : ℤ, a n = sourceActionCriticalCoordinate hp hp1 n ψ) ∧ ‖a‖ ≤ K := by
  obtain ⟨Vb,hVb,_,hφb,hbW,B,hB,hbound⟩ := H.criticalOffsets.locally_uniform φ hφ
  obtain ⟨_,_,Vg,hVg,hφg,G,hG,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0:ℝ)<1)
  refine ⟨Vb ∩ Vg,hVb.inter hVg,⟨hφb,hφg⟩,fun _ hψ => hbW hψ.1,2*G*B,by positivity,?_⟩
  intro ψ hψ
  obtain ⟨a,ha,han⟩ := H.criticalCoordinate_halfExponent ψ (hbW hψ.1)
  refine ⟨a,ha,han.trans ?_⟩
  gcongr
  · exact (hgap ψ hψ.2).1
  · exact hbound ψ hψ.1

/-- Fixed summand functions for both estimates on one source neighborhood. -/
def SourceSection11UniformAsymptotics (hp : p ≠ ⊤) (hp1 : 1 < p) (V : Set (CoeffPair p)) : Prop :=
  ∃ Gχ GA : CoeffPair p → Coeff (p/2), ∃ Bχ BA : CoeffPair p → CoeffOnePlus,
    (∀ ψ ∈ V, ∀ n : ℤ,
      (sourceActionChiGapSup hp hp1 ψ n : ℂ) = Gχ ψ n+(Bχ ψ).1 n ∧
      4*sourceNormalizedIndexedAction hp hp1 n ψ-1 = GA ψ n+(BA ψ).1 n) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ‖Gχ ψ‖ ≤ K ∧ ‖GA ψ‖ ≤ K) ∧
    ∀ (r : ℝ≥0∞) (hr1 : 1 < r) (hr : r ≠ ⊤),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V,
        ‖CoeffOnePlus.toCoeff r hr1 hr (Bχ ψ)‖ ≤ K ∧ ‖CoeffOnePlus.toCoeff r hr1 hr (BA ψ)‖ ≤ K

/-- The original-domain assertions following (2.19), with the earlier formulas retained. -/
structure SourceSection11OriginalEstimates (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) : Prop where
  previous : SourceEquation2_19Data hp hp1 W
  locally_uniform : ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
    SourceSection11UniformAsymptotics hp hp1 V
  critical_coordinate : ∀ φ ∈ W, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ V, ∃ a : Coeff (p/2),
      (∀ n : ℤ, a n = sourceActionCriticalCoordinate hp hp1 n ψ) ∧ ‖a‖ ≤ K

/-- Upgrade every existing original open domain, with no reality restriction or domain shrink. -/
theorem SourceEquation2_19Data.originalEstimates
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (hW : IsOpen W) :
    SourceSection11OriginalEstimates hp hp1 W := by
  refine ⟨H,?_,H.previous.criticalCoordinate_locally_uniform⟩
  intro φ hφ
  obtain ⟨V,hV,hφV,hVW,hs,ha⟩ := H.uniform_refined hW φ hφ
  have htop : p/2 ≠ ⊤ := ENNReal.div_ne_top hp (by norm_num)
  obtain ⟨Gχ,Bχ,heχ,⟨Kχ,hKχ,hGχ⟩,hBχ⟩ := Coeff.exists_onePlus_decomposition_of_refined V
    (fun ψ n => (sourceActionChiGapSup hp hp1 ψ n : ℂ)) htop hs
  obtain ⟨GA,BA,heA,⟨KA,hKA,hGA⟩,hBA⟩ := Coeff.exists_onePlus_decomposition_of_refined V
    (fun ψ n => 4*sourceNormalizedIndexedAction hp hp1 n ψ-1) htop ha
  refine ⟨V,hV,hφV,hVW,Gχ,GA,Bχ,BA,(fun ψ hψ n => ⟨heχ ψ hψ n,heA ψ hψ n⟩),
    ⟨max Kχ KA,hKχ.trans (le_max_left _ _),fun ψ hψ =>
      ⟨(hGχ ψ hψ).trans (le_max_left _ _),(hGA ψ hψ).trans (le_max_right _ _)⟩⟩,?_⟩
  intro r hr1 hr
  obtain ⟨Lχ,hLχ,hχ⟩ := hBχ r hr1 hr
  obtain ⟨LA,_,hA⟩ := hBA r hr1 hr
  exact ⟨max Lχ LA,hLχ.trans (le_max_left _ _),fun ψ hψ =>
    ⟨(hχ ψ hψ).trans (le_max_left _ _),(hA ψ hψ).trans (le_max_right _ _)⟩⟩

/-- The remaining page 62 estimates for every finite p>1 on the original connected W. -/
theorem sourceSection11OriginalEstimates (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceSection11OriginalEstimates hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceEquation2_19 hp hp1
  exact ⟨W,ho,hc,hr,H.originalEstimates ho⟩

end NLS.ZakharovShabat
