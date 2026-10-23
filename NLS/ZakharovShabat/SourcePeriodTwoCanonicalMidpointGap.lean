import NLS.ZakharovShabat.SourcePeriodTwoCanonicalEndpoints
import NLS.ZakharovShabat.SourcePeriodTwoMidpointGap

/-! # Midpoints and gaps of the complete canonical period-two spectrum

The definitions use the actual ordered pair at every index, including the
central block. Their displacements are in ℓᵖ and their power tails are
locally uniformly small. Identification with contour invariants is asserted
only past a common central cutoff.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The midpoint of the actual canonical spectral pair, also at central indices. -/
def sourcePeriodTwoCanonicalMidpoint (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  (sourcePeriodTwoCanonicalLeft hp hp1 φ n + sourcePeriodTwoCanonicalRight hp hp1 φ n)/2

/-- The ordered gap of the actual canonical spectral pair. -/
def sourcePeriodTwoCanonicalGap (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) : ℂ :=
  sourcePeriodTwoCanonicalRight hp hp1 φ n - sourcePeriodTwoCanonicalLeft hp hp1 φ n

/-- The complete canonical midpoint displacement and gap both belong to ℓᵖ. -/
theorem sourcePeriodTwoCanonicalMidpointGap_memℓp (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Memℓp (fun n => sourcePeriodTwoCanonicalMidpoint hp hp1 φ n-(Real.pi : ℂ)*n) p ∧
      Memℓp (sourcePeriodTwoCanonicalGap hp hp1 φ) p := by
  obtain ⟨hl,hr⟩ := sourcePeriodTwoCanonicalEndpoints_memℓp hp hp1 φ
  constructor
  · convert (hl.add hr).const_smul (1/2 : ℂ) using 1
    funext n
    dsimp [sourcePeriodTwoCanonicalMidpoint]
    ring
  · convert hr.sub hl using 1
    funext n
    dsimp [sourcePeriodTwoCanonicalGap]
    ring

/-- The joint midpoint and gap power tail of the fixed canonical sequences. -/
def sourcePeriodTwoCanonicalMidpointGapTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (K : ℕ) (n : ℤ) : ℝ :=
  if K ≤ n.natAbs then
    ‖sourcePeriodTwoCanonicalMidpoint hp hp1 φ n-(Real.pi : ℂ)*n‖^p.toReal +
      ‖sourcePeriodTwoCanonicalGap hp hp1 φ n‖^p.toReal else 0

/-- A common displacement majorant controls the canonical midpoint and gap tail. -/
theorem sourcePeriodTwoCanonicalMidpointGapTail_le (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (K : ℕ) (n : ℤ) :
    sourcePeriodTwoCanonicalMidpointGapTail hp hp1 φ K n ≤
      (2*(2 : ℝ)^(p.toReal-1))*rootDisplacementPowerTail p K
        (sourcePeriodTwoCanonicalLeft hp hp1 φ) (sourcePeriodTwoCanonicalRight hp hp1 φ) n := by
  unfold sourcePeriodTwoCanonicalMidpointGapTail rootDisplacementPowerTail
  split_ifs with hn
  · have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
    obtain ⟨hm,hg⟩ := midpoint_gap_power_le hP (sourcePeriodTwoCanonicalLeft hp hp1 φ n)
      (sourcePeriodTwoCanonicalRight hp hp1 φ n) ((Real.pi : ℂ)*n)
    simp only [sourcePeriodTwoCanonicalMidpoint,sourcePeriodTwoCanonicalGap,norm_sub_rev] at *
    linarith
  · norm_num

/-- The actual canonical midpoints and gaps have locally uniform small tails and a corrected budget. -/
theorem sourcePeriodTwoCanonicalMidpointGap_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        Summable (sourcePeriodTwoCanonicalMidpointGapTail hp hp1 ψ K) ∧
        (∑' n : ℤ, sourcePeriodTwoCanonicalMidpointGapTail hp hp1 ψ K n) ≤
          (2*(2 : ℝ)^(p.toReal-1))*sourcePeriodTwoDisplacementBudget ψ K ∧
        (∑' n : ℤ, sourcePeriodTwoCanonicalMidpointGapTail hp hp1 ψ K n) < ε := by
  let C := 2*(2 : ℝ)^(p.toReal-1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨N,hN,U,ho,hc,hφ,h0,ht⟩ := sourceProposition6_1_canonical_asymptotics hp hp1 φ (div_pos hε hC)
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  obtain ⟨hs,hb,hsmall⟩ := (ht ψ hψ).2 K hK
  have hsC := hs.mul_left C
  have hnonneg (n : ℤ) : 0 ≤ sourcePeriodTwoCanonicalMidpointGapTail hp hp1 ψ K n := by
    unfold sourcePeriodTwoCanonicalMidpointGapTail
    split_ifs <;> positivity
  have hle := sourcePeriodTwoCanonicalMidpointGapTail_le hp hp1 ψ K
  have hs' := hsC.of_nonneg_of_le hnonneg hle
  have hsum := hs'.tsum_le_tsum hle hsC
  rw [tsum_mul_left] at hsum
  exact ⟨hs',hsum.trans (mul_le_mul_of_nonneg_left hb hC.le),
    hsum.trans_lt ((mul_lt_mul_of_pos_left hsmall hC).trans_eq (mul_div_cancel₀ ε hC.ne'))⟩

/-- Equal spectral pair multisets have equal midpoint and squared gap. -/
theorem midpoint_squaredGap_eq_of_pair_multiset (x y a b : ℂ)
    (h : ({x,y} : Multiset ℂ) = {a,b}) : (x+y)/2 = (a+b)/2 ∧ (y-x)^2 = (a-b)^2 := by
  have hp : List.Perm [x,y] [a,b] := Multiset.coe_eq_coe.mp h
  have he : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
    simpa only [List.cons.injEq,and_true] using List.perm_pair.mp hp
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> constructor <;> ring

/-- Past one common cutoff, canonical midpoints and squared gaps equal the actual contour invariants. -/
theorem sourcePeriodTwoCanonicalMidpointGap_eq_contours (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ n : ℤ, N₀ < n.natAbs →
        sourcePeriodTwoCanonicalMidpoint hp hp1 ψ n = periodicMidpoint hp (CoeffPair.toMax p ψ) n ∧
        sourcePeriodTwoCanonicalGap hp hp1 ψ n ^ 2 = periodicSquaredGap hp (CoeffPair.toMax p ψ) n := by
  obtain ⟨Nc,hNc,V,hoV,hcV,hφV,h0V,hcanon⟩ := sourceProposition6_1_canonical_asymptotics hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Nr,_,W,hoW,hcW,hφW,h0W,hr⟩ := exists_uniform_sourcePeriodTwoDisplacement hp hp1 φ
  refine ⟨max Nc Nr,hNc.trans (le_max_left _ _),V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ n hn
  obtain ⟨ξ,η,hpair,_,_⟩ := hr ψ hψ.2
  have hc := (hcanon ψ hψ.1).1.distant n (by omega)
  have hrn := hpair n (by omega)
  have he := hrn.toEndpoints
  rw [weightedBaseToPair_unitWeightedPairEquiv] at he
  obtain ⟨hm,hg⟩ := midpoint_squaredGap_eq_of_pair_multiset _ _ _ _ (hc.multiset_eq he)
  have hmc := hrn.midpoint_eq
  have hgc := hrn.squaredGap_eq
  rw [weightedBaseToPair_unitWeightedPairEquiv] at hmc hgc
  exact ⟨hm.trans hmc.symm,hg.trans hgc.symm⟩

end NLS.ZakharovShabat
