import NLS.ZakharovShabat.SourcePeriodTwoAsymptotics
import NLS.ZakharovShabat.PeriodicGapSummability

/-!
# Midpoint and gap asymptotics for arbitrary period-two inputs

The contour midpoint and squared gap agree with the actual counted spectral
pair at every sufficiently distant signed index. Their power tails therefore
inherit the original-norm displacement bound. Central contour values are not
asserted to label the individual central eigenvalue pairs.
-/

noncomputable section
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- A common power bound for the midpoint displacement and gap of two roots. -/
theorem midpoint_gap_power_le {P : ℝ} (hP : 1 ≤ P) (x y c : ℂ) :
    ‖(x+y)/2-c‖^P ≤ (2 : ℝ)^(P-1)*(‖x-c‖^P+‖y-c‖^P) ∧
    ‖x-y‖^P ≤ (2 : ℝ)^(P-1)*(‖x-c‖^P+‖y-c‖^P) := by
  have hm : (‖x-c‖+‖y-c‖)^P ≤ (2 : ℝ)^(P-1)*(‖x-c‖^P+‖y-c‖^P) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow
      (⟨‖x-c‖,norm_nonneg _⟩ : ℝ≥0) (⟨‖y-c‖,norm_nonneg _⟩ : ℝ≥0) hP
  have ha : ‖(x+y)/2-c‖ ≤ ‖x-c‖+‖y-c‖ := by
    rw [show (x+y)/2-c = ((x-c)+(y-c))/2 by ring, norm_div]
    norm_num only [Complex.norm_ofNat]
    have h := norm_add_le (x-c) (y-c)
    linarith [norm_nonneg (x-c),norm_nonneg (y-c)]
  have hb : ‖x-y‖ ≤ ‖x-c‖+‖y-c‖ := by
    simpa only [sub_sub_sub_cancel_right] using norm_sub_le (x-c) (y-c)
  exact ⟨(Real.rpow_le_rpow (norm_nonneg _) ha (zero_le_one.trans hP)).trans hm,
    (Real.rpow_le_rpow (norm_nonneg _) hb (zero_le_one.trans hP)).trans hm⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Joint intrinsic midpoint and squared-gap power tail, in the original raw input. -/
def sourcePeriodTwoMidpointGapTail (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then
    ‖periodicMidpoint hp (CoeffPair.toMax p φ) n-(Real.pi : ℂ)*n‖^p.toReal +
      ‖periodicSquaredGap hp (CoeffPair.toMax p φ) n‖^(p.toReal/2) else 0

/-- The actual contour invariants are controlled by any counted high spectral pairs. -/
theorem sourcePeriodTwoMidpointGapTail_le (hp : p ≠ ⊤) (φ : CoeffPair p) (N : ℕ)
    (ξ η : ℤ → ℂ)
    (hr : ∀ n : ℤ, N ≤ n.natAbs →
      PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv φ) n (ξ n) (η n)) (n : ℤ) :
    sourcePeriodTwoMidpointGapTail hp φ N n ≤
      (2*(2 : ℝ)^(p.toReal-1))*rootDisplacementPowerTail p N ξ η n := by
  by_cases hn : N ≤ n.natAbs
  · have hm := (hr n hn).midpoint_eq
    have hg := (hr n hn).squaredGap_eq
    rw [weightedBaseToPair_unitWeightedPairEquiv] at hm hg
    simp only [sourcePeriodTwoMidpointGapTail,rootDisplacementPowerTail,if_pos hn,hm,hg,norm_sq_rpow_half]
    have hP : 1 ≤ p.toReal := (ENNReal.toReal_le_toReal (by simp) hp).mpr (show 1 ≤ p from Fact.out)
    obtain ⟨ha,hb⟩ := midpoint_gap_power_le hP (ξ n) (η n) ((Real.pi : ℂ)*n)
    linarith
  · simp [sourcePeriodTwoMidpointGapTail,rootDisplacementPowerTail,hn]

/-- Locally uniformly small intrinsic midpoint and gap power tails in the original norm. -/
theorem exists_uniform_small_sourcePeriodTwoMidpointGapTail (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (sourcePeriodTwoMidpointGapTail hp ψ N) ∧
        (∑' n : ℤ, sourcePeriodTwoMidpointGapTail hp ψ N n) < ε := by
  let K := 2*(2 : ℝ)^(p.toReal-1)
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨N₀,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_1_asymptotics hp hp1 φ (div_pos hε hK)
  refine ⟨N₀,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ N hNN
  obtain ⟨ξ,η,_,_,hpair,_,ht⟩ := hr ψ hψ
  have hs := ((ht N hNN).1).mul_left K
  have hb := sourcePeriodTwoMidpointGapTail_le hp ψ N ξ η (fun n hn => hpair n (hNN.trans hn))
  have hn (n : ℤ) : 0 ≤ sourcePeriodTwoMidpointGapTail hp ψ N n := by
    unfold sourcePeriodTwoMidpointGapTail
    split_ifs <;> positivity
  have hs' := hs.of_nonneg_of_le hn hb
  refine ⟨hs',lt_of_le_of_lt (hs'.tsum_le_tsum hb hs) ?_⟩
  rw [tsum_mul_left]
  exact (mul_lt_mul_of_pos_left (ht N hNN).2.2 hK).trans_eq (mul_div_cancel₀ ε hK.ne')

/-- Full intrinsic midpoint and squared-gap power sums converge. The finitely
many central contour values do not affect this assertion. -/
theorem sourcePeriodTwoMidpointGap_summable (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Summable (fun n : ℤ => ‖periodicMidpoint hp (CoeffPair.toMax p φ) n-(Real.pi : ℂ)*n‖^p.toReal) ∧
      Summable (fun n : ℤ => ‖periodicSquaredGap hp (CoeffPair.toMax p φ) n‖^(p.toReal/2)) := by
  obtain ⟨N,_,U,_,_,hφ,_,ht⟩ := exists_uniform_small_sourcePeriodTwoMidpointGapTail hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  let F := fun n : ℤ => ‖periodicMidpoint hp (CoeffPair.toMax p φ) n-(Real.pi : ℂ)*n‖^p.toReal +
    ‖periodicSquaredGap hp (CoeffPair.toMax p φ) n‖^(p.toReal/2)
  have hf : (fun n : ℤ => if N ≤ n.natAbs then (0 : ℝ) else F n).HasFiniteSupport := by
    apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
    intro n hn
    have hh : ¬N ≤ n.natAbs := by intro h; simp [Function.mem_support,h] at hn
    constructor <;> omega
  have hs : Summable F := by
    convert (ht φ hφ N le_rfl).1.add (summable_of_hasFiniteSupport hf) using 1
    funext n
    simp only [sourcePeriodTwoMidpointGapTail,F]
    split_ifs <;> simp
  exact ⟨hs.of_nonneg_of_le (fun _ => by positivity) (fun _ => le_add_of_nonneg_right (by positivity)),
    hs.of_nonneg_of_le (fun _ => by positivity) (fun _ => le_add_of_nonneg_left (by positivity))⟩

/-- The full intrinsic midpoint displacement belongs to the original scalar ℓᵖ space. -/
theorem sourcePeriodTwoMidpoint_mem (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    Memℓp (fun n : ℤ => periodicMidpoint hp (CoeffPair.toMax p φ) n-(Real.pi : ℂ)*n) p :=
  (memℓp_gen_iff (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp)).mpr
    (sourcePeriodTwoMidpointGap_summable hp hp1 φ).1

/-- Actual distant spectral pairs give the displayed midpoint and gap ℓᵖ asymptotics.
The selected finite central entries remain unspecified, as in Proposition 6.1. -/
theorem sourcePeriodTwo_midpoint_gap_asymptotics (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (CoeffPair p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        ∃ ξ η : ℤ → ℂ,
          (∀ n : ℤ, N ≤ n.natAbs →
            PeriodicResonantPair hp SpectralWeight.one (unitWeightedPairEquiv ψ) n (ξ n) (η n)) ∧
          Memℓp (fun n : ℤ => (ξ n+η n)/2-(Real.pi : ℂ)*n) p ∧
          Memℓp (fun n : ℤ => ξ n-η n) p := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := sourceProposition6_1_asymptotics hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,hpair,_,_⟩ := hr ψ hψ
  refine ⟨ξ,η,hpair,?_,?_⟩
  · convert (hξ.add hη).const_smul (1/2 : ℂ) using 1
    funext n
    change (ξ n+η n)/2-(Real.pi : ℂ)*n = (1/2 : ℂ)*((ξ n-(Real.pi : ℂ)*n)+(η n-(Real.pi : ℂ)*n))
    ring
  · convert hξ.sub hη using 1
    funext n
    change ξ n-η n = (ξ n-(Real.pi : ℂ)*n)-(η n-(Real.pi : ℂ)*n)
    ring

end NLS.ZakharovShabat
