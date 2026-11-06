import NLS.MKdV.MiuraCartesianSobolevInverse
import NLS.SequenceSpaces.WeightedNonnegativeActionLifting

/-! # Arbitrary native nonnegative mKdV action data are attained

For every integer s>=1 the full positive action cone with weight 2s+1,
and an arbitrary signed mean, is realized by an actual original H^s
profile. Zero actions and infinite support are allowed.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Every positive native nonnegative action sequence and real mean admit
a real Cartesian representative with the exact native half-order shift. -/
theorem exists_miuraSobolevCartesian_action_data (s : ℕ)
    (J : WeightedCoeff (miuraSpectralActionWeight s) 1)
    (hJ : ∀ n, (J.val n).im = 0 ∧ 0 ≤ (J.val n).re)
    (hzero : ∀ n : ℤ, ¬0 < n → J.val n = 0) (c : ℝ) :
    ∃ z : MiuraRealSobolevCartesianTarget s, z.val.2 = (c : ℂ) ∧
      ∀ n, (1/2 : ℂ)*((z.val.1.1.val.val n)^2+(z.val.1.2.val.val n)^2) = J.val n := by
  obtain ⟨x,y,hreal,hradius⟩ := WeightedCoeff.exists_real_quadratic_lift
    (miuraCartesianWeight s) (miuraSpectralActionWeight s) (fun n => (miuraCartesianWeight_squared s n).symm) J hJ
  let z : MiuraPositiveSobolevTarget s :=
    ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 x,
      WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 y),(c : ℂ))
  have hz : z ∈ miuraSobolevCartesianRealSubmodule s := by
    apply (mem_miuraSobolevCartesianRealSubmodule_iff s z).mpr
    refine ⟨?_,rfl⟩
    intro n
    change ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 x).val.val n).im = 0 ∧
      ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 y).val.val n).im = 0
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply]
    by_cases hn : 0 < n
    · simpa only [if_pos hn] using hreal n
    · simp only [if_neg hn,Complex.zero_im,and_self]
  refine ⟨⟨z,hz⟩,rfl,?_⟩
  intro n
  change (1/2 : ℂ)*(((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 x).val.val n)^2+
    ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 y).val.val n)^2) = J.val n
  rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply]
  by_cases hn : 0 < n
  · simpa only [if_pos hn] using hradius n
  · rw [if_neg hn,if_neg hn,hzero n hn]
    ring

/-- Every native nonnegative physical action sequence with arbitrary
signed mean is attained on the entire original real H^s domain, s>=1. -/
theorem exists_miuraSobolev_profile_of_nonnegative_actions (s : ℕ) (hs : 1 ≤ s)
    (J : WeightedCoeff (miuraSpectralActionWeight s) 1)
    (hJ : ∀ n, (J.val n).im = 0 ∧ 0 ≤ (J.val n).re)
    (hzero : ∀ n : ℤ, ¬0 < n → J.val n = 0) (c : ℝ) :
    ∃ a : MiuraRealSobolevSource s, miuraSobolevActionSequence s a.val = J ∧ a.val.val 0 = (c : ℂ) := by
  obtain ⟨z,hmean,hradius⟩ := exists_miuraSobolevCartesian_action_data s J hJ hzero c
  obtain ⟨a,ha⟩ := miuraPhysicalSobolevCartesianMap_surjective s hs z
  have hmap := congrArg Subtype.val ha
  rw [miuraPhysicalSobolevCartesianMap_inclusion] at hmap
  refine ⟨a,?_,?_⟩
  · apply Subtype.ext
    funext n
    by_cases hn : 0 < n
    · have hx := congrArg (fun v : MiuraPositiveSobolevTarget s => v.1.1.val.val n) hmap
      have hy := congrArg (fun v : MiuraPositiveSobolevTarget s => v.1.2.val.val n) hmap
      change (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).1).val.val n = _ at hx
      change (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a.val).2).val.val n = _ at hy
      rw [WeightedCoeff.positiveProjection_apply,if_pos hn] at hx hy
      have he := congrArg (fun q : WeightedCoeff (miuraSpectralActionWeight s) 1 => q.val n)
        (miuraSobolevCartesianActions_sequence_eq s a.val a.property).symm
      change (miuraSobolevActionSequence s a.val).val n =
        (miuraSobolevCartesianActions s (miuraSobolevCartesianSequence s a.val)).val n at he
      rw [miuraSobolevCartesianActions_apply,hx,hy,hradius] at he
      exact he
    · rw [miuraSobolevActionSequence_nonpositive s a.val n hn,hzero n hn]
  · have he := congrArg Prod.snd hmap
    change a.val.val 0 = z.val.2 at he
    exact he.trans hmean

/-- The native H1 action entries are the independently defined physical
Hill actions on the literal original H1 input. -/
theorem miuraSobolevActionSequence_one_eq_physical (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    (miuraSobolevActionSequence 1 (miuraH1SobolevEquiv a)).val (n : ℤ) = miuraMKdVAction a ha n := by
  obtain ⟨U,_,haU,_,hcoord⟩ := exists_local_miuraSobolevActionSequence_analytic 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha)
  have hc := hcoord (miuraH1SobolevEquiv a) haU n (by omega)
  rw [miuraSobolevActionSource_eq_L2_diagonal] at hc
  have hraw : hierarchySobolevJetL2 1 0 (Nat.zero_le 1) (miuraH1SobolevEquiv a) = scalarInclusion a := by
    ext j
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraH1SobolevEquiv_apply,scalarInclusion_apply]
  rw [hraw] at hc
  change (miuraSobolevActionSequence 1 (miuraH1SobolevEquiv a)).val (n : ℤ) = miuraL2Action n (scalarInclusion a) at hc
  exact hc.trans (miuraL2Action_eq_physical a ha n hn)

end NLS.MKdV
