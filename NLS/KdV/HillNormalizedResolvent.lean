import NLS.KdV.HillNormalizedPencil

/-! The actual native resolvent factorization on the entire original base,
with the original H1 domain. The sign of A-lambda*J is explicit. -/
noncomputable section
open Set Metric
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The normalized inverse with the source lambda-minus-operator orientation. -/
def hillNormalizedResolventToH1 (r : ℝ) (q : WeightedCoeff (Weight.sobolev (-r)) 2) (z : ℂ) :
    FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2 :=
  (hillHalfToH1 z).comp ((hillNormalizedInverse r q z).comp (hillHalfFromBase z))

/-- Every original H-minus-one forcing is solved by the normalized formula. -/
theorem hillNormalizedResolventToH1_right (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) (F : FourierLebesgueSpace (2:ℝ) (-1) 2) :
    (z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q))
      (hillNormalizedResolventToH1 r q z F) = F := by
  have hBinj : Function.Injective (hillHalfFromBase z) :=
    Function.LeftInverse.injective (hillRootToBase_halfFromBase n hn z hz)
  apply hBinj
  change hillHalfFromBase z
    ((z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q))
      (hillHalfToH1 z (hillNormalizedInverse r q z (hillHalfFromBase z F)))) = _
  rw [hillNormalizedPencil_apply r hr hr1 q n hn hlog z hz]
  exact congrArg (fun T : Coeff 2 →L[ℂ] Coeff 2 => T (hillHalfFromBase z F))
    (hillNormalizedInverse_spec r q n hn z hz hS).1

/-- The normalized formula recovers EVERY original H1 vector, not only a core. -/
theorem hillNormalizedResolventToH1_left (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) (f : FourierLebesgueSpace (2:ℝ) 1 2) :
    hillNormalizedResolventToH1 r q z
      ((z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q)) f) = f := by
  have hQ := congrArg (fun T : Coeff 2 →L[ℂ] Coeff 2 => T (hillRootFromH1 z f))
    (hillNormalizedInverse_spec r q n hn z hz hS).2.1
  change hillHalfToH1 z (hillNormalizedInverse r q z (hillHalfFromBase z
    ((z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q)) f))) = f
  have hnorm := hillNormalizedPencil_apply r hr hr1 q n hn hlog z hz (hillRootFromH1 z f)
  rw [hillHalfToH1_rootFromH1 n hn z hz] at hnorm
  rw [hnorm]
  change hillHalfToH1 z (((hillNormalizedInverse r q z).comp
    (hillNormalizedPhase z-hillHalfSandwich r q z)) (hillRootFromH1 z f)) = f
  rw [hQ,ContinuousLinearMap.id_apply,hillHalfToH1_rootFromH1 n hn z hz]

/-- Actual smallness proves membership in the ORIGINAL native resolvent set. -/
theorem mem_singularHillResolventSet_of_halfSandwich_small (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) : z ∈ singularHillResolventSet (hillHalfPotentialBase r hr1 q) := by
  have hP : Function.Bijective
      (z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q)) :=
    ⟨Function.LeftInverse.injective (hillNormalizedResolventToH1_left r hr hr1 q n hn hlog z hz hS),
      Function.RightInverse.surjective (hillNormalizedResolventToH1_right r hr hr1 q n hn hlog z hz hS)⟩
  have he : singularHillOperator (hillHalfPotentialBase r hr1 q)-z • singularHillDomainInclusion =
      -(z • singularHillDomainInclusion-singularHillOperator (hillHalfPotentialBase r hr1 q)) := by
    rw [neg_sub]
  change Function.Bijective (singularHillOperator (hillHalfPotentialBase r hr1 q)-z • singularHillDomainInclusion)
  rw [he]
  exact (Equiv.neg (FourierLebesgueSpace (2:ℝ) (-1) 2)).bijective.comp hP

/-- The normalized formula is EXACTLY the existing actual native inverse,
with the original A-lambda*J sign, on the ENTIRE H-minus-one base. -/
theorem singularHillResolventToH1_eq_normalized (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2) (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (hS : ‖hillHalfSandwich r q z‖ ≤ 1/2) :
    singularHillResolventToH1 (hillHalfPotentialBase r hr1 q) z = -hillNormalizedResolventToH1 r q z := by
  have hmem := mem_singularHillResolventSet_of_halfSandwich_small r hr hr1 q n hn hlog z hz hS
  apply ContinuousLinearMap.ext
  intro F
  have hright := hillNormalizedResolventToH1_right r hr hr1 q n hn hlog z hz hS F
  change z • singularHillDomainInclusion (hillNormalizedResolventToH1 r q z F)-
    singularHillOperator (hillHalfPotentialBase r hr1 q) (hillNormalizedResolventToH1 r q z F) = F at hright
  have hneg : singularHillOperator (hillHalfPotentialBase r hr1 q) (hillNormalizedResolventToH1 r q z F)-
      z • singularHillDomainInclusion (hillNormalizedResolventToH1 r q z F) = -F := by
    simpa only [neg_sub] using congrArg Neg.neg hright
  have hleft := singularHillResolventToH1_left (hillHalfPotentialBase r hr1 q) z hmem
    (hillNormalizedResolventToH1 r q z F)
  rw [hneg,map_neg] at hleft
  change singularHillResolventToH1 (hillHalfPotentialBase r hr1 q) z F = -hillNormalizedResolventToH1 r q z F
  simpa only [neg_neg] using congrArg Neg.neg hleft

end NLS.KdV
