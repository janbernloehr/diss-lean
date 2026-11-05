import NLS.MKdV.MiuraNativeActionVelocityGardner
import NLS.Poisson.SobolevGardnerGradient

/-! # Native action-flow chain rules for independent H¹ functionals

An actual H¹ functional with a physical H¹ Hilbert gradient can be
 differentiated along every native positive Sobolev action flow. Its
 derivative is evaluated on the original physical Gardner action field.
 No extension of the functional to L² is required.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem hasDerivAt_independent_functional_miuraActionFlow (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (F : ScalarDomain 2 → ℂ)
    (P : SobolevGardnerGradientAt F (hierarchySobolevToScalarDomain s hs a.val)) :
    HasDerivAt (fun t => F (hierarchySobolevToScalarDomain s hs
      (miuraActionFlow s a.val (fun j => a.property j) n t)))
      (reflectedHilbertPairing (scalarInclusion P.gradient)
        (l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val))) 0 := by
  let H := hierarchySobolevToScalarDomain s hs
  have hd := (H.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (hasDerivAt_miuraActionFlow_native_zero s hs a n hn)
  have hzero := miuraActionFlow_zero s a.val (fun j => a.property j) n
  have hp : HasFDerivAt F
      (((reflectedHilbertPairing (scalarInclusion P.gradient)).comp scalarInclusion).restrictScalars ℝ)
      (H (miuraActionFlow s a.val (fun j => a.property j) n 0)) := by
    simpa only [hzero] using P.hasFDerivAt.restrictScalars ℝ
  have he := hp.comp_hasDerivAt 0 hd
  change HasDerivAt (fun t => F (H (miuraActionFlow s a.val (fun j => a.property j) n t)))
    (reflectedHilbertPairing (scalarInclusion P.gradient)
      (scalarInclusion (H (miuraNativeActionVelocity s a n)))) 0 at he
  have hv := scalarInclusion_hierarchySobolevToScalarDomain s hs (miuraNativeActionVelocity s a n)
  rw [miuraNativeActionVelocity_L2_Gardner s hs a n hn] at hv
  simpa only [H,hv] using he

end NLS.MKdV
