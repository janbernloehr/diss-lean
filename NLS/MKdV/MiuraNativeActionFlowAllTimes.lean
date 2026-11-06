import NLS.MKdV.MiuraNativeActionVelocityGardner
import NLS.MKdV.MiuraNormalizedCartesianHomeomorph
import NLS.Poisson.SobolevGardnerGradient

/-! # Native Sobolev action-flow derivatives at every real time

The actual group law translates the native derivative at zero. Chain
rules for H¹ functionals evaluate on the original physical Gardner field
at each point of the complete orbit.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem hasDerivAt_miuraActionFlow_native (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    HasDerivAt (miuraActionFlow s a.val (fun j => a.property j) n)
      (miuraNativeActionVelocity s (miuraNativeRealActionFlow s a n t) n) t := by
  let b := miuraNativeRealActionFlow s a n t
  have hv := hasDerivAt_miuraActionFlow_native_zero s hs b n hn
  have hv' : HasDerivAt (miuraActionFlow s b.val (fun j => b.property j) n)
      (miuraNativeActionVelocity s b n) (t-t) := by simpa only [sub_self] using hv
  have ht : HasDerivAt (fun r : ℝ => r-t) 1 t := by
    simpa only [id_eq] using (hasDerivAt_id t).sub_const t
  have hd := hv'.scomp (h := fun r : ℝ => r-t) t ht
  have he : (fun r : ℝ => miuraActionFlow s b.val (fun j => b.property j) n (r-t)) =
      miuraActionFlow s a.val (fun j => a.property j) n := by
    funext r
    change miuraActionFlow s (miuraActionFlow s a.val (fun j => a.property j) n t)
      (miuraActionFlow_real s a.val (fun j => a.property j) n t) n (r-t) = _
    rw [miuraActionFlow_add]
    congr 1
    ring
  change HasDerivAt (fun r : ℝ => miuraActionFlow s b.val (fun j => b.property j) n (r-t))
    ((1 : ℝ) • miuraNativeActionVelocity s b n) t at hd
  rw [he,one_smul] at hd
  exact hd

theorem hasDerivAt_independent_functional_miuraActionFlow_allTimes (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (F : ScalarDomain 2 → ℂ)
    (P : SobolevGardnerGradientAt F
      (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a n t).val)) :
    HasDerivAt (fun r => F (hierarchySobolevToScalarDomain s hs
      (miuraActionFlow s a.val (fun j => a.property j) n r)))
      (reflectedHilbertPairing (scalarInclusion P.gradient)
        (l2GardnerDirection (miuraL2Action n)
          (hierarchySobolevJetL2 s 0 (Nat.zero_le _) (miuraNativeRealActionFlow s a n t).val))) t := by
  let H := hierarchySobolevToScalarDomain s hs
  have hd := (H.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (hasDerivAt_miuraActionFlow_native s hs a n hn t)
  have he := (P.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hd
  change HasDerivAt (fun r => F (H (miuraActionFlow s a.val (fun j => a.property j) n r)))
    (reflectedHilbertPairing (scalarInclusion P.gradient)
      (scalarInclusion (H (miuraNativeActionVelocity s (miuraNativeRealActionFlow s a n t) n)))) t at he
  have hv := scalarInclusion_hierarchySobolevToScalarDomain s hs
    (miuraNativeActionVelocity s (miuraNativeRealActionFlow s a n t) n)
  rw [miuraNativeActionVelocity_L2_Gardner s hs _ n hn] at hv
  simpa only [H,hv] using he

end NLS.MKdV
