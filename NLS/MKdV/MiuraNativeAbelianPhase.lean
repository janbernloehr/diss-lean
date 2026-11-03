import NLS.MKdV.MiuraFullAbelianPhase
import NLS.MKdV.MiuraNativeNLSAngularDomain
import NLS.MKdV.MiuraThetaActionDirection

/-! # Independent full Abelian phase in the native Sobolev source spaces

The bounded phase and its continuity domain are exactly those required
by full phase-product descent. Its opposite physical action-flow law
is not assumed here and still has to be proved.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraNativeH1Profile_real (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    ∀ j, (hierarchySobolevToScalarDomain s hs a.val).val j =
      conj ((hierarchySobolevToScalarDomain s hs a.val).val (-j)) := by
  intro j
  simpa only [hierarchySobolevToScalarDomain_apply] using (fun j => a.property j) j

def miuraNativeFullAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) : ℂ :=
  miuraFullAbelianPhase (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) n hn

theorem miuraNativeH1_action_zero_iff_angular_zero (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) :
    miuraMKdVAction (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) n = 0 ↔
      miuraNativeNLSAngularCoordinate s n a = 0 := by
  rw [← miuraL2Action_eq_physical _ (miuraNativeH1Profile_real s hs a) n hn,
    scalarInclusion_hierarchySobolevToScalarDomain s hs a.val]
  exact (miuraNativeNLSAngularCoordinate_zero_iff_physical_action_zero s n hn a).symm

theorem norm_miuraNativeFullAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) (hangle : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    ‖miuraNativeFullAbelianPhase s hs n hn a‖ = 1 :=
  norm_miuraFullAbelianPhase _ _ n hn
    (fun h => hangle ((miuraNativeH1_action_zero_iff_angular_zero s hs n hn a).mp h))

theorem miuraNativeFullAbelianPhase_closed (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) (hangle : miuraNativeNLSAngularCoordinate s n a = 0) :
    miuraNativeFullAbelianPhase s hs n hn a = 0 :=
  miuraFullAbelianPhase_closed _ _ n hn ((miuraNativeH1_action_zero_iff_angular_zero s hs n hn a).mpr hangle)

theorem norm_miuraNativeFullAbelianPhase_le_one (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource s) : ‖miuraNativeFullAbelianPhase s hs n hn a‖ ≤ 1 :=
  norm_miuraFullAbelianPhase_le_one _ _ n hn

theorem continuousOn_miuraNativeFullAbelianPhase (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (miuraNativeFullAbelianPhase s hs n hn) {a | miuraNativeNLSAngularCoordinate s n a ≠ 0} := by
  intro a ha
  have hA : Continuous (fun b : MiuraRealSobolevSource s => hierarchySobolevToScalarDomain s hs b.val) :=
    (hierarchySobolevToScalarDomain s hs).continuous.comp continuous_subtype_val
  exact (continuousAt_miuraFullAbelianPhase_along_real_family _ hA (miuraNativeH1Profile_real s hs) n hn a
    (fun h => ha ((miuraNativeH1_action_zero_iff_angular_zero s hs n hn a).mp h))).continuousWithinAt

end NLS.MKdV
