import NLS.MKdV.MiuraL2CartesianActions
import NLS.MKdV.MiuraL2ActionProperness

/-! # Properness of the full native Cartesian and signed-mean map

The quadratic native radius map recovers every physical action. The
already proved original L² action properness therefore gives properness
of the actual full Cartesian map with signed mean. No inverse chart or
Gardner canonicity is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- Exact positive-coordinate evaluation of the full native map. -/
theorem miuraL2CartesianSequence_positive
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℕ) (hn : 1 ≤ n) :
    ((miuraL2CartesianSequence a).1.val n,(miuraL2CartesianSequence a).2.val n) =
      miuraL2CartesianCoordinates n a := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2CartesianSequence_domain
  have hnZ : (0 : ℤ) < n := by omega
  simpa only [miuraL2CartesianCoefficient,if_pos hnZ,Int.toNat_natCast] using hcoord a (hreal ha) n

/-- Nonpositive slots encode no physical Cartesian variables. -/
theorem miuraL2CartesianSequence_nonpositive
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) (n : ℤ) (hn : ¬0 < n) :
    ((miuraL2CartesianSequence a).1.val n,(miuraL2CartesianSequence a).2.val n) = 0 := by
  obtain ⟨U,_,hreal,_,hcoord⟩ := exists_miuraL2CartesianSequence_domain
  simpa only [miuraL2CartesianCoefficient,if_neg hn] using hcoord a (hreal ha) n

def miuraL2CartesianMeanMap (a : Coeff 2) : MiuraL2CartesianTarget × ℂ :=
  (miuraL2CartesianSequence a,a 0)

theorem analyticAt_miuraL2CartesianMeanMap
    (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) : AnalyticAt ℂ miuraL2CartesianMeanMap a :=
  (analyticAt_miuraL2CartesianSequence a ha).prod ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).analyticAt a)

def miuraRealL2CartesianMeanMap (a : MiuraRealL2) : MiuraL2CartesianTarget × ℂ :=
  miuraL2CartesianMeanMap a.val

theorem continuous_miuraRealL2CartesianMeanMap : Continuous miuraRealL2CartesianMeanMap := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (analyticAt_miuraL2CartesianMeanMap a.val a.property).continuousAt.comp
    continuous_subtype_val.continuousAt

def miuraCartesianActionMeanProjection (z : MiuraL2CartesianTarget × ℂ) :
    WeightedCoeff (Weight.sobolev 1) 1 × ℂ := (miuraL2CartesianActions z.1,z.2)

theorem continuous_miuraCartesianActionMeanProjection : Continuous miuraCartesianActionMeanProjection :=
  (continuous_miuraL2CartesianActions.comp continuous_fst).prodMk continuous_snd

/-- Every physical action and the literal signed mean are recovered
continuously from the full native Cartesian map. -/
theorem miuraCartesianActionMeanProjection_map (a : MiuraRealL2) :
    miuraCartesianActionMeanProjection (miuraRealL2CartesianMeanMap a) = miuraRealL2ActionMeanMap a :=
  Prod.ext (miuraL2CartesianActions_sequence_eq a.val a.property) rfl

/-- Compact full native Cartesian data and signed mean have compact
preimages in original physical L², including every closed-action stratum. -/
theorem isProperMap_miuraRealL2CartesianMeanMap : IsProperMap miuraRealL2CartesianMeanMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨continuous_miuraRealL2CartesianMeanMap,?_⟩
  intro K hK
  have hPK := hK.image continuous_miuraCartesianActionMeanProjection
  have hAK := (isProperMap_iff_isCompact_preimage.mp isProperMap_miuraRealL2ActionMeanMap).2 hPK
  apply hAK.of_isClosed_subset (hK.isClosed.preimage continuous_miuraRealL2CartesianMeanMap)
  intro a ha
  exact ⟨miuraRealL2CartesianMeanMap a,ha,miuraCartesianActionMeanProjection_map a⟩

/-- Every complete native Cartesian and signed-mean fiber is compact. -/
theorem isCompact_miuraRealL2CartesianMeanFiber (z : MiuraL2CartesianTarget × ℂ) :
    IsCompact {a : MiuraRealL2 | miuraRealL2CartesianMeanMap a = z} := by
  have hz : IsCompact ({z} : Set (MiuraL2CartesianTarget × ℂ)) := isCompact_singleton
  exact (isProperMap_iff_isCompact_preimage.mp isProperMap_miuraRealL2CartesianMeanMap).2 hz

end NLS.MKdV
