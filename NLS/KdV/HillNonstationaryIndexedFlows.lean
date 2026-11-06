import NLS.KdV.HillOwnDirichletNumerator
import NLS.KdV.HillIndexedFlowCartesianDynamics
import NLS.KdV.HillOwnAmplitudeAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem physical_gap_open_iff_action_pos
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0 ↔
      0<hillRealGapIntegral q.val q.property.1 q.property.2 n 0 := by
  rw [hillRealGapIntegral_pos_iff q.val q.property.1 q.property.2 n hn]
  have hle := monotone_hillRealLabels q.val q.property.1 q.property.2 (show 2*n-1≤2*n by omega)
  constructor
  · intro hne
    apply lt_of_le_of_ne hle
    intro he
    exact hne (by simp only [hillRealGapHalfLength,he,sub_self,zero_div])
  · intro hlt hz
    dsimp only [hillRealGapHalfLength] at hz
    linarith

/-- The open or collapsed status of every labelled gap is preserved throughout
an actual indexed spectral integral curve. -/
theorem hillRealGapHalfLength_zero_iff_on_indexed_integralCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) :
    hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n=0 ↔
      hillRealGapHalfLength (γ v).val (γ v).property.1 (γ v).property.2 n=0 := by
  have hI := hillRealGapIntegral_eq_on_indexed_integralCurve n k hn hk 0 γ a b hγ u v hu hv
  have hU := physical_gap_open_iff_action_pos (⟨(γ u).val,(γ u).property⟩ : RealPeriodOneHillPotential) n hn
  have hV := physical_gap_open_iff_action_pos (⟨(γ v).val,(γ v).property⟩ : RealPeriodOneHillPotential) n hn
  have he : (hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n≠0) ↔
      (hillRealGapHalfLength (γ v).val (γ v).property.1 (γ v).property.2 n≠0) := by
    rw [hU,hV,hI]
  exact not_iff_not.mp he

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- An actual indexed spectral source cannot vanish when its own physical gap
is open, including when its Dirichlet label is at an endpoint. -/
theorem hillIndexedDiscriminantHamiltonianSource_ne_zero_of_open_gap
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    hillIndexedDiscriminantHamiltonianSource q n hn≠0 := by
  intro hz
  obtain ⟨Z,_,_,hD⟩ := exists_hillSpectralCartesian_indexedSource_variations
    q.val q.property.1 q.property.2 h0q h0r n hn
  have he := hD n hn
  rw [hz,map_zero,map_zero] at he
  have hZ : hillSpectralCartesian q.val q.property.1 q.property.2 n hn≠0 :=
    mt (hillSpectralCartesian_eq_zero_iff q.val q.property.1 q.property.2 n hn).mp hgap
  have hΨ := hillAbelianSelectedGlobalPsi_own_dirichlet_ne_zero q n hn
  exact (mul_ne_zero (mul_ne_zero I_ne_zero (div_ne_zero hΨ (by norm_num))) hZ) he.symm

/-- The genuine real Banach-space indexed field is nonzero at every source with
an open selected gap. -/
theorem hillRealIndexedDiscriminantField_ne_zero_of_open_gap
    (q : hillRealSourceSubmodule) (n : ℕ) (hn : 1≤n)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n≠0) :
    hillRealIndexedDiscriminantField n hn q≠0 := by
  intro hz
  have he := congrArg Subtype.val hz
  exact hillIndexedDiscriminantHamiltonianSource_ne_zero_of_open_gap h0q h0r
    ⟨q.val,q.property⟩ n hn hgap he

/-- At every point whose selected gap is open, the actual indexed spectral
trajectory has nonzero velocity. -/
theorem deriv_hillIndexedIntegralCurve_ne_zero_of_open_gap
    (n : ℕ) (hn : 1≤n) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t)
    (hgap : hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 n≠0) :
    deriv γ t≠0 := by
  rw [hγ.deriv]
  exact hillRealIndexedDiscriminantField_ne_zero_of_open_gap h0q h0r (γ t) n hn hgap

/-- An initially open selected gap makes the actual spectral trajectory
nonstationary at every point of its interval, even at terminal endpoints. -/
theorem deriv_hillIndexedIntegralCurve_ne_zero_on_interval
    (n : ℕ) (hn : 1≤n) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t)
    (u : ℝ) (hu : u∈Ioo a b)
    (hgap : hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n≠0) :
    ∀ t∈Ioo a b, deriv γ t≠0 := by
  intro t ht
  apply deriv_hillIndexedIntegralCurve_ne_zero_of_open_gap h0q h0r n hn γ t (hγ t ht)
  exact mt (hillRealGapHalfLength_zero_iff_on_indexed_integralCurve n n hn hn γ a b hγ t u ht hu).mp hgap

end NLS.KdV
