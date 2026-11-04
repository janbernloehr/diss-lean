import NLS.KdV.HillIsospectralAbelianData
import NLS.MKdV.MiuraGapIdentification
import NLS.MKdV.MiuraHillDirichletPositivity
import NLS.MKdV.MiuraNativeAbelianPhase
import NLS.MKdV.MiuraActionFlowInvariants

/-! # Independent Abelian data along the original complete physical flows

The actual source isospectrality fixes every original Hill periodic label.
Period uniqueness therefore fixes the independently normalized differential
and its primitive on every native integer Sobolev action orbit.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraHillLabels_eq_of_isospectral (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (b : ScalarDomain 2)
    (hb : ∀ j, b.val j = conj (b.val (-j)))
    (hi : realDiagonalH1Source b hb ∈ sourceIsospectralSet (by simp) (realDiagonalH1Source a ha)) :
    miuraHillLabels b hb = miuraHillLabels a ha := by
  obtain ⟨hL,hR⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
    (periodOnePotential (realDiagonalH1Source b hb).val)
    (periodOnePotential (realDiagonalH1Source a ha).val) (periodOnePotential_mem _)
    (periodOnePotential_mem _) hi.1 hi.2
  change miuraNLSLeft b = miuraNLSLeft a at hL
  change miuraNLSRight b = miuraNLSRight a at hR
  funext j
  rw [miuraHillLabels_eq_squaredNLS b hb,miuraHillLabels_eq_squaredNLS a ha]
  simp only [miuraSquaredNLS,miuraPositiveFrequency,hL,hR]

theorem miuraNativeH1Source_eq_originalSource (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) :
    realDiagonalH1Source (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) =
      miuraActionInitialSource s a.val (fun j => a.property j) := by
  apply Subtype.ext
  change sobolevSourceInclusion (_,_) = (miuraActionInitialSource s a.val (fun j => a.property j)).val
  rw [miuraActionInitialSource_L2_diagonal,← scalarInclusion_hierarchySobolevToScalarDomain s hs a.val,
    scalarL2Diagonal_scalarInclusion]

theorem miuraNativeH1Source_actionFlow_isospectral (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) (t : ℝ) :
    realDiagonalH1Source (hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val)
      (miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)) ∈
        sourceIsospectralSet (by simp)
          (realDiagonalH1Source (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)) := by
  rw [miuraNativeH1Source_eq_originalSource,miuraNativeH1Source_eq_originalSource]
  exact miuraActionFlow_isospectral s a.val (fun k => a.property k) j t

theorem miuraNativeHillLabels_actionFlow (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j : ℕ) (t : ℝ) :
    let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
    let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
    miuraHillLabels b hb =
      miuraHillLabels (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a) :=
  miuraHillLabels_eq_of_isospectral _ _ _ _ (miuraNativeH1Source_actionFlow_isospectral s hs a j t)

theorem miuraNativeAbelianPsi_actionFlow (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
    let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
    let q := realSobolevMiuraHillPotential b hb
    let r := realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn =
      hillAbelianSelectedGlobalPsi r.val r.property.1 r.property.2 n hn :=
by
  dsimp only
  apply hillAbelianSelectedGlobalPsi_eq_of_labels
  exact miuraNativeHillLabels_actionFlow s hs a j t

theorem miuraNativeAbelianPrimitive_actionFlow (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (j n k : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let b := hierarchySobolevToScalarDomain s hs (miuraNativeRealActionFlow s a j t).val
    let hb := miuraNativeH1Profile_real s hs (miuraNativeRealActionFlow s a j t)
    let q := realSobolevMiuraHillPotential b hb
    let r := realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)
    hillRegularAbelianPrimitive q.val q.property.1 q.property.2 n hn k =
      hillRegularAbelianPrimitive r.val r.property.1 r.property.2 n hn k :=
by
  dsimp only
  apply hillRegularAbelianPrimitive_eq_of_labels
  exact miuraNativeHillLabels_actionFlow s hs a j t

end NLS.MKdV
