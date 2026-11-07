import NLS.KdV.HminusOneMiuraIsospectral
import NLS.ZakharovShabat.SourceHilbertIsospectralConnected

/-!
# Compact real scalar Miura lifts in an actual Dirac isospectral set

The real diagonal source map is a closed embedding. The verified actual
Hilbert isospectral compactness theorem therefore gives compactness of its
real scalar preimage, and of the literal shifted rough Miura image.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.KdV
open NLS.ZakharovShabat

/-- The scalar reality constraint is closed in the original unit-period L2 norm. -/
theorem isClosed_periodOneRealL2_locus :
    IsClosed {u : Coeff 2 | ∀ k : ℤ, u (-k) = conj (u k)} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-k)).continuous
    (Complex.continuous_conj.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous)

/-- Real scalar diagonal lifts form a closed original source subspace. -/
theorem isClosedEmbedding_hillMiuraRealSource :
    Topology.IsClosedEmbedding hillMiuraRealSource := by
  let r : CoeffPair 2 → Coeff 2 := fun φ => (CoeffPair.toMax 2 φ).1
  have hr : Continuous r := continuous_fst.comp (CoeffPair.toMax 2).continuous
  have hl : Function.LeftInverse r hillMiuraDiagonal := fun u => hillMiuraDiagonal_fst u
  have hd := hl.isClosedEmbedding hr hillMiuraDiagonal.continuous
  have he := hd.comp isClosed_periodOneRealL2_locus.isClosedEmbedding_subtypeVal
  apply Topology.IsClosedEmbedding.of_comp Topology.IsEmbedding.subtypeVal
  exact he

/-- The real scalar lifts in one ACTUAL original Dirac isospectral set are
compact in the original scalar L2 topology, including all algebraic counts. -/
theorem isCompact_hillMiuraRealSource_isospectral_preimage (u : PeriodOneRealL2) :
    IsCompact (hillMiuraRealSource ⁻¹'
      sourceIsospectralSet (by norm_num) (hillMiuraRealSource u)) :=
  isClosedEmbedding_hillMiuraRealSource.isCompact_preimage
    (sourceHilbertIsospectralSet_compact_connected (hillMiuraRealSource u)).1

/-- Literal shifted rough Miura images of all real diagonal lifts in an
actual Dirac isospectral set are compact in the full unit-period H-minus-one norm. -/
theorem isCompact_shiftedMiura_image_of_dirac_isospectral (u : PeriodOneRealL2) (c : ℂ) :
    IsCompact ((fun v : PeriodOneRealL2 => periodOneMiura v.val-
      periodOneL2Inclusion (lp.single 2 0 c)) ''
        (hillMiuraRealSource ⁻¹' sourceIsospectralSet (by norm_num) (hillMiuraRealSource u))) :=
  (isCompact_hillMiuraRealSource_isospectral_preimage u).image
    ((continuous_periodOneMiura.comp continuous_subtype_val).sub continuous_const)

end NLS.KdV
