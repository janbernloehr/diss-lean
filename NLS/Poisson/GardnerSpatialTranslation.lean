import NLS.Poisson.GardnerHamiltonianDirection
import NLS.SequenceSpaces.WeightedSpatialTranslationDerivative

/-! The ACTUAL scalar Gardner Poisson structure is preserved by physical
spatial translation. Full Hminus-one cotangents and their unique H1
representatives transform with opposite translation, retaining2*pi. -/
noncomputable section
open Complex Filter Topology
namespace NLS.Poisson

/-- The physical Gardner derivative commutes with every Fourier translation. -/
theorem gardnerDerivative_spatialTranslation (c t : ℝ)
    (a : WeightedCoeff (Weight.sobolev 1) 2) :
    gardnerDerivative (WeightedCoeff.spatialTranslation (Weight.sobolev 1) c t a)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t (gardnerDerivative a) := by
  apply Subtype.ext
  funext k
  rw [gardnerDerivative_apply,WeightedCoeff.spatialTranslation_apply,
    WeightedCoeff.spatialTranslation_apply,gardnerDerivative_apply]
  ring

/-- Opposite Fourier indices cancel the exact translation phases. -/
theorem gardnerBivector_spatialTranslation (c t : ℝ)
    (a b : WeightedCoeff (Weight.sobolev 1) 2) :
    gardnerBivector (WeightedCoeff.spatialTranslation (Weight.sobolev 1) c t a)
      (WeightedCoeff.spatialTranslation (Weight.sobolev 1) c t b)=gardnerBivector a b := by
  rw [gardnerBivector_eq_tsum,gardnerBivector_eq_tsum]
  apply tsum_congr
  intro k
  rw [WeightedCoeff.spatialTranslation_apply,WeightedCoeff.spatialTranslation_apply]
  have he := NLS.spatialTranslation_phase_add c t k (-k)
  simp only [add_neg_cancel,Int.cast_zero,mul_zero,Complex.ofReal_zero,zero_mul,exp_zero] at he
  calc
    _=(exp ((t*(c*k):ℝ)*I)*exp ((t*(c*((-k:ℤ):ℝ)):ℝ)*I))*
        (a.val k*((2*Real.pi:ℂ)*I*(-k)*b.val (-k))) := by ring
    _=_ := by rw [← he,one_mul]

/-- The full cotangent pullback is exactly the opposite H1 translation. -/
theorem hminusCotangentCLM_comp_spatialTranslation (c t : ℝ)
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    hminusCotangentCLM (L.comp
      (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t).toContinuousLinearEquiv.toContinuousLinearMap)=
      WeightedCoeff.spatialTranslation (Weight.sobolev 1) c (-t) (hminusCotangentCLM L) := by
  apply Subtype.ext
  funext k
  have hu : WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t
      (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1))=
      exp ((t*(c*((-k:ℤ):ℝ)):ℝ)*I) •
        WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1) := by
    apply Subtype.ext
    funext j
    change (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t
      (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1))).val j=
        exp ((t*(c*((-k:ℤ):ℝ)):ℝ)*I)*(WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1)).val j
    rw [WeightedCoeff.spatialTranslation_apply]
    change exp ((t*(c*j):ℝ)*I)*(Finsupp.single (-k) (1:ℂ)) j=
      exp ((t*(c*((-k:ℤ):ℝ)):ℝ)*I)*(Finsupp.single (-k) (1:ℂ)) j
    by_cases hj : -k=j
    · rw [hj]
    · simp [hj]
  rw [hminusCotangentCLM_apply,ContinuousLinearMap.comp_apply]
  change L (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t
    (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1)))=
      (WeightedCoeff.spatialTranslation (Weight.sobolev 1) c (-t) (hminusCotangentCLM L)).val k
  rw [hu,map_smul,
    WeightedCoeff.spatialTranslation_apply,hminusCotangentCLM_apply]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

theorem gardnerHamiltonianDirection_comp_spatialTranslation (c t : ℝ)
    (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerHamiltonianDirection (L.comp
      (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t).toContinuousLinearEquiv.toContinuousLinearMap)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c (-t) (gardnerHamiltonianDirection L) := by
  change gardnerDerivative (hminusCotangentCLM _)= _
  rw [hminusCotangentCLM_comp_spatialTranslation,gardnerDerivative_spatialTranslation]
  rfl

/-- Exact invariance of the ACTUAL full-dual scalar Gardner Poisson tensor. -/
theorem gardnerCotangentBivector_comp_spatialTranslation (c t : ℝ)
    (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ) :
    gardnerCotangentBivector
      (L.comp (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t).toContinuousLinearEquiv.toContinuousLinearMap)
      (M.comp (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t).toContinuousLinearEquiv.toContinuousLinearMap)=
      gardnerCotangentBivector L M := by
  change gardnerBivector (hminusCotangentCLM _) (hminusCotangentCLM _)= _
  rw [hminusCotangentCLM_comp_spatialTranslation,hminusCotangentCLM_comp_spatialTranslation,
    gardnerBivector_spatialTranslation]
  rfl

/-- A genuine translation-invariance germ transports the ACTUAL gradient.
Differentiability is needed at the translated point; the germ supplies it
at the original point. No invariance is inferred from one equal value. -/
theorem hminusScalarGradient_spatialTranslation_of_germ
    (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (c t : ℝ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hF : DifferentiableAt ℂ F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t q))
    (hinv : (fun a => F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t a)) =ᶠ[𝓝 q] F) :
    hminusScalarGradient F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t q)=
      WeightedCoeff.spatialTranslation (Weight.sobolev 1) c t (hminusScalarGradient F q) := by
  let T : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-1)) 2 := (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t).toContinuousLinearEquiv.toContinuousLinearMap
  have he : (fderiv ℂ F (T q)).comp T=fderiv ℂ F q := by
    have hd := hF.hasFDerivAt.comp q T.hasFDerivAt
    exact hd.fderiv.symm.trans hinv.fderiv_eq
  have hc := congrArg hminusCotangentCLM he
  rw [hminusCotangentCLM_comp_spatialTranslation] at hc
  have ht := congrArg (WeightedCoeff.spatialTranslation (Weight.sobolev 1) c t) hc
  rw [WeightedCoeff.spatialTranslation_add,add_neg_cancel,WeightedCoeff.spatialTranslation_zero] at ht
  exact ht

/-- The ACTUAL Hamiltonian vector is spatially covariant whenever its
functional has the proved local invariance germ. -/
theorem gardnerHamiltonianVector_spatialTranslation_of_germ
    (F : WeightedCoeff (Weight.sobolev (-1)) 2 → ℂ) (c t : ℝ)
    (q : WeightedCoeff (Weight.sobolev (-1)) 2)
    (hF : DifferentiableAt ℂ F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t q))
    (hinv : (fun a => F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t a)) =ᶠ[𝓝 q] F) :
    gardnerHamiltonianVector F (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t q)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) c t (gardnerHamiltonianVector F q) := by
  change gardnerDerivative (hminusScalarGradient F _)= _
  rw [hminusScalarGradient_spatialTranslation_of_germ F c t q hF hinv,gardnerDerivative_spatialTranslation]
  rfl

end NLS.Poisson
