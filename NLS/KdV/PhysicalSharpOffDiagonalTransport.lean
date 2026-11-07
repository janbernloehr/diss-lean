import NLS.KdV.PhysicalSobolevLpFrequencyChart
import NLS.KdV.PhysicalOffDiagonalFrequency
import NLS.ZakharovShabat.SourceSharpOffDiagonalDecay
import NLS.SequenceSpaces.PositiveFrequencyDecayNormalization
import NLS.ComplexAnalysis.CommonPullbackDomain

/-! Sharp decay transports through a native parameterization of the SAME
actual physical Miura chart. Chart and inclusion remain opaque. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.PhysicalMiuraFrequencyChart

theorem exists_sharp_offDiagonal_decay_of_native_parameterization
    (B : PhysicalMiuraFrequencyChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots)
    (t : ℝ) (ht : 0≤t) (ht1 : t≤2/3)
    (J : WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] PeriodOneHminusOne)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqB : J q∈B.domain)
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V) (hqV : q∈V)
    (η : WeightedCoeff (Weight.sobolev (t-1)) 2 → CoeffPair 2) (hη : AnalyticOnNhd ℂ η V)
    (hηqr : η q∈realTypeSourceLocus 2)
    (he : ∀ a∈V, normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht) (η a)=
      hillMiuraDiagonal (B.psi.miura.lift (J a))) :
    ∃ T : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen T ∧ q∈T ∧
      T⊆J ⁻¹' B.domain ∧
      ∃ K : ℝ, 0≤K ∧
        (∀ a∈T, ∀ n : ℕ+, Weight.sobolev (3*t-1) (n : ℤ)*
          ‖B.offDiagonalCorrection n (J a)‖≤K) ∧
        (t<2/3 → ∀ a∈T,
          Tendsto (fun n : ℕ => Weight.sobolev (3*t-1) ((n+1 : ℕ) : ℤ)*
            ‖B.offDiagonalCorrection ⟨n+1,by omega⟩ (J a)‖)
            atTop (𝓝 0)) := by
  let L := normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht)
  obtain ⟨Ur,_hUr,hrealUr,_hUrV,hdecay⟩ := B.atlas.exists_sharp_offDiagonal_secondMoment_decay
    t ht ht1 H.angular_extension B.psi.family.domain_open B.psi.family.real_subset
  obtain ⟨S,hS,hηS,_hSUr,K,hK,hb,hd⟩ := hdecay (η q) (hrealUr hηqr)
  obtain ⟨T,hT,hqT,hTV,hTS,hTB⟩ := exists_open_common_pullback_domain V hV q hqV
    η hη.continuousOn S hS hηS J J.continuous B.domain B.domain_open hqB
  have hraw (a : WeightedCoeff (Weight.sobolev (t-1)) 2) (haT : a∈T) (n : ℕ+) :
      B.offDiagonalCorrection n (J a)=(-12 : ℂ)*
        (B.atlas.weightedSecondMomentSum (n : ℤ) (L (η a))-(n : ℂ)*
          (B.atlas.moment (n : ℤ) (n : ℤ) 2 (L (η a))-B.atlas.moment (n : ℤ) (-(n : ℤ)) 2 (L (η a)))) := by
    change (-12 : ℂ)*(B.atlas.weightedSecondMomentSum (n : ℤ) (hillMiuraDiagonal (B.psi.miura.lift (J a)))-(n : ℂ)*
      (B.atlas.moment (n : ℤ) (n : ℤ) 2 (hillMiuraDiagonal (B.psi.miura.lift (J a)))-B.atlas.moment (n : ℤ) (-(n : ℤ)) 2 (hillMiuraDiagonal (B.psi.miura.lift (J a)))))=_
    rw [he a (hTV haT)]
  refine ⟨T,hT,hqT,hTB,12*K,mul_nonneg (by norm_num) hK,?_,?_⟩
  · intro a haT n
    let d : ℤ → ℂ := fun j => B.atlas.weightedSecondMomentSum j (L (η a))-(j : ℂ)*
      (B.atlas.moment j j 2 (L (η a))-B.atlas.moment j (-j) 2 (L (η a)))
    have hcal (j : ℕ+) : B.offDiagonalCorrection j (J a)=(-12 : ℂ)*d (j : ℤ) := by
      simpa only [d,Int.cast_natCast] using hraw a haT j
    have hb' : ∀ j : ℤ, Weight.sobolev (3*t-1) j*‖d j‖≤K := hb (η a) (hTS a haT)
    have H := Coeff.scaled_positive_frequency_bound (Weight.sobolev (3*t-1)) d
      (fun j => B.offDiagonalCorrection j (J a)) (-12) hcal K hb' n
    norm_num only [norm_neg,Complex.norm_ofNat] at H
    exact H
  · intro ht2 a haT
    let d : ℤ → ℂ := fun j => B.atlas.weightedSecondMomentSum j (L (η a))-(j : ℂ)*
      (B.atlas.moment j j 2 (L (η a))-B.atlas.moment j (-j) 2 (L (η a)))
    have hcal (j : ℕ+) : B.offDiagonalCorrection j (J a)=(-12 : ℂ)*d (j : ℤ) := by
      simpa only [d,Int.cast_natCast] using hraw a haT j
    have hd' : Tendsto (fun j : ℕ => Weight.sobolev (3*t-1) (j : ℤ)*‖d (j : ℤ)‖) atTop (𝓝 0) := by
      simpa only [d,Int.cast_natCast] using hd ht2 (η a) (hTS a haT)
    exact Coeff.tendsto_scaled_positive_frequency (Weight.sobolev (3*t-1)) d
      (fun j => B.offDiagonalCorrection j (J a)) (-12) hcal hd'

end NLS.KdV.PhysicalMiuraFrequencyChart
