import NLS.MKdV.MiuraMassFrequencyComparison
import NLS.MKdV.MiuraNativeMassFrequency

/-! # Theorem 3 at m=1 on its full original real L² domain

The NLS S_2 frequency is the unique continuous real-L² extension of the
actual original angle-S_2 bracket on H¹ open-angle inputs. The independent
K_1 derivative is intrinsic for every global physical mass action normal
form. Their equality has positive period-one sign, without the printed
parity factor. The remaining m>=2 comparison is not asserted here.
-/
noncomputable section
open Set Complex NLS.MKdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

/-- One constructed original NLS angle family certifies the frequency
identification and its unique continuous extension simultaneously at all
signed indices, including every closed-gap real L² profile. -/
theorem theorem3_m1_original_NLS_frequency_certificate :
    ∃ A : SourceMomentumFrequencyFamily, ∀ n : ℤ,
      IsSourceMomentumFrequencyExtension A n (fun φ => sourceMomentumFrequency n φ.val) ∧
        ∀ f : realTypeSourceSubmodule 2 → ℂ, IsSourceMomentumFrequencyExtension A n f →
          f = (fun φ => sourceMomentumFrequency n φ.val) := by
  obtain ⟨A⟩ := nonempty_sourceMomentumFrequencyFamily
  exact ⟨A,fun n => ⟨sourceMomentumFrequency_extension A n,
    fun f hf => sourceMomentumFrequency_extension_unique A n f hf⟩⟩

/-- Corrected Theorem 3 for m=1: on every original real L² profile,
the original NLS S_2 frequency equals the independent physical K_1 action
derivative for any global mass normal form, including closed actions. -/
theorem theorem3_m1_corrected (n : ℕ) (hn : 1 ≤ n) (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (D : MiuraL2MassActionData) :
    sourceMomentumFrequency (n : ℤ) (scalarL2Diagonal a) = D.frequency (n : ℤ) (miuraL2ActionMeanMap a) :=
  (miura_mass_frequency_eq_NLS_momentum D a ha n (by omega)).symm

/-- The same endpoint comparison in the uniform native normal-form
framework, with the raw physical action unit and literal signed mean. -/
theorem theorem3_m1_corrected_native (n : ℕ) (hn : 1 ≤ n)
    (a : MiuraRealSobolevSource 0) (D : MiuraNativeHamiltonianActionData 0) :
    sourceMomentumFrequency (n : ℤ) (miuraSobolevActionSource 0 a.val) =
      D.frequency (n : ℤ) (miuraNativeActionMeanMap 0 a.val) :=
  (D.frequency_mass_eq a n (by omega)).symm

/-- All native positive action frequencies are intrinsic at every order,
including the H⁰ mass endpoint and every collapsed selected action. -/
theorem native_Hill_frequency_unique_allOrders (m : ℕ) (_hm : 1 ≤ m)
    (D E : MiuraNativeHamiltonianActionData (m-1)) (a : MiuraRealSobolevSource (m-1))
    (n : ℕ) (hn : 1 ≤ n) :
    D.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) =
      E.frequency (n : ℤ) (miuraNativeActionMeanMap (m-1) a.val) :=
  D.frequency_unique_allOrders E a n (by omega)

/-- The article's printed parity factor is false already at m=1,
on the actual zero profile and first positive index. -/
theorem theorem3_printed_parity_counterexample :
    (-1 : ℂ)^1*sourceMomentumFrequency 1 (scalarL2Diagonal 0) ≠
      miuraL2MassActionData.frequency 1 (miuraL2ActionMeanMap 0) :=
  miura_mass_frequency_printed_parity_zero_counterexample

end NLS.Articles.MKdVNLSHierarchies
