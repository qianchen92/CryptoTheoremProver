import Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad.Construction
import Crypto.Primitive.Encryption.SymmetricEncryption.Properties.OneTime

namespace Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad

universe uGroup

open Crypto.Primitive.Encryption.SymmetricEncryption
open Crypto.Infrastructure.Computation.Algebra.Group
open Crypto.Infrastructure.Computation.Distribution

/-- Adding a fixed group element to a uniform one-time-pad key hides the message. -/
theorem challengeDistribution_eq
    (G : Type uGroup) [AddGroup G] [Fintype G] [Nonempty G] (m₀ m₁ : G) :
    PMF.bind (uniformPMF G) (fun key => PMF.pure ((some (key + m₀) : Option G), true)) =
    PMF.bind (uniformPMF G) (fun key => PMF.pure ((some (key + m₁) : Option G), true)) := by
  classical
  ext y
  rcases y with ⟨oc, used⟩
  cases used
  · cases oc <;> simp [uniformPMF, PMF.bind_apply]
  · cases oc with
    | none => simp [uniformPMF, PMF.bind_apply]
    | some c =>
        have hcard₀ : (Finset.univ.filter (fun a : G => a + m₀ = c)).card = 1 := by
          rw [Finset.card_eq_one]
          refine ⟨c - m₀, ?_⟩
          ext a
          simp [eq_sub_iff_add_eq]
        have hcard₁ : (Finset.univ.filter (fun a : G => a + m₁ = c)).card = 1 := by
          rw [Finset.card_eq_one]
          refine ⟨c - m₁, ?_⟩
          ext a
          simp [eq_sub_iff_add_eq]
        calc
          (PMF.bind (uniformPMF G)
                (fun key => PMF.pure ((some (key + m₀) : Option G), true))) (some c, true)
              = (∑ a : G, if c = a + m₀ then (↑(Fintype.card G) : ENNReal)⁻¹ else 0) := by
                simp [uniformPMF, PMF.bind_apply]
          _ = (↑((Finset.univ.filter (fun a : G => a + m₀ = c)).card) : ENNReal) *
                (↑(Fintype.card G) : ENNReal)⁻¹ := by
                rw [← Finset.sum_filter]
                simp [eq_comm, Finset.sum_const, nsmul_eq_mul]
          _ = (↑((Finset.univ.filter (fun a : G => a + m₁ = c)).card) : ENNReal) *
                (↑(Fintype.card G) : ENNReal)⁻¹ := by
                rw [hcard₀, hcard₁]
          _ = (∑ a : G, if c = a + m₁ then (↑(Fintype.card G) : ENNReal)⁻¹ else 0) := by
                rw [← Finset.sum_filter]
                simp [eq_comm, Finset.sum_const, nsmul_eq_mul]
          _ = (PMF.bind (uniformPMF G)
                (fun key => PMF.pure ((some (key + m₁) : Option G), true))) (some c, true) := by
                simp [uniformPMF, PMF.bind_apply]

/-- The false and true challenge oracles of the group one-time pad are extensionally equal. -/
theorem oneTimeEncryptionOracle_false_eq_true
    (F : Family.{uGroup}) (sec : Crypto.SecPar) (pp : PublicParam.{uGroup}) :
    oneTimeEncryptionOracle (scheme F) sec pp false =
    oneTimeEncryptionOracle (scheme F) sec pp true := by
  dsimp [oneTimeEncryptionOracle, scheme]
  congr
  funext name _querySec used query
  cases name
  cases used
  · simpa using challengeDistribution_eq pp.Carrier query.1 query.2
  · rfl

/-- The two one-time security games of the group one-time pad are identical. -/
theorem oneTimeSecurityGame_false_eq_true
    (F : Family.{uGroup})
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      (fun _ => PublicParam.{uGroup})
      (fun _ => Bool)
      (oneTimeOracleSpec (fun pp => pp.Carrier) (fun pp => pp.Carrier))) :
    oneTimeSecurityGame (scheme F) A false =
      oneTimeSecurityGame (scheme F) A true := by
  funext sec
  change
    PMF.bind (F.setup sec)
      (fun pp => PMF.bind
        (A.run sec pp (oneTimeEncryptionOracle (scheme F) sec pp false))
        fun output => PMF.pure output) =
    PMF.bind (F.setup sec)
      (fun pp => PMF.bind
        (A.run sec pp (oneTimeEncryptionOracle (scheme F) sec pp true))
        fun output => PMF.pure output)
  simp only [PMF.bind_pure]
  congr
  funext pp
  exact congrArg (A.run sec pp) (oneTimeEncryptionOracle_false_eq_true F sec pp)

/-- Every oracle machine has zero one-time advantage against the group one-time pad. -/
theorem oneTimeAdvantage_eq_zero
    (F : Family.{uGroup})
    (A : Crypto.Infrastructure.Complexity.ProbabilisticOracleMachine
      (fun _ => PublicParam.{uGroup})
      (fun _ => Bool)
      (oneTimeOracleSpec (fun pp => pp.Carrier) (fun pp => pp.Carrier))) :
    OneTimeAdvantage (scheme F) A = fun _ => 0 := by
  funext sec
  simp [OneTimeAdvantage, Crypto.Infrastructure.GameBased.Advantage,
    Crypto.Infrastructure.GameBased.AcceptProb, oneTimeSecurityGame_false_eq_true F A]

/-- Perfect one-time security of the group one-time pad. -/
theorem perfectOneTimeSecure (F : Family.{uGroup}) :
    PerfectOneTimeSecure (scheme F) := by
  intro A
  exact oneTimeAdvantage_eq_zero F A

/-- PPT one-time security of the group one-time pad. -/
theorem oneTimeSecure (F : Family.{uGroup}) :
    OneTimeSecure (scheme F) := by
  exact PerfectOneTimeSecure.toOneTimeSecure (perfectOneTimeSecure F)

/-- Perfect one-time security of the one-time-pad family induced by a type-level group family. -/
theorem perfectOneTimeSecure_ofGroupFamily
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)] :
    PerfectOneTimeSecure (scheme (Family.ofGroupFamily GroupFamily)) :=
  perfectOneTimeSecure (Family.ofGroupFamily GroupFamily)

/-- PPT one-time security of the one-time-pad family induced by a type-level group family. -/
theorem oneTimeSecure_ofGroupFamily
    (GroupFamily : Crypto.SecPar → Type uGroup)
    [∀ sec, AddGroup (GroupFamily sec)] [∀ sec, Fintype (GroupFamily sec)]
    [∀ sec, Nonempty (GroupFamily sec)] :
    OneTimeSecure (scheme (Family.ofGroupFamily GroupFamily)) :=
  oneTimeSecure (Family.ofGroupFamily GroupFamily)

end Crypto.Primitive.Encryption.SymmetricEncryption.Instantiations.OneTimePad
