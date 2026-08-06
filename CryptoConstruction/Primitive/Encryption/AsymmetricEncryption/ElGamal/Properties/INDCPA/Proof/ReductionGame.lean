import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.ReductionGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.OperationalClosure

/-! # Concrete-to-semantic reduction-game equivalence lemmas -/

namespace CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal

open Crypto.Infrastructure.Computation.Cost
open Crypto.Infrastructure.Computation
open Crypto.Infrastructure.Computation.Oracle
open Crypto.Primitive.Encryption.AsymmetricEncryption

universe uCost uParameter uScalar uGroup

variable
    {M : CostModel.{uCost}}
    {measure : NatMeasure M}
    {Parameter : Type uParameter}
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

/-- PMF bind respects continuation equality on the support actually sampled. -/
private theorem pmf_bind_congr_on_support
    {α β : Type*} (sample : PMF α) (left right : α → PMF β)
    (heq : ∀ value, value ∈ sample.support → left value = right value) :
    PMF.bind sample left = PMF.bind sample right := by
  apply PMF.ext
  intro output
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro value
  by_cases hvalue : value ∈ sample.support
  · rw [heq value hvalue]
  · have hzero : sample value = 0 := by
      simpa only [PMF.mem_support_iff, not_ne_iff] using hvalue
    simp only [hzero, zero_mul]

/-- On a sample whose setup tag is valid, the concrete compiled machine and
the semantic reduction induce exactly the same security game. -/
private theorem concreteSecurityGame_eq_semantic
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool)
    (sample : Crypto.SecPar → PMF
      (Crypto.Assumption.DL.DDH.ChallengeInput F))
    (htag : ∀ sec challenge, challenge ∈ (sample sec).support →
      F.parameterSec challenge.parameter = sec) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame sample
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      semanticReductionGame F sample adversary.toOracleMachine
        rightMessage := by
  funext sec
  unfold Crypto.Infrastructure.GameBased.Distinguishing.securityGame
    semanticReductionGame
  apply pmf_bind_congr_on_support
  intro challenge hchallenge
  exact concreteDDHReduction_runDist_eq_semantic F efficiency
    adversary.toOracleMachine rightMessage sec challenge
    (htag sec challenge hchallenge)

theorem concreteRealReductionGame_eq
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.realSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      realReductionGame F adversary.toOracleMachine rightMessage := by
  exact concreteSecurityGame_eq_semantic F efficiency adversary rightMessage
    (Crypto.Assumption.DL.DDH.realSample F)
    (Crypto.Assumption.DL.DDH.parameterSec_eq_of_mem_support_realSample F)

theorem concreteRandomReductionGame_eq
    (F : Family M Parameter Scalar Carrier)
    (efficiency : ReductionEfficiencyCertificate measure F)
    (adversary : Crypto.Infrastructure.Complexity.PPTOracleMachine
      M measure
      (PublicInput Parameter (PublicKey (Carrier := Carrier)))
      (fun _sec _input => Bool)
      (indCPAOracleSpec
        (Message (Carrier := Carrier)) (Ciphertext (Carrier := Carrier))))
    (rightMessage : Bool) :
    Crypto.Infrastructure.GameBased.Distinguishing.securityGame
        (Crypto.Assumption.DL.DDH.randomSample F)
        (concreteDDHReductionPPT F efficiency adversary
          rightMessage).toProbabilisticMachine =
      randomReductionGame F adversary.toOracleMachine rightMessage := by
  exact concreteSecurityGame_eq_semantic F efficiency adversary rightMessage
    (Crypto.Assumption.DL.DDH.randomSample F)
    (Crypto.Assumption.DL.DDH.parameterSec_eq_of_mem_support_randomSample F)

end CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal
