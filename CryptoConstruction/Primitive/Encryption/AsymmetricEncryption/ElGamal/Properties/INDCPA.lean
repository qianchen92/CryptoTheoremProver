import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Efficiency
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Reduction
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Cost
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.ReductionGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.Game
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.RealGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Definition.RandomGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.Reduction
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RealGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.RandomGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.OperationalMachine
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.Efficiency
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.Efficiency
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.OperationalClosure
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.ReductionGame
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.ReductionClosure
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.ReductionClosure
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.Reduction
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.GameHop
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Lemma.GameHop
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Proof.GameSequence
import CryptoConstruction.Primitive.Encryption.AsymmetricEncryption.ElGamal.Properties.INDCPA.Main.Security

/-!
# ElGamal IND-CPA security

This compatibility module aggregates the layered formalization:

* `Definition` contains efficiency data, reduction machinery, and endpoint games.
* `G₀` and `G₁` are definitionally the real and random IND-CPA games.
* `Proof` puts the complete DDH reduction in the middle `G₀ → G₁` hop.
* `Lemma` exposes the corresponding public lemmas by calling `_proof` declarations.
* Operational closure and `Main` consume only the public lemmas.
-/
