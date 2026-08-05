import CryptoFirstOrder.Type

namespace CryptoFirstOrder

universe uBase uOp uSourceOp uTargetOp uLeftOp uRightOp

/--
A first-order signature whose operations declare both an argument type and a
result type. Operation values contain no runtime arguments; arguments are
supplied by first-order expressions at call sites.
-/
structure Signature (Base : Type uBase) where
  Op : (Args Result : Ty Base) → Type uOp

namespace Signature

/-- A type-preserving injection of one primitive signature into another. -/
class Embedding
    {Base : Type uBase}
    (source : Signature.{uBase, uSourceOp} Base)
    (target : Signature.{uBase, uTargetOp} Base) where
  inject : {Args Result : Ty Base} →
    source.Op Args Result → target.Op Args Result

/-- Inject one primitive operation into a larger signature. -/
def inject
    {Base : Type uBase}
    {source : Signature.{uBase, uSourceOp} Base}
    {target : Signature.{uBase, uTargetOp} Base}
    [Embedding source target]
    {Args Result : Ty Base} :
    source.Op Args Result → target.Op Args Result :=
  Embedding.inject

/-- The disjoint union of two first-order primitive signatures. -/
def sum
    {Base : Type uBase}
    (left : Signature.{uBase, uLeftOp} Base)
    (right : Signature.{uBase, uRightOp} Base) :
    Signature.{uBase, max uLeftOp uRightOp} Base where
  Op Args Result := Sum (left.Op Args Result) (right.Op Args Result)

instance embeddingRefl
    {Base : Type uBase} (S : Signature.{uBase, uOp} Base) :
    Embedding S S where
  inject operation := operation

instance (priority := 900) embeddingSumLeft
    {Base : Type uBase}
    (left : Signature.{uBase, uLeftOp} Base)
    (right : Signature.{uBase, uRightOp} Base) :
    Embedding left (sum left right) where
  inject operation := .inl operation

instance (priority := 800) embeddingSumRight
    {Base : Type uBase}
    (source : Signature.{uBase, uSourceOp} Base)
    (left : Signature.{uBase, uLeftOp} Base)
    (right : Signature.{uBase, uRightOp} Base)
    [Embedding source right] :
    Embedding source (sum left right) where
  inject operation := .inr (Embedding.inject operation)

end Signature

end CryptoFirstOrder
