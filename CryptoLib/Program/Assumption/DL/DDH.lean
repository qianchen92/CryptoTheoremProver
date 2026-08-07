import CryptoLib.Core.Assumption.DL.DDH
import CryptoLib.Program.Algebra.ScalarAction

namespace CryptoLib.Program.Assumption.DL.DDH

open CryptoLib.Core.Infrastructure.Computation.Cost
open CryptoLib.Program
open scoped DDHParameter

universe uCost uScalar uGroup

variable
    {Scalar : Type uScalar}
    {Carrier : Type uGroup}

export CryptoLib.Program.Algebra.ScalarAction
  (Base scalarTy carrierTy Operation signature)

namespace Operation

export CryptoLib.Program.Algebra.ScalarAction.Operation
  (sampleScalar smul add sub)

end Operation

abbrev interpret
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  CryptoLib.Program.Algebra.ScalarAction.interpret pp.Scalar pp.Carrier

abbrev ScalarValue
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  CryptoLib.Program.Algebra.ScalarAction.ScalarValue pp.Scalar pp.Carrier

abbrev CarrierValue
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :=
  CryptoLib.Program.Algebra.ScalarAction.CarrierValue pp.Scalar pp.Carrier

abbrev liftScalar
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    pp.Scalar → ScalarValue pp :=
  CryptoLib.Program.Algebra.ScalarAction.liftScalar pp.Scalar pp.Carrier

abbrev liftCarrier
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    pp.Carrier → CarrierValue pp :=
  CryptoLib.Program.Algebra.ScalarAction.liftCarrier pp.Scalar pp.Carrier

/-- The distinguished DDH generator at the first-order carrier boundary. -/
abbrev generatorValue
    {M : CostModel.{uCost}}
    {pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier} :
    CarrierValue pp :=
  liftCarrier pp pp.generator

abbrev carrierScalarPairDown
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    CarrierValue pp × ScalarValue pp → pp.Carrier × pp.Scalar :=
  CryptoLib.Program.Algebra.ScalarAction.carrierScalarPairDown
    pp.Scalar pp.Carrier

abbrev carrierPairDown
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    CarrierValue pp × CarrierValue pp → pp.Carrier × pp.Carrier :=
  CryptoLib.Program.Algebra.ScalarAction.carrierPairDown pp.Scalar pp.Carrier

/-- Adapt the authoritative exact DDH handler without changing its computations. -/
noncomputable def handler
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    CryptoLib.Program.Algebra.ScalarAction.Handler
      M pp.Scalar pp.Carrier where
  sampleScalar := pp.algebra.exec .sampleScalar
  smul := fun scalar value => pp.algebra.exec (.smul scalar value)
  add := fun left right => pp.algebra.exec (.add left right)
  sub := fun left right => pp.algebra.exec (.sub left right)

/-- The reusable first-order view of a DDH parameter's exact algebra. -/
noncomputable def algebra
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier) :
    CostedAlgebra M (interpret pp) signature :=
  CryptoLib.Program.Algebra.ScalarAction.algebra (handler pp)

@[simp] theorem valueDist_exec_sampleScalar
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (args : Ty.denote (interpret pp) .unit) :
    RandCosted.valueDist ((algebra pp).exec Operation.sampleScalar args) =
      PMF.map ULift.up
        (CryptoLib.Core.Infrastructure.Probability.uniformPMF pp.Scalar) := by
  simpa [algebra, handler, CryptoLib.Program.Algebra.ScalarAction.algebra] using
    (CryptoLib.Core.Assumption.DL.DDH.algebraLaws pp).exec_spec
      CryptoLib.Core.Assumption.DL.DDH.Op.sampleScalar

@[simp] theorem valueDist_exec_smul
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (args : Ty.denote (interpret pp) (scalarTy ×ₜ carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.smul args) =
      PMF.pure (ULift.up (args.1.down • args.2.down)) := by
  simpa [algebra, handler, CryptoLib.Program.Algebra.ScalarAction.algebra] using
    (CryptoLib.Core.Assumption.DL.DDH.algebraLaws pp).exec_spec
      (CryptoLib.Core.Assumption.DL.DDH.Op.smul args.1.down args.2.down)

@[simp] theorem valueDist_exec_add
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (args : Ty.denote (interpret pp) (carrierTy ×ₜ carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.add args) =
      PMF.pure (ULift.up (args.1.down + args.2.down)) := by
  simpa [algebra, handler, CryptoLib.Program.Algebra.ScalarAction.algebra] using
    (CryptoLib.Core.Assumption.DL.DDH.algebraLaws pp).exec_spec
      (CryptoLib.Core.Assumption.DL.DDH.Op.add args.1.down args.2.down)

@[simp] theorem valueDist_exec_sub
    {M : CostModel.{uCost}}
    (pp : CryptoLib.Core.Assumption.DL.DDH.PublicParam.{uCost, uScalar, uGroup} M Scalar Carrier)
    (args : Ty.denote (interpret pp) (carrierTy ×ₜ carrierTy)) :
    RandCosted.valueDist ((algebra pp).exec Operation.sub args) =
      PMF.pure (ULift.up (args.1.down - args.2.down)) := by
  simpa [algebra, handler, CryptoLib.Program.Algebra.ScalarAction.algebra] using
    (CryptoLib.Core.Assumption.DL.DDH.algebraLaws pp).exec_spec
      (CryptoLib.Core.Assumption.DL.DDH.Op.sub args.1.down args.2.down)

end CryptoLib.Program.Assumption.DL.DDH

/-!
`DDHGroup` owns the optional `⦋x⦌` representation notation. It is separate
from both the generic first-order scope and the broader `DDHParameter` instance
scope so that fixed-generator notation is enabled only where it is meaningful.
-/
namespace DDHGroup

open scoped CryptoLib.Program

set_option quotPrecheck false in
scoped macro:max "⦋" scalar:term "⦌" : term =>
  `($scalar •
    value(CryptoLib.Program.Assumption.DL.DDH.generatorValue))

end DDHGroup
