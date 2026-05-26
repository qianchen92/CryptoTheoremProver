namespace Crypto.Infrastructure.GameBased

universe uSourceAdv uTargetAdv

/-- A reduction maps adversaries for one problem to adversaries for another problem. -/
structure Reduction (SourceAdv : Type uSourceAdv) (TargetAdv : Type uTargetAdv) where
  mapAdv : SourceAdv → TargetAdv

end Crypto.Infrastructure.GameBased
