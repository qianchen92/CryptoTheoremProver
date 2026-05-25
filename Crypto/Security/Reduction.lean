namespace Crypto.Security

universe uSourceAdv uTargetAdv

/-- A reduction maps adversaries for one problem to adversaries for another problem. -/
structure Reduction (SourceAdv : Type uSourceAdv) (TargetAdv : Type uTargetAdv) where
  mapAdv : SourceAdv → TargetAdv

end Crypto.Security
