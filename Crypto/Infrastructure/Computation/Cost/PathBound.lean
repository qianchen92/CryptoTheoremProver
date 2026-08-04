import Crypto.Infrastructure.Computation.Cost.Randomized

namespace Crypto.Infrastructure.Computation.Cost

universe uCost uValue uMapped

namespace RandCosted

noncomputable section

variable
    {M : CostModel.{uCost}}
    {α : Type uValue} {β : Type uMapped}

/-- Every path in `dist` has cost at most `budget` in the model's exact order. -/
def CostBound (dist : RandCosted M α) (budget : M.Cost) : Prop :=
  ∀ result, result ∈ dist.support →
    M.instPartialOrder.le result.cost budget

namespace CostBound

/-- A zero-cost pure computation is bounded by the sequential identity. -/
theorem pure (value : α) :
    CostBound (RandCosted.pure M value) M.instAddMonoid.zero := by
  letI := M.instPartialOrder
  intro result hresult
  simp only [RandCosted.pure, RandCosted.liftCosted] at hresult
  rw [PMF.mem_support_pure_iff] at hresult
  subst result
  exact le_refl _

/-- Mapping values preserves an exact path bound. -/
theorem map
    {dist : RandCosted M α} {budget : M.Cost}
    (bound : CostBound dist budget) (f : α → β) :
    CostBound (RandCosted.map f dist) budget := by
  intro result hresult
  simp only [RandCosted.map] at hresult
  rw [PMF.mem_support_map_iff] at hresult
  rcases hresult with ⟨source, hsource, hresult⟩
  subst result
  exact bound source hsource

/-- Sequential composition adds the independently certified path budgets. -/
theorem bind
    {first : RandCosted M α} {next : α → RandCosted M β}
    {firstBudget nextBudget : M.Cost}
    (firstBound : CostBound first firstBudget)
    (nextBound : ∀ value, CostBound (next value) nextBudget) :
    CostBound (RandCosted.bind first next)
      (M.instAddMonoid.add firstBudget nextBudget) := by
  letI := M.instAddMonoid
  letI := M.instPartialOrder
  letI := M.instAddLeftMono
  letI := M.instAddRightMono
  intro result hresult
  simp only [RandCosted.bind] at hresult
  rw [PMF.mem_support_bind_iff] at hresult
  rcases hresult with ⟨firstResult, hfirstResult, hnextResult⟩
  rw [PMF.mem_support_map_iff] at hnextResult
  rcases hnextResult with ⟨nextResult, hnextResult, hresult⟩
  subst result
  exact add_le_add
    (firstBound firstResult hfirstResult)
    (nextBound firstResult.val nextResult hnextResult)

/-- A path bound remains sound after replacing its budget by a larger one. -/
theorem weaken
    {dist : RandCosted M α} {budget largerBudget : M.Cost}
    (bound : CostBound dist budget)
    (budget_le : M.instPartialOrder.le budget largerBudget) :
    CostBound dist largerBudget := by
  letI := M.instPartialOrder
  intro result hresult
  exact le_trans (bound result hresult) budget_le

end CostBound

end

end RandCosted

end Crypto.Infrastructure.Computation.Cost
