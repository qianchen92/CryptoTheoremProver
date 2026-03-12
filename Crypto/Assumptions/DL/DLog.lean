import Mathlib.Algebra.Group.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Crypto.SecModel.Adversary.PPT

namespace DLog

open Crypto.SecModel
open Crypto.SecModel.Adversary

/-!
离散对数问题（DLog）：给定有限群中的元素 `g` 与 `h`，寻找 `x` 使得
`g ^ x = h`。这里的定义只描述问题本身，不涉及概率多项式时间对手或安全性。
-/

structure DLogProblem (G : Type) [Group G] where
  g : G
  h : G



def IsSolution {G : Type} [Group G] (prob : DLogProblem G) (x : Nat) : Prop :=
  prob.g ^ x = prob.h

/--
离散对数假设：不存在任何 PPT 对手能够以不可忽略的概率解决 DLog 问题。
这里我们先定义对手的类型：输入是 DLogProblem，输出是 Nat。
-/
abbrev DLogAdversary (G : Type) [Group G] := PPTAdversary (DLogProblem G) Nat

/--
群生成器：输入安全参数，输出一个群 G，其大小大于 2^secpar，以及一个生成元 g。
这里我们用 PMF 抽象表示随机生成过程。
-/
structure GroupGen (G : Type) [Group G] where
  gen : SecPar → PMF (G × Nat) -- 返回生成元和群的阶
  size_bound : ∀ (sp : SecPar) (g : G) (q : Nat),
    (gen sp) (g, q) > 0 → q > 2^sp

/--
DLog 实验：
1. 运行群生成器得到 (g, q)
2. 随机选择 x ∈ [0, q-1]
3. 计算 h = g^x
4. 将 (g, h) 交给对手 A
5. 对手输出 x'
6. 如果 g^x' = h，则实验成功（返回 true），否则失败（返回 false）
-/
noncomputable def DLogExperiment {G : Type} [Group G]
    (gen : GroupGen G) (A : DLogAdversary G) (sp : SecPar) : PMF Bool := do
  let (g, q) ← gen.gen sp
  -- 假设有一个从 [0, q-1] 均匀采样的 PMF
  -- let x ← uniform_of_fin q
  -- let h := g ^ x
  -- let x' ← A.run sp ⟨g, h⟩
  -- return (g ^ x' = h)
  -- 为了编译通过，这里先用一个占位符，实际需要引入均匀分布
  pure false

/--
DLog 假设：对于任意 PPT 对手 A，其在 DLog 实验中成功的概率是不可忽略的。
-/
def DLogAssumption {G : Type} [Group G] (gen : GroupGen G) : Prop :=
  ∀ A : DLogAdversary G, IsNegligible (fun sp => ((DLogExperiment gen A sp) true).toReal)

end DLog
