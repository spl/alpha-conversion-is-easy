import algebra.order
import algebra.relation
import algebra.relation.is_irreflexive
import data.sum.trichotomy
import data.nat.order

open relation
open nat
open sum

theorem nat.gt_irrefl [instance] : @is_irreflexive ℕ gt :=
  is_irreflexive.mk nat.lt_irrefl

theorem nat.gt_trans [instance] : @is_transitive ℕ gt :=
  is_transitive.mk (λa b c, gt.trans)

theorem nat.gt_trich [instance] : @is_trichotomic ℕ gt :=
  is_trichotomic.mk
    (λa b, nat.lt_by_cases
      (λH, sum.inr (sum.inr H))
      (λH, sum.inr (sum.inl H))
      (λH, sum.inl H))
