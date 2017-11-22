/-

This files contains the `vset` instance for finset and nat.

-/

import vset
import data.finset.extra
import data.finset.fresh

namespace finset ---------------------------------------------------------------

instance vset_nat : acie.vset finset ℕ :=
  { mem                        := finset.mem
  , fresh                      := has_fresh.fresh
  , insert                     := has_insert.insert
  , subset                     := has_subset.subset
  , prop_insert_self           := λ a s, finset.mem_insert_self
  , prop_insert                := λ a b s, finset.mem_insert_of_mem
  , prop_insert_idem           := λ a s, finset.insert_idem
  , prop_insert_comm           := λ a b s, finset.insert.comm
  , prop_rm_insert_if_ne       := λ a b s, finset.mem_of_mem_insert_of_ne
  , prop_mem_of_subset         := λ a s₁ s₂, finset.mem_of_subset_of_mem
  , prop_ne_if_mem_and_not_mem := λ a b s, finset.ne_of_mem_of_not_mem
  , prop_subset_refl           := finset.subset.refl
  , prop_subset_trans          := λ s₁ s₂ s₃, finset.subset.trans
  , prop_insert_of_subset      := λ a s₁ s₂, finset.insert_subset_insert
  , prop_subset_insert_self    := λ a s, finset.subset_insert
  }

end /- namespace -/ finset -----------------------------------------------------
