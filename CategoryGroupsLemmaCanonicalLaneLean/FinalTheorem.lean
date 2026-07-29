import canonicalLaneMathlib.AdmissibleClass
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.CategoryGroupsLemma
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.BridgeLemmas
import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.GateLemmas

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

def ConstrainedCategoryGroupsClosure (A : AdmissibleClass) : Prop :=
  bridgeClosed A ∧ gateClosed A

theorem constrained_category_groups_endgame (A : AdmissibleClass) :
    ConstrainedCategoryGroupsClosure A := by
  exact And.intro (bridge_from_admissible_class A) (gate_from_admissible_class A)

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse