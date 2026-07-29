import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.AdjointFunctor

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure LimitsColimitsPackage where
  category : Type u
  hasLimits : Prop
  hasColimits : Prop
  limitConstruction : Prop
  colimitConstruction : Prop
  universalProperties : Prop

structure LimitsColimitsEvidence (L : LimitsColimitsPackage) where
  hasLimitsClosed : L.hasLimits
  hasColimitsClosed : L.hasColimits
  limitConstructionClosed : L.limitConstruction
  colimitConstructionClosed : L.colimitConstruction
  universalPropertiesClosed : L.universalProperties

def LimitsColimitsClosed (L : LimitsColimitsPackage) : Prop :=
  L.hasLimits ∧ L.hasColimits ∧ L.limitConstruction ∧ L.colimitConstruction ∧ L.universalProperties

theorem limits_colimits_closed_from_evidence (L : LimitsColimitsPackage) (E : LimitsColimitsEvidence L) : LimitsColimitsClosed L := by
  exact And.intro E.hasLimitsClosed (And.intro E.hasColimitsClosed (And.intro E.limitConstructionClosed (And.intro E.colimitConstructionClosed E.universalPropertiesClosed)))

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse