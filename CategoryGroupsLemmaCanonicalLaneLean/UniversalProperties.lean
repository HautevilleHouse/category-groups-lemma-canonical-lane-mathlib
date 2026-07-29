import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure UniversalProperty {C D : Type u} [Category C] [Category D] (F : C ⥤ D) where
  terminalObject : D
  initialObject : D
  productExists : Prop
  coproductExists : Prop
  equalizerExists : Prop
  coequalizerExists : Prop
  pullbackExists : Prop
  pushoutExists : Prop
  productExistsClosed : productExists
  coproductExistsClosed : coproductExists
  equalizerExistsClosed : equalizerExists
  coequalizerExistsClosed : coequalizerExists
  pullbackExistsClosed : pullbackExists
  pushoutExistsClosed : pushoutExists

def UniversalPropertyStatement (C : Type u) [Category C] : Prop :=
  HasTerminal C ∧ HasInitial C ∧ HasProducts C ∧ HasCoproducts C ∧
  HasEqualizers C ∧ HasCoequalizers C ∧ HasPullbacks C ∧ HasPushouts C

theorem universal_property_holds (C : Type u) [Category C] [HasTerminal C] [HasInitial C] [HasProducts C]
    [HasCoproducts C] [HasEqualizers C] [HasCoequalizers C] [HasPullbacks C] [HasPushouts C] :
    UniversalPropertyStatement C := by
  exact ⟨by infer_instance, by infer_instance, by infer_instance, by infer_instance,
         by infer_instance, by infer_instance, by infer_instance, by infer_instance⟩

structure UniversalPropertyEvidence {C : Type u} [Category C] (U : UniversalProperty (𝟭 C)) where
  terminalClosed : U.terminalObject = Terminal C
  initialClosed : U.initialObject = Initial C
  productClosed : U.productExists
  coproductClosed : U.coproductExists
  equalizerClosed : U.equalizerExists
  coequalizerClosed : U.coequalizerExists
  pullbackClosed : U.pullbackExists
  pushoutClosed : U.pushoutExists

def UniversalPropertyClosed {C : Type u} [Category C] (U : UniversalProperty (𝟭 C)) : Prop :=
  U.productExists ∧ U.coproductExists ∧ U.equalizerExists ∧ U.coequalizerExists ∧
  U.pullbackExists ∧ U.pushoutExists

theorem universal_property_closed_from_evidence {C : Type u} [Category C]
    (U : UniversalProperty (𝟭 C)) (ev : UniversalPropertyEvidence U) : UniversalPropertyClosed U := by
  exact And.intro ev.productClosed (And.intro ev.coproductClosed
    (And.intro ev.equalizerClosed (And.intro ev.coequalizerClosed
      (And.intro ev.pullbackClosed ev.pushoutClosed))))

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse