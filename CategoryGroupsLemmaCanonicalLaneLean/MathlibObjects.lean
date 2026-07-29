import HautevilleHouse.CategoryGroupsLemmaCanonicalLaneLean.TheoremStatement
import CategoryTheory
import CategoryTheory.Limits

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

open CategoryTheory

structure CategoryObject where
  carrier : Type
  id : carrier → carrier
  comp : carrier → carrier → carrier

structure FunctorObject where
  source : CategoryObject
  target : CategoryObject
  map : source.carrier → target.carrier
  preserves_id : ∀ x, map (source.id x) = target.id (map x)
  preserves_comp : ∀ f g, map (source.comp f g) = target.comp (map f) (map g)

structure NaturalTransformationObject where
  source : FunctorObject
  target : FunctorObject
  components : ∀ X : source.source.carrier, target.target.carrier
  naturality : ∀ X Y f, target.target.comp (components X) (target.map f) = target.target.comp (source.map f) (components Y)

def CategoryWitnessClosed (O : CategoryAdmittedObject) : Prop :=
  O.yonedaLemma ∧ O.adjointFunctorTheorem ∧ O.limitsExist

structure CategoryAdmittedObject where
  category : CategoryObject
  yonedaLemma : Prop
  adjointFunctorTheorem : Prop
  limitsExist : Prop
  conclusion : yonedaLemma ∧ adjointFunctorTheorem ∧ limitsExist

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse