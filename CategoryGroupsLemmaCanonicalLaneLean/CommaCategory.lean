import canonicalLaneMathlib.AdmissibleClass

namespace HautevilleHouse
namespace CategoryGroupsLemmaCanonicalLaneLean

structure CommaObject (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C) where
  left : A
  right : B
  arrow : S.obj left ⟶ T.obj right

structure CommaMorphism (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C)
    (X Y : CommaObject A B C S T) where
  leftMorphism : X.left ⟶ Y.left
  rightMorphism : X.right ⟶ Y.right
  compatibility : T.map rightMorphism ∘ X.arrow = Y.arrow ∘ S.map leftMorphism
  compatibilityClosed : compatibility

def CommaCategory (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C) : Category (CommaObject A B C S T) where
  Hom X Y := CommaMorphism A B C S T X Y
  id X :=
    { leftMorphism := 𝟙 X.left
      rightMorphism := 𝟙 X.right
      compatibility := by
        simp
      compatibilityClosed := by trivial
    }
  comp f g :=
    { leftMorphism := f.leftMorphism ≫ g.leftMorphism
      rightMorphism := f.rightMorphism ≫ g.rightMorphism
      compatibility := by
        calc T.map (f.rightMorphism ≫ g.rightMorphism) ∘ X.arrow
            = T.map g.rightMorphism ∘ T.map f.rightMorphism ∘ X.arrow := by simp
        _ = T.map g.rightMorphism ∘ (Y.arrow ∘ S.map f.leftMorphism) := by rw [f.compatibility]
        _ = (T.map g.rightMorphism ∘ Y.arrow) ∘ S.map f.leftMorphism := by simp
        _ = (Z.arrow ∘ S.map g.leftMorphism) ∘ S.map f.leftMorphism := by rw [g.compatibility]
        _ = Z.arrow ∘ (S.map g.leftMorphism ∘ S.map f.leftMorphism) := by simp
        _ = Z.arrow ∘ S.map (f.leftMorphism ≫ g.leftMorphism) := by simp
      compatibilityClosed := by trivial
    }

theorem comma_category_is_category (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C) :
    Category (CommaObject A B C S T) := by
  apply CommaCategory A B C S T

structure CommaCategoryEvidence (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C) where
  categoryInstance : Category (CommaObject A B C S T)
  categoryInstanceClosed : categoryInstance = CommaCategory A B C S T

def CommaCategoryClosed (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C) : Prop :=
  Category (CommaObject A B C S T)

theorem comma_category_closed_from_evidence (A B C : Type u) [Category A] [Category B] [Category C] (S : A ⥤ C) (T : B ⥤ C)
    (ev : CommaCategoryEvidence A B C S T) : CommaCategoryClosed A B C S T := by
  exact ev.categoryInstance

end CategoryGroupsLemmaCanonicalLaneLean
end HautevilleHouse